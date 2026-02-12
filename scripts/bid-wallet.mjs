#!/usr/bin/env node
/* eslint-disable no-console */

import fs from "node:fs/promises";
import path from "node:path";

import { CookieJar } from "tough-cookie";
import fetchCookie from "fetch-cookie";
import {
  createPublicClient,
  createWalletClient,
  defineChain,
  formatUnits,
  http,
  maxUint256,
  parseUnits,
} from "viem";
import { privateKeyToAccount } from "viem/accounts";

const DEFAULTS = {
  msuBaseUrl: "https://msu.io",
  rpcUrl: "https://henesys-rpc.msu.io",
  chainId: 68414,
  priceMeso: "1",
  durationDays: 14,
  throttleMs: 250,
  maxOffers: Infinity,
  dryRun: true,
  approve: false,
  dumpInventory: true,
  types: ["items", "characters"],
};

function printUsage() {
  console.log(
    [
      "Usage:",
      "  npm run bid:wallet -- --seller 0xSELLER --private-key 0xPK [options]",
      "",
      "Required:",
      "  --seller 0x...            Wallet du vendeur (ton ami)",
      "  --private-key 0x...       Private key du bidder (toi). Alternative: env BIDDER_PRIVATE_KEY",
      "",
      "Options:",
      "  --dry-run true|false      Default: true (ne POST pas les offers)",
      "  --approve true|false      Default: false (fait approve NextMeso -> MarketplaceV2 onchain)",
      "  --price-meso 1            Default: 1",
      "  --duration-days 14        Default: 14",
      "  --types items,characters  Default: items,characters",
      "  --max-offers 50           Default: Infinity",
      "  --throttle-ms 250         Default: 250",
      "  --msu-base-url https://msu.io",
      "  --rpc-url https://henesys-rpc.msu.io",
      "  --dump-inventory true|false  Default: true (écrit tmp/inventory-*.json)",
      "",
      "Env alternatives:",
      "  SELLER_ADDRESS, BIDDER_PRIVATE_KEY, MSU_BASE_URL, RPC_URL",
      "",
      "Safety:",
      "  DRY_RUN=true par défaut. Vérifie d'abord inventory + coûts, puis relance avec --dry-run false.",
    ].join("\n"),
  );
}

function parseBool(v, fallback) {
  if (v === undefined || v === null) return fallback;
  if (typeof v === "boolean") return v;
  const s = String(v).trim().toLowerCase();
  if (["1", "true", "yes", "y", "on"].includes(s)) return true;
  if (["0", "false", "no", "n", "off"].includes(s)) return false;
  return fallback;
}

function parseCsv(v) {
  if (!v) return [];
  return String(v)
    .split(",")
    .map((s) => s.trim())
    .filter(Boolean);
}

function parseArgs(argv) {
  const out = { _: [] };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith("--")) {
      out._.push(a);
      continue;
    }
    const eq = a.indexOf("=");
    let key = a;
    let value = undefined;
    if (eq !== -1) {
      key = a.slice(0, eq);
      value = a.slice(eq + 1);
    } else if (i + 1 < argv.length && !argv[i + 1].startsWith("--")) {
      value = argv[++i];
    } else {
      value = "true";
    }
    out[key] = value;
  }
  return out;
}

function requireAddress(name, v) {
  if (!v) throw new Error(`Missing ${name}.`);
  const s = String(v);
  if (!s.startsWith("0x") || s.length !== 42) {
    throw new Error(`Invalid ${name}: ${s}`);
  }
  return s;
}

async function readJsonIfExists(p) {
  try {
    const raw = await fs.readFile(p, "utf8");
    return JSON.parse(raw);
  } catch (e) {
    if (e && (e.code === "ENOENT" || e.code === "ENOTDIR")) return undefined;
    throw e;
  }
}

function toLowerAddress(addr) {
  return String(addr).toLowerCase();
}

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

function jsonStringifySafe(v) {
  return JSON.stringify(
    v,
    (_k, val) => (typeof val === "bigint" ? val.toString() : val),
    2,
  );
}

function pickAny(obj, keys) {
  for (const k of keys) {
    if (obj && Object.prototype.hasOwnProperty.call(obj, k) && obj[k] != null) return obj[k];
  }
  return undefined;
}

function extractOwnedTokenIdsByNftContract(inventoryJson, { equipAddress, characterAddress }) {
  const equip = toLowerAddress(equipAddress);
  const character = toLowerAddress(characterAddress);

  const items = new Set();
  const characters = new Set();

  // Walk the JSON and look for entries that contain tokenId + nftAddress (or similar).
  const seen = new Set();

  function visit(v) {
    if (v == null) return;
    if (typeof v !== "object") return;
    if (seen.has(v)) return;
    seen.add(v);

    if (Array.isArray(v)) {
      for (const el of v) visit(el);
      return;
    }

    const tokenIdRaw = pickAny(v, ["tokenId", "nftTokenId", "id"]);
    const nftAddrRaw = pickAny(v, ["nftAddress", "contractAddress", "nftContractAddress"]);
    const typeRaw = pickAny(v, ["tokenType", "type", "nftType"]);

    const tokenId =
      tokenIdRaw != null && (typeof tokenIdRaw === "string" || typeof tokenIdRaw === "number")
        ? String(tokenIdRaw)
        : undefined;
    const nftAddr = nftAddrRaw != null ? toLowerAddress(nftAddrRaw) : undefined;
    const type = typeRaw != null ? String(typeRaw).toLowerCase() : undefined;

    if (tokenId && nftAddr) {
      if (nftAddr === equip) items.add(tokenId);
      if (nftAddr === character) characters.add(tokenId);
    } else if (tokenId && type) {
      // Fallback if API returns tokenType without nftAddress.
      if (type === "items") items.add(tokenId);
      if (type === "characters") characters.add(tokenId);
    }

    for (const vv of Object.values(v)) visit(vv);
  }

  const root = inventoryJson && typeof inventoryJson === "object" && "data" in inventoryJson ? inventoryJson.data : inventoryJson;
  visit(root);

  return {
    items: Array.from(items),
    characters: Array.from(characters),
  };
}

function buildEip712({ chainId, marketplaceV2 }) {
  return {
    domain: {
      name: "Marketplace",
      version: "1.0",
      chainId,
      verifyingContract: marketplaceV2,
    },
    types: {
      EIP712Domain: [
        { name: "name", type: "string" },
        { name: "version", type: "string" },
        { name: "chainId", type: "uint256" },
        { name: "verifyingContract", type: "address" },
      ],
      Order: [
        { name: "isSeller", type: "uint256" },
        { name: "maker", type: "address" },
        { name: "listingTime", type: "uint256" },
        { name: "expirationTime", type: "uint256" },
        { name: "tokenAddress", type: "address" },
        { name: "tokenAmount", type: "uint256" },
        { name: "nftAddress", type: "address" },
        { name: "nftTokenId", type: "uint256" },
        { name: "salt", type: "uint256" },
      ],
    },
    primaryType: "Order",
  };
}

function buildOfferOrder({
  walletAddress,
  tokenId,
  amountWei,
  tokenType,
  nextMeso,
  maplestoryEquip,
  maplestoryCharacter,
  nowSec,
  expirationSec,
  salt,
}) {
  let nftAddress = "";
  if (tokenType === "items") nftAddress = maplestoryEquip;
  else if (tokenType === "characters") nftAddress = maplestoryCharacter;
  else throw new Error(`Unsupported tokenType: ${tokenType}`);

  const orderForChain = {
    isSeller: 0n,
    maker: walletAddress,
    listingTime: nowSec,
    expirationTime: expirationSec,
    tokenAddress: nextMeso,
    tokenAmount: amountWei,
    nftAddress,
    nftTokenId: BigInt(tokenId),
    salt,
  };

  // Mirror frontend: isSeller boolean + stringified numeric fields.
  const orderForApi = {
    ...orderForChain,
    isSeller: false,
    listingTime: orderForChain.listingTime.toString(),
    expirationTime: orderForChain.expirationTime.toString(),
    tokenAmount: orderForChain.tokenAmount?.toString(),
    nftTokenId: tokenId,
    salt: orderForChain.salt.toString(),
  };

  return { orderForChain, orderForApi };
}

function createMsuClient({ baseUrl }) {
  const jar = new CookieJar(undefined, { looseMode: true });
  const fetchWithCookies = fetchCookie(globalThis.fetch, jar);

  async function doFetch(pathname, { method = "GET", headers, body, query } = {}) {
    const url = new URL(pathname, baseUrl);
    if (query && typeof query === "object") {
      for (const [k, v] of Object.entries(query)) {
        if (v === undefined || v === null) continue;
        url.searchParams.set(k, String(v));
      }
    }

    const res = await fetchWithCookies(url.toString(), {
      method,
      headers: {
        "content-type": "application/json",
        "user-agent": "msu-bid-bot/0.1",
        ...(headers || {}),
      },
      body: body === undefined ? undefined : typeof body === "string" ? body : JSON.stringify(body),
    });
    return res;
  }

  async function fetchJson(pathname, opts = {}) {
    const maxRetries = 3;
    let lastErr = null;
    for (let attempt = 0; attempt <= maxRetries; attempt++) {
      const res = await doFetch(pathname, opts);
      if (res.status === 401 && attempt < maxRetries) {
        // Try refresh then retry.
        await doFetch("/api/web/token/refresh-web", { method: "POST" }).catch(() => null);
        await sleep(200 * (attempt + 1));
        continue;
      }
      if (res.status >= 500 && attempt < maxRetries) {
        await sleep(500 * 2 ** attempt);
        continue;
      }

      let json = null;
      const text = await res.text();
      try {
        json = text ? JSON.parse(text) : null;
      } catch {
        json = { _raw: text };
      }

      if (!res.ok) {
        const err = new Error(`HTTP ${res.status} ${res.statusText} for ${pathname}`);
        err.status = res.status;
        err.body = json;
        lastErr = err;
        break;
      }

      return json;
    }
    throw lastErr || new Error("Request failed");
  }

  return { jar, fetchJson };
}

async function msuLogin({ msu, address, account }) {
  await msu.fetchJson("/api/web/can-signin", { method: "POST", body: {} });
  await msu.fetchJson(`/api/web/account/${address}`, { method: "GET" });
  const msgRes = await msu.fetchJson("/api/web/message", {
    method: "POST",
    body: { address },
  });
  const message = msgRes?.message || msgRes?.data?.message || "";
  if (!message) throw new Error("MSU login: missing message to sign.");

  const signature = await account.signMessage({ message });

  const signinRes = await msu.fetchJson("/api/web/signin-wallet", {
    method: "POST",
    body: { address, signature, walletType: "metamask" },
  });
  return signinRes;
}

async function main() {
  const args = parseArgs(process.argv);
  if (args["--help"] || args["-h"]) {
    printUsage();
    process.exit(0);
  }

  const seller = requireAddress("seller address", args["--seller"] || process.env.SELLER_ADDRESS);
  const privateKey =
    args["--private-key"] ||
    process.env.BIDDER_PRIVATE_KEY ||
    process.env.BUYER_PRIVATE_KEY;
  if (!privateKey) throw new Error("Missing --private-key or env BIDDER_PRIVATE_KEY.");

  const msuBaseUrl = String(args["--msu-base-url"] || process.env.MSU_BASE_URL || DEFAULTS.msuBaseUrl);
  const rpcUrl = String(args["--rpc-url"] || process.env.RPC_URL || DEFAULTS.rpcUrl);

  const dryRun = parseBool(args["--dry-run"] ?? process.env.DRY_RUN, DEFAULTS.dryRun);
  const approve = parseBool(args["--approve"] ?? process.env.APPROVE, DEFAULTS.approve);
  const dumpInventory = parseBool(args["--dump-inventory"] ?? process.env.DUMP_INVENTORY, DEFAULTS.dumpInventory);

  const priceMeso = String(args["--price-meso"] || process.env.PRICE_MESO || DEFAULTS.priceMeso);
  const durationDays = Number(args["--duration-days"] || process.env.DURATION_DAYS || DEFAULTS.durationDays);
  const throttleMs = Number(args["--throttle-ms"] || process.env.THROTTLE_MS || DEFAULTS.throttleMs);
  const maxOffers = Number(args["--max-offers"] || process.env.MAX_OFFERS || DEFAULTS.maxOffers);
  const types = (parseCsv(args["--types"] || process.env.TYPES).length
    ? parseCsv(args["--types"] || process.env.TYPES)
    : DEFAULTS.types
  ).map((t) => t.toLowerCase());

  const addressMap = (await readJsonIfExists("data/context/contracts/address-map.json")) || {};
  const marketplaceV2 = requireAddress(
    "MarketplaceV2",
    process.env.MARKETPLACE_V2 || addressMap.MarketplaceV2 || "0x6813869c3E5deC06e6f88b42D41487dC5D7aBF57",
  );
  const nextMeso = requireAddress(
    "NextMeso",
    process.env.NEXT_MESO || addressMap.NextMeso || "0x07E49Ad54FcD23F6e7B911C2068F0148d1827c08",
  );
  const maplestoryEquip = requireAddress(
    "MaplestoryEquip",
    process.env.MAPLESTORY_EQUIP || addressMap.MaplestoryEquip || "0x43DCff2A0cedcd5e10e6f1c18b503498dDCe60d5",
  );
  const maplestoryCharacter = requireAddress(
    "MaplestoryCharacter",
    process.env.MAPLESTORY_CHARACTER || addressMap.MaplestoryCharacter || "0xcE8e48Fae05c093a4A1a1F569BDB53313D765937",
  );

  const chain = defineChain({
    id: DEFAULTS.chainId,
    name: "Henesys",
    nativeCurrency: { name: "Henesys", symbol: "HEN", decimals: 18 },
    rpcUrls: { default: { http: [rpcUrl] } },
  });

  const pk = String(privateKey).startsWith("0x") ? String(privateKey) : `0x${privateKey}`;
  const account = privateKeyToAccount(pk);
  const bidder = account.address;

  const publicClient = createPublicClient({
    chain,
    transport: http(rpcUrl),
  });
  const walletClient = createWalletClient({
    chain,
    transport: http(rpcUrl),
    account,
  });

  const nextMesoAbiPath = path.join("data/context/abis", `${toLowerAddress(nextMeso)}.json`);
  const nextMesoAbi = (await readJsonIfExists(nextMesoAbiPath)) || [
    { type: "function", name: "decimals", stateMutability: "view", inputs: [], outputs: [{ type: "uint8" }] },
    { type: "function", name: "balanceOf", stateMutability: "view", inputs: [{ name: "a", type: "address" }], outputs: [{ type: "uint256" }] },
    { type: "function", name: "allowance", stateMutability: "view", inputs: [{ name: "o", type: "address" }, { name: "s", type: "address" }], outputs: [{ type: "uint256" }] },
    { type: "function", name: "approve", stateMutability: "nonpayable", inputs: [{ name: "s", type: "address" }, { name: "a", type: "uint256" }], outputs: [{ type: "bool" }] },
  ];

  const decimals = await publicClient.readContract({
    address: nextMeso,
    abi: nextMesoAbi,
    functionName: "decimals",
  });
  const amountWei = parseUnits(priceMeso, Number(decimals));

  console.log(jsonStringifySafe({
    seller,
    bidder,
    dryRun,
    approve,
    priceMeso,
    amountWei: amountWei.toString(),
    durationDays,
    throttleMs,
    types,
    marketplaceV2,
    nextMeso,
    maplestoryEquip,
    maplestoryCharacter,
    msuBaseUrl,
    rpcUrl,
  }));

  const msu = createMsuClient({ baseUrl: msuBaseUrl });
  await msuLogin({ msu, address: bidder, account });

  const inventory = await msu.fetchJson(`/api/marketplace/inventory/${seller}/owned`, {
    method: "GET",
    query: { page: 1, size: 1000 },
  }).catch(async (e) => {
    // Some backends reject unknown query params. Retry without.
    if (e && (e.status === 400 || e.status === 404)) {
      return await msu.fetchJson(`/api/marketplace/inventory/${seller}/owned`, { method: "GET" });
    }
    throw e;
  });

  if (dumpInventory) {
    const outPath = path.join("tmp", `inventory-${seller}-${Date.now()}.json`);
    await fs.writeFile(outPath, jsonStringifySafe(inventory), "utf8");
    console.log(`Wrote ${outPath}`);
  }

  const owned = extractOwnedTokenIdsByNftContract(inventory, {
    equipAddress: maplestoryEquip,
    characterAddress: maplestoryCharacter,
  });

  const tokenIdsByType = {
    items: owned.items,
    characters: owned.characters,
  };

  for (const t of Object.keys(tokenIdsByType)) {
    tokenIdsByType[t] = tokenIdsByType[t].filter((x) => /^[0-9]+$/.test(String(x)));
  }

  const allPlanned = [];
  for (const t of types) {
    for (const tokenId of tokenIdsByType[t] || []) allPlanned.push({ tokenType: t, tokenId });
  }

  if (!allPlanned.length) {
    throw new Error(
      "No owned tokenIds found from inventory response. Blocker: je dois voir la shape de la reponse /owned pour ton wallet vendeur.",
    );
  }

  const planned = allPlanned.slice(0, Number.isFinite(maxOffers) ? maxOffers : allPlanned.length);
  const totalCost = amountWei * BigInt(planned.length);

  const [balance, allowance] = await Promise.all([
    publicClient.readContract({
      address: nextMeso,
      abi: nextMesoAbi,
      functionName: "balanceOf",
      args: [bidder],
    }),
    publicClient.readContract({
      address: nextMeso,
      abi: nextMesoAbi,
      functionName: "allowance",
      args: [bidder, marketplaceV2],
    }),
  ]);

  console.log(
    jsonStringifySafe({
      plannedOffers: planned.length,
      totalCostWei: totalCost.toString(),
      totalCost: formatUnits(totalCost, Number(decimals)),
      balanceWei: balance.toString(),
      balance: formatUnits(balance, Number(decimals)),
      allowanceWei: allowance.toString(),
      allowance: formatUnits(allowance, Number(decimals)),
    }),
  );

  if (approve) {
    if (allowance < totalCost) {
      console.log("Approving NextMeso allowance to MarketplaceV2 (maxUint256) ...");
      const hash = await walletClient.writeContract({
        address: nextMeso,
        abi: nextMesoAbi,
        functionName: "approve",
        args: [marketplaceV2, maxUint256],
      });
      const receipt = await publicClient.waitForTransactionReceipt({ hash });
      console.log(jsonStringifySafe({ approveTx: hash, status: receipt.status }));
    } else {
      console.log("Skip approve: allowance already >= total cost.");
    }
  }

  const eip712 = buildEip712({ chainId: DEFAULTS.chainId, marketplaceV2 });
  const nowSec = BigInt(Math.floor(Date.now() / 1000));
  const expirationSec = nowSec + BigInt(Math.floor(durationDays * 86400));

  const report = {
    startedAt: new Date().toISOString(),
    seller,
    bidder,
    dryRun,
    approve,
    msuBaseUrl,
    offers: [],
    failures: [],
  };

  let counter = 0;
  for (const { tokenType, tokenId } of planned) {
    counter++;
    const salt = BigInt(Date.now()) * 1000n + BigInt(counter); // unique-ish + sortable
    const { orderForChain, orderForApi } = buildOfferOrder({
      walletAddress: bidder,
      tokenId,
      amountWei,
      tokenType,
      nextMeso,
      maplestoryEquip,
      maplestoryCharacter,
      nowSec,
      expirationSec,
      salt,
    });

    const orderSign = await account.signTypedData({
      domain: eip712.domain,
      types: eip712.types,
      primaryType: eip712.primaryType,
      message: orderForChain,
    });

    const payload = { order: orderForApi, orderSign };

    if (dryRun) {
      report.offers.push({ tokenType, tokenId, dryRun: true });
      if (throttleMs) await sleep(throttleMs);
      continue;
    }

    try {
      const res = await msu.fetchJson(`/api/marketplace/${tokenType}/${tokenId}/offer`, {
        method: "POST",
        body: payload,
      });
      report.offers.push({ tokenType, tokenId, ok: true, res });
    } catch (e) {
      report.failures.push({
        tokenType,
        tokenId,
        error: { message: e?.message, status: e?.status, body: e?.body },
      });
    }

    if (throttleMs) await sleep(throttleMs);
  }

  report.finishedAt = new Date().toISOString();
  const reportPath = path.join("tmp", `bid-wallet-report-${Date.now()}.json`);
  await fs.writeFile(reportPath, jsonStringifySafe(report), "utf8");
  console.log(`Wrote ${reportPath}`);

  console.log(
    jsonStringifySafe({
      ok: report.offers.filter((o) => o.ok || o.dryRun).length,
      failures: report.failures.length,
    }),
  );
}

main().catch((e) => {
  console.error(e?.stack || e);
  process.exit(1);
});

