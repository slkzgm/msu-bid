import { promises as fs } from "node:fs";
import path from "node:path";
import crypto from "node:crypto";

const API_BASE_URL = "https://api-gateway.xangle.io";
const RPC_URL = "https://henesys-rpc.msu.io";
const X_CHAIN = "NEXON";
const USER_AGENT =
  "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) HeadlessChrome/144.0.0.0 Safari/537.36";

const CONTEXT_ROOT = path.join(process.cwd(), "data", "context");
const CONTRACT_MODULE_PATH = path.join(
  process.cwd(),
  "data",
  "extracted",
  "modules",
  "97134__8009-cbb84f0b3e10ffb3.js",
);

const IMPORTANT_CONTRACT_KEYS = [
  "Marketplace",
  "MarketplaceV2",
  "OrderBook",
  "NextMeso",
  "Commission",
  "MaplestoryEquip",
  "MaplestoryCharacter",
  "MaplestoryConsume",
];

const secretCache = {
  key: null,
  expiresAt: 0,
};

function nowMs() {
  return Date.now();
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function toLowerAddress(address) {
  return String(address || "").toLowerCase();
}

function dedupeAddresses(addresses) {
  return [...new Set(addresses.map(toLowerAddress).filter(Boolean))];
}

async function ensureDir(dirPath) {
  await fs.mkdir(dirPath, { recursive: true });
}

async function writeJson(filePath, data) {
  await ensureDir(path.dirname(filePath));
  await fs.writeFile(filePath, JSON.stringify(data, null, 2));
}

function generateRandomHash() {
  return `0x${crypto.randomBytes(32).toString("hex")}`;
}

function generateSecretKey(secretResponse, randomHash) {
  const secretBase64 = secretResponse?.SECRET;
  const dataList = secretResponse?.DATALIST;
  if (!secretBase64 || !Array.isArray(dataList) || dataList.length < 36) {
    throw new Error("Unexpected /api/secret/key response shape");
  }

  const decoded = Buffer.from(secretBase64, "base64").toString("utf8");
  const parsed = Number.parseInt(decoded, 10);
  if (Number.isNaN(parsed)) {
    throw new Error("Invalid SECRET value returned by /api/secret/key");
  }

  let index = null;
  for (let r = 0; r < 36; r += 1) {
    // This is the exact obfuscated check used in the explorer bundle.
    if ((((r * 5 + 11) ^ 47) + r * 3) === parsed) {
      index = r;
      break;
    }
  }
  if (index === null) {
    return null;
  }

  const selected = String(dataList[35 - index] || "").replace(/^0x/i, "");
  const random = String(randomHash || "").replace(/^0x/i, "");
  const mixed = (random + random).split("");
  const mixedLen = mixed.length;

  for (let t = 0; t < 64; t += 2) {
    const src = t / 2;
    if (src < selected.length) mixed[t] = selected[src];
  }
  for (let t = 65; t < 128; t += 2) {
    const src = 32 + (t - 65) / 2;
    if (src < selected.length) mixed[t] = selected[src];
  }

  const result = mixed.join("");
  if (result.length !== mixedLen) {
    throw new Error("Secret key derivation length mismatch");
  }
  return result;
}

function defaultHeaders() {
  return {
    accept: "application/json",
    "x-chain": X_CHAIN,
    "user-agent": USER_AGENT,
  };
}

async function requestSecretKey() {
  for (let attempt = 0; attempt < 15; attempt += 1) {
    const hash = generateRandomHash();
    const response = await fetch(`${API_BASE_URL}/api/secret/key`, {
      method: "POST",
      headers: {
        ...defaultHeaders(),
        "content-type": "application/json",
      },
      body: JSON.stringify({ hash }),
    });

    const text = await response.text();
    let data;
    try {
      data = JSON.parse(text);
    } catch {
      throw new Error(`Secret key response is not JSON: ${text.slice(0, 300)}`);
    }
    if (!response.ok) {
      throw new Error(
        `Secret key request failed: HTTP ${response.status} ${JSON.stringify(data).slice(0, 300)}`,
      );
    }

    const key = generateSecretKey(data, hash);
    if (key) return key;
  }

  throw new Error("Unable to derive usable X-Secret-Key after multiple attempts");
}

async function requestTextWithRetry(url, options, { attempts = 8, backoffMs = 400 } = {}) {
  let lastResponse = null;
  let lastText = "";

  for (let attempt = 1; attempt <= attempts; attempt += 1) {
    const response = await fetch(url, options);
    const text = await response.text();
    lastResponse = response;
    lastText = text;

    const tooManyRequests = response.status === 429 || /too many requests/i.test(text);
    if (!tooManyRequests) {
      return { response, text };
    }

    const delay = backoffMs * attempt;
    await sleep(delay);
  }

  return { response: lastResponse, text: lastText };
}

async function getSecretKey() {
  if (secretCache.key && secretCache.expiresAt > nowMs()) {
    return secretCache.key;
  }
  const newKey = await requestSecretKey();
  // Explorer renews every 5 minutes. Keep a safety margin.
  secretCache.key = newKey;
  secretCache.expiresAt = nowMs() + 4 * 60 * 1000;
  return newKey;
}

async function apiPost(endpoint, body = null, { withSecret = true } = {}) {
  const headers = {
    ...defaultHeaders(),
  };
  if (body !== null) headers["content-type"] = "application/json";
  if (withSecret) {
    headers["x-secret-key"] = await getSecretKey();
  }

  const { response, text } = await requestTextWithRetry(`${API_BASE_URL}${endpoint}`, {
    method: "POST",
    headers,
    body: body === null ? undefined : JSON.stringify(body),
  });
  let data;
  try {
    data = JSON.parse(text);
  } catch {
    data = { raw: text };
  }

  if (!response.ok) {
    throw new Error(
      `POST ${endpoint} failed: HTTP ${response.status} ${JSON.stringify(data).slice(0, 400)}`,
    );
  }

  return data;
}

async function rpcCall(method, params = []) {
  const payload = {
    jsonrpc: "2.0",
    id: crypto.randomInt(1, 1_000_000_000),
    method,
    params,
  };

  const { response, text } = await requestTextWithRetry(
    RPC_URL,
    {
      method: "POST",
      headers: {
        "content-type": "application/json",
      },
      body: JSON.stringify(payload),
    },
    { attempts: 10, backoffMs: 500 },
  );
  if (!response?.ok) {
    throw new Error(`RPC ${method} failed: HTTP ${response?.status} ${text?.slice(0, 400)}`);
  }

  let data;
  try {
    data = JSON.parse(text);
  } catch {
    throw new Error(`RPC ${method} returned non-JSON: ${text.slice(0, 300)}`);
  }

  if (data.error) {
    throw new Error(`RPC ${method} failed: ${JSON.stringify(data.error)}`);
  }
  return data.result;
}

async function rpcBatchGetCode(addresses) {
  const calls = addresses.map((address, index) => ({
    jsonrpc: "2.0",
    id: index + 1,
    method: "eth_getCode",
    params: [address, "latest"],
  }));
  const { response, text } = await requestTextWithRetry(
    RPC_URL,
    {
      method: "POST",
      headers: {
        "content-type": "application/json",
      },
      body: JSON.stringify(calls),
    },
    { attempts: 10, backoffMs: 500 },
  );

  if (!response?.ok) {
    throw new Error(`RPC batch eth_getCode failed: HTTP ${response?.status} ${text?.slice(0, 400)}`);
  }

  let data;
  try {
    data = JSON.parse(text);
  } catch {
    throw new Error(`RPC batch eth_getCode returned non-JSON: ${text.slice(0, 300)}`);
  }

  const map = new Map();
  for (const item of data) {
    if (item.error) {
      map.set(item.id, { error: item.error });
    } else {
      map.set(item.id, { result: item.result });
    }
  }
  return addresses.map((address, index) => {
    const entry = map.get(index + 1);
    const codeHex = entry?.result || "0x";
    return {
      address,
      codeHex,
      bytecodeSize: Math.max(0, (String(codeHex).length - 2) / 2),
      hasCode: String(codeHex) !== "0x",
      error: entry?.error || null,
    };
  });
}

async function rpcGetCodeSingle(address) {
  const codeHex = await rpcCall("eth_getCode", [address, "latest"]);
  return {
    address,
    codeHex,
    bytecodeSize: Math.max(0, (String(codeHex).length - 2) / 2),
    hasCode: String(codeHex) !== "0x",
    error: null,
  };
}

function parseAddressMapFromModule(moduleContents) {
  const match = moduleContents.match(/JSON\.parse\('(.+?)'\)/);
  if (!match) {
    throw new Error("Unable to find contract JSON blob in extracted module");
  }
  const jsonLiteral = match[1].replace(/\\'/g, "'").replace(/\\"/g, '"');
  return JSON.parse(jsonLiteral);
}

function sanitizeFilename(name) {
  return String(name).replace(/[<>:"/\\|?*\u0000-\u001F]/g, "_");
}

async function fetchAllContractListEntries() {
  const all = [];
  let page = 1;
  const size = 100;
  let total = null;

  while (true) {
    const payload = await apiPost("/api/address/contract/code/list", { page, size });
    const pageList = Array.isArray(payload.CALIST) ? payload.CALIST : [];
    if (total === null) {
      total = Number.parseInt(payload.TCNT || payload.VCNT || `${pageList.length}`, 10);
    }
    all.push(...pageList);
    if (pageList.length < size || all.length >= total) break;
    page += 1;
  }

  return all;
}

async function main() {
  await ensureDir(CONTEXT_ROOT);
  await ensureDir(path.join(CONTEXT_ROOT, "contracts", "details"));
  await ensureDir(path.join(CONTEXT_ROOT, "abis"));
  await ensureDir(path.join(CONTEXT_ROOT, "sources"));
  await ensureDir(path.join(CONTEXT_ROOT, "onchain"));
  await ensureDir(path.join(CONTEXT_ROOT, "raw"));

  const moduleContents = await fs.readFile(CONTRACT_MODULE_PATH, "utf8");
  const frontendAddressMap = parseAddressMapFromModule(moduleContents);

  const importantAddresses = IMPORTANT_CONTRACT_KEYS.map((key) => ({
    key,
    address: toLowerAddress(frontendAddressMap[key]),
  })).filter((x) => Boolean(x.address));

  const [generalSummary, generalOverview, contractList] = await Promise.all([
    apiPost("/api/general/summary", {}),
    apiPost("/api/general", {
      types: [
        "BLOCK",
        "NORMAL_TRANSACTION_TOTAL_COUNT",
        "INTERNAL_TRANSACTION_TOTAL_COUNT",
        "ACCOUNT",
        "BALANCE",
      ],
    }),
    fetchAllContractListEntries(),
  ]);

  const listedAddresses = dedupeAddresses(contractList.map((c) => c.ADDR));
  const sourceTargets = dedupeAddresses([
    ...listedAddresses,
    ...importantAddresses.map((x) => x.address),
  ]);

  const detailResults = [];
  for (const address of sourceTargets) {
    try {
      const details = await apiPost("/api/address/contract/code", { address });
      detailResults.push({ address, ok: true, details });
      await writeJson(
        path.join(CONTEXT_ROOT, "contracts", "details", `${address}.json`),
        details,
      );

      if (typeof details?.ABI === "string" && details.ABI.trim()) {
        try {
          const abi = JSON.parse(details.ABI);
          await writeJson(path.join(CONTEXT_ROOT, "abis", `${address}.json`), abi);
        } catch {
          // keep raw details only
        }
      }

      if (Array.isArray(details?.SCLIST)) {
        const sourceDir = path.join(CONTEXT_ROOT, "sources", address);
        await ensureDir(sourceDir);
        for (const sourceFile of details.SCLIST) {
          const fileName = sanitizeFilename(sourceFile?.FNM || "Contract.sol");
          const sourceCode = String(sourceFile?.SC ?? "");
          await fs.writeFile(path.join(sourceDir, fileName), sourceCode);
        }
      }
    } catch (error) {
      detailResults.push({
        address,
        ok: false,
        error: error instanceof Error ? error.message : String(error),
      });
    }
  }

  const mapAddresses = dedupeAddresses(Object.values(frontendAddressMap));
  const chunks = [];
  for (let i = 0; i < mapAddresses.length; i += 20) {
    chunks.push(mapAddresses.slice(i, i + 20));
  }

  const codeCheck = [];
  for (const chunk of chunks) {
    try {
      // eslint-disable-next-line no-await-in-loop
      const result = await rpcBatchGetCode(chunk);
      codeCheck.push(...result);
    } catch {
      for (const address of chunk) {
        try {
          // eslint-disable-next-line no-await-in-loop
          const single = await rpcGetCodeSingle(address);
          codeCheck.push(single);
        } catch (error) {
          codeCheck.push({
            address,
            codeHex: "0x",
            bytecodeSize: 0,
            hasCode: false,
            error: error instanceof Error ? error.message : String(error),
          });
        }
        // eslint-disable-next-line no-await-in-loop
        await sleep(120);
      }
    }
    // eslint-disable-next-line no-await-in-loop
    await sleep(200);
  }

  const chainInfo = {
    rpcUrl: RPC_URL,
    chainIdHex: await rpcCall("eth_chainId"),
    blockNumberHex: await rpcCall("eth_blockNumber"),
    netVersion: await rpcCall("net_version"),
    clientVersion: await rpcCall("web3_clientVersion"),
    checkedAt: new Date().toISOString(),
  };

  const importantStatus = importantAddresses.map((x) => {
    const detail = detailResults.find((d) => d.address === x.address);
    const onchain = codeCheck.find((c) => c.address === x.address);
    return {
      key: x.key,
      address: x.address,
      detailOk: Boolean(detail?.ok),
      detailStatus: detail?.ok ? detail?.details?.STS ?? "UNKNOWN" : "NOT_AVAILABLE",
      hasCode: Boolean(onchain?.hasCode),
      bytecodeSize: onchain?.bytecodeSize ?? 0,
    };
  });

  await writeJson(path.join(CONTEXT_ROOT, "raw", "general-summary.json"), generalSummary);
  await writeJson(path.join(CONTEXT_ROOT, "raw", "general-overview.json"), generalOverview);
  await writeJson(path.join(CONTEXT_ROOT, "contracts", "address-map.json"), frontendAddressMap);
  await writeJson(path.join(CONTEXT_ROOT, "contracts", "list.json"), contractList);
  await writeJson(path.join(CONTEXT_ROOT, "contracts", "detail-index.json"), detailResults);
  await writeJson(path.join(CONTEXT_ROOT, "onchain", "chain-info.json"), chainInfo);
  await writeJson(path.join(CONTEXT_ROOT, "onchain", "code-check.json"), codeCheck);
  await writeJson(path.join(CONTEXT_ROOT, "important-contracts.json"), importantStatus);

  const summary = {
    fetchedAt: new Date().toISOString(),
    contractListCount: contractList.length,
    frontendAddressMapCount: Object.keys(frontendAddressMap).length,
    detailFetchedCount: detailResults.filter((d) => d.ok).length,
    detailMissingCount: detailResults.filter((d) => !d.ok).length,
    abiCount: detailResults.filter((d) => d.ok && typeof d.details?.ABI === "string").length,
    sourceContractCount: detailResults.filter((d) => d.ok && Array.isArray(d.details?.SCLIST)).length,
    onchainCodeAddressCount: codeCheck.filter((c) => c.hasCode).length,
    onchainNoCodeAddressCount: codeCheck.filter((c) => !c.hasCode).length,
    importantContracts: importantStatus,
  };
  await writeJson(path.join(CONTEXT_ROOT, "summary.json"), summary);

  console.log("Context fetch complete.");
  console.log(JSON.stringify(summary, null, 2));
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
