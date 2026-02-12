# MSU Marketplace Context Report

Generated on: `2026-02-12T23:16:20.335Z`

## 1) Chain / RPC confirmation
- RPC: `https://henesys-rpc.msu.io`
- `eth_chainId`: `0x10b3e` (`68414`)
- `net_version`: `68414`
- `clientVersion`: `v0.8.0@44b20d219471a0e08bd163b7466e3d8620ff45f2`

Source: `data/context/onchain/chain-info.json`

## 2) Explorer API auth (required)
The Xangle explorer API is callable directly but needs browser-like headers + dynamic secret key.

Required request headers:
- `X-Chain: NEXON`
- `User-Agent`: browser-like UA (curl default gets 404)
- `X-Secret-Key`: dynamic (except `/api/secret/key`)

Secret flow (reverse-engineered from explorer bundle):
1. `POST /api/secret/key` with body `{ "hash": "0x..." }`
2. Response includes `{ SECRET, DATALIST }`
3. Derive `X-Secret-Key` using the same obfuscated algorithm used by frontend (`tmp/BgxnjiVI.js`)

Implemented in: `scripts/fetch-msu-context.mjs`

## 3) Contracts discovered
- Frontend address map entries: `101`
- Unique addresses checked on RPC: `89`
- Addresses with deployed bytecode: `80`
- Addresses without bytecode on Henesys: `9`

No-code addresses list in:
- `data/context/onchain/code-check.json`

## 4) Verified source/ABI coverage (explorer)
- Verified contract detail payloads fetched: `26`
- ABI files parsed/written: `25` (contract `USDt` has empty ABI string in payload)
- Missing in explorer contract-code endpoint: `1`
- Missing address: `0x6813869c3e5dec06e6f88b42d41487dc5d7abf57` (`MarketplaceV2`)

Indexes:
- Contract list: `data/context/contracts/list.json`
- Frontend map: `data/context/contracts/address-map.json`
- Per-address detail status: `data/context/contracts/detail-index.json`
- ABIs: `data/context/abis/`
- Sources: `data/context/sources/`

## 5) Key marketplace contracts (current status)
- `Marketplace` `0xf1c82c082af3de3614771105f01dc419c3163352`: verified source+ABI available
- `MarketplaceV2` `0x6813869c3e5dec06e6f88b42d41487dc5d7abf57`: bytecode present, source not found on explorer endpoint
- `OrderBook` `0xdf6d3658335a6608c8c76470b53250add03bcc77`: verified source+ABI available
- `NextMeso` `0x07e49ad54fcd23f6e7b911c2068f0148d1827c08`: verified source+ABI available

Snapshot: `data/context/important-contracts.json`

## 6) Marketplace app reverse-engineered context (from `msu.io`)
Already extracted in prior step (files under `data/extracted/modules`):
- EIP-712 order signing domain:
  - `name: "Marketplace"`
  - `version: "1.0"`
  - `chainId: 68414`
  - `verifyingContract: MarketplaceV2 (0x6813...bf57)`
- Order fields:
  - `isSeller, maker, listingTime, expirationTime, tokenAddress, tokenAmount, nftAddress, nftTokenId, salt`
- API groups identified:
  - `/api/marketplace/...`
  - `/orderbook/items/...` (`buy`, `sell`, `bids`, `trade-history`, `mybids`, etc.)
  - auth flow `/api/web/*` (message/signin-wallet/token refresh)

Primary extracted modules:
- `data/extracted/modules/13716__2268-ec9cbe7f93c0e7a0.js`
- `data/extracted/modules/56933__2268-ec9cbe7f93c0e7a0.js`
- `data/extracted/modules/25703__2268-ec9cbe7f93c0e7a0.js`
- `data/extracted/modules/57600__8009-cbb84f0b3e10ffb3.js`
- `data/extracted/modules/97134__8009-cbb84f0b3e10ffb3.js`

## 7) Practical blocker to plan for
- `MarketplaceV2` source/ABI is not returned by explorer contract-code endpoint.
- For bot implementation, ABI for V2 must be obtained via:
  - other verified artifact sources, or
  - event/function selector reconstruction from transactions/logs and frontend usage.
