# MSU Marketplace Bid/Offer Bot (Henesys)

This repo contains a small Node.js script that can create **Marketplace offers** (buyer-side “bids”) on **MapleStory Universe (MSU)** assets on the Henesys chain.

Primary use case: you want to move assets from a friend’s wallet to yours when direct transfers aren’t possible. You place offers on all their items/characters, and your friend accepts the offers in the UI.

## What It Does

- Logs into `msu.io` using the same wallet that will place the offers (cookie-based web auth).
- Fetches the seller wallet inventory (owned assets) from MSU marketplace.
- Builds and signs an EIP-712 `Order` for each asset (buyer-side offer).
- Submits offers to the MSU marketplace API.
- Can optionally send an onchain `approve()` for `NextMeso` allowance to `MarketplaceV2`.

Supported asset types:
- `items` (MaplestoryEquip / ERC-721)
- `characters` (MaplestoryCharacter / ERC-721)

## Safety / Important Notes

- The script defaults to `DRY_RUN=true` (it will **not** submit offers until you explicitly disable dry-run).
- You are handling a **private key**. Do not paste it into logs, screenshots, or commit it.
- This is an automation tool that interacts with a third-party service (MSU). Use at your own risk (rate limits, ToS, account restrictions, etc.).

## Requirements

- Node.js 18+ (recommended: Node 20+)
- npm

No browser/Metamask is required for the script itself: it signs using the provided private key via `viem`.

## Install

```bash
npm install
```

Optional (context extraction / contract metadata already exists in `data/context`):
```bash
npm run fetch:context
```

## Configuration

You can configure via CLI flags or env vars.

### Required

- Seller wallet (your friend): `--seller 0x...` or `SELLER_ADDRESS`
- Bidder private key (your wallet): `--private-key 0x...` or `BIDDER_PRIVATE_KEY`

### Common Options

- `--dry-run true|false` (default: `true`)
- `--approve true|false` (default: `false`)
  - If `true`, the script may send an onchain `approve(MarketplaceV2, maxUint256)` on `NextMeso` when allowance is insufficient.
- `--price-meso 1` (default: `1`)
  - Fixed pricing mapping. If your token has decimals, this is converted using `NextMeso.decimals()`.
- `--duration-days 14` (default: `14`)
  - Offer expiration window.
- `--types items,characters` (default: `items,characters`)
- `--max-offers 50` (default: unlimited)
- `--throttle-ms 250` (default: `250`)
- `--dump-inventory true|false` (default: `true`)
  - Writes the raw inventory response into `tmp/` for debugging.

### Network Defaults (Henesys)

- RPC: `https://henesys-rpc.msu.io`
- MSU base URL: `https://msu.io`
- Chain ID: `68414`

You can override:
- `--rpc-url ...` or `RPC_URL`
- `--msu-base-url ...` or `MSU_BASE_URL`

## Usage

Show help:
```bash
node scripts/bid-wallet.mjs --help
```

### 1) Dry run (recommended first)

This logs in, fetches inventory, calculates the planned offers + total cost, but does not submit offers.

```bash
SELLER_ADDRESS=0xSELLER_WALLET \
BIDDER_PRIVATE_KEY=0xYOUR_PRIVATE_KEY \
npm run bid:wallet -- --dry-run true --types items,characters --price-meso 1
```

### 2) Submit a small batch first

```bash
npm run bid:wallet -- \
  --seller 0xSELLER_WALLET \
  --private-key 0xYOUR_PRIVATE_KEY \
  --dry-run false \
  --max-offers 10
```

### 3) Full run (submit offers)

```bash
npm run bid:wallet -- \
  --seller 0xSELLER_WALLET \
  --private-key 0xYOUR_PRIVATE_KEY \
  --dry-run false
```

### 4) Full run with automatic allowance approval

If your friend can’t accept offers because your `NextMeso` allowance is too low, use:

```bash
npm run bid:wallet -- \
  --seller 0xSELLER_WALLET \
  --private-key 0xYOUR_PRIVATE_KEY \
  --approve true \
  --dry-run false
```

## Output Files

The script writes:
- Inventory dump (optional): `tmp/inventory-<seller>-<timestamp>.json`
- Execution report: `tmp/bid-wallet-report-<timestamp>.json`

## Troubleshooting

### “No owned tokenIds found…”

This usually means the inventory endpoint returned a structure the parser didn’t recognize.

1. Find the latest `tmp/inventory-*.json`
2. Share the shape (redact addresses if you want)
3. Update the parser to match the actual response

### HTTP 401

The MSU web auth is cookie-based. The script:
- Signs `/api/web/message`
- Calls `/api/web/signin-wallet`
- Auto-tries `/api/web/token/refresh-web` on 401 and retries a few times

If you still get 401s, MSU may have changed the auth flow or requires additional headers/fields.

### Rate limiting / flakiness

Use:
- `--throttle-ms 500` (or higher)
- `--max-offers` to split into multiple runs

## Repository Scripts

- `npm run fetch:context`: fetches chain/contracts context (ABIs, sources, address map) into `data/context/`
- `npm run bid:wallet`: runs the offer creation script (`scripts/bid-wallet.mjs`)

