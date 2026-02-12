# Repository Guidelines

## Project Structure & Module Organization

- `scripts/`: runnable Node.js tools (ESM). Key entrypoints:
  - `scripts/bid-wallet.mjs`: logs into `msu.io`, fetches seller inventory, signs EIP-712 orders, and creates Marketplace offers.
  - `scripts/fetch-msu-context.mjs`: collects onchain/offchain context (ABIs, sources, address map) into `data/context/`.
- `data/context/`: generated contract metadata (e.g. `data/context/contracts/address-map.json`, `data/context/abis/`).
- `data/extracted/`: reverse-engineered frontend module snapshots used for reference.
- `tmp/`: runtime outputs (reports, inventory dumps). Ignored by git.

## Build, Test, and Development Commands

- `npm install`: install dependencies.
- `npm run fetch:context`: refresh `data/context/` (ABIs, sources, address map).
- `npm run bid:wallet -- --help`: show CLI options.
- Example dry run:
  - `npm run bid:wallet -- --seller 0x... --private-key 0x... --dry-run true`

## Coding Style & Naming Conventions

- JavaScript modules are ESM (`"type": "module"`). Prefer explicit imports and async/await.
- Keep scripts self-contained and CLI-friendly: parse args, validate inputs, write a JSON report to `tmp/`.
- Naming:
  - Files: kebab-case for scripts (e.g. `bid-wallet.mjs`)
  - Variables: camelCase; constants in UPPER_SNAKE_CASE only for true constants.

## Testing Guidelines

- No formal test suite is currently set up.
- When changing API parsing/signing logic, validate with a small batch run first:
  - `--dry-run true`, then `--max-offers 1..10`, then full run.

## Commit & Pull Request Guidelines

- Commit messages in this repo are short and action-oriented (examples: `init`, `chore: ...`, `Add ...`).
- Prefer Conventional Commit style for new work: `feat: ...`, `fix: ...`, `chore: ...`.
- PRs should include:
  - What changed, how to run it, and any risk/rollback notes.
  - Redact secrets and wallet addresses when sharing logs.

## Security & Configuration Tips

- Never commit private keys. Use env vars like `BIDDER_PRIVATE_KEY` or local `.env` (ignored).
- Do not commit `tmp/` artifacts; reports/inventory dumps are generated per run.
