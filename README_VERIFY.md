# Futamura–Adelic (Organic Alignment) Verification (Self-Contained Bundle)

## A) System prerequisites

- Lean is managed by `elan`; `lake` will fetch deps.
- Linux/macOS expected.
- Network access is required unless `vendor/git/` is provided.
- Optional: set `FUTAMURA_ADELIC_DISABLE_VENDOR=1` to force network URLs.

## B) One-command verification

```bash
./scripts/verify_futamura_adelic.sh
```

If you are offline but already have dependencies present under `.lake/packages/`, you can skip `lake update`:

```bash
FUTAMURA_ADELIC_SKIP_UPDATE=1 ./scripts/verify_futamura_adelic.sh
```

## C) What it checks

- strict build (`--wfail`)
- grep for `sorry`/`admit` under `HeytingLean/`
- builds + runs the organic-alignment demo executables
- hostile-environment runs (`env -i PATH="" ...`)
- portability spot-check (`ldd`, if available)
- reproducible `SHA256SUMS` (excluding `.lake/`, `build/`, `vendor/`)

## D) Where to look

- `reports/BUILD_TRANSCRIPT_STRICT.txt`
- `reports/GREP_SORRY_ADMIT.txt`
- `reports/SHA256SUMS.txt`

