# Reproducibility Guide

## Prerequisites

- **Lean 4.15.0** (managed by elan)
- **Lake** (Lean's build tool, bundled with Lean)
- Linux or macOS
- Network access (for dependency fetching)

## Quick Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_futamura_adelic.sh
```

This script performs:
1. Strict build (`lake build --wfail`)
2. Sorry/admit grep (must be empty)
3. Demo executable runs
4. Hostile-environment tests
5. Portability checks
6. SHA256 checksums

## Manual Steps

### 1. Fetch Dependencies

```bash
cd RESEARCHER_BUNDLE
lake update
```

### 2. Build

```bash
lake build --wfail
```

The `--wfail` flag treats warnings as errors.

### 3. Verify No Sorries

```bash
grep -rn "sorry\|admit" HeytingLean/ | grep -v "Main.lean"
# Should return empty
```

### 4. Run Demos

```bash
lake exe tropical_relu_demo
lake exe free_energy_demo
lake exe rg_flow_demo
lake exe sheaf_diffusion_demo
lake exe adelic_futamura_demo
lake exe organic_alignment_stack_test
```

### 5. Hostile Environment Test

```bash
# Test with minimal PATH
env -i PATH="" .lake/build/bin/tropical_relu_demo
```

## Offline Build

If you have dependencies cached in `.lake/packages/`:

```bash
FUTAMURA_ADELIC_SKIP_UPDATE=1 ./scripts/verify_futamura_adelic.sh
```

## Toolchain Pinning

The `lean-toolchain` file pins Lean 4.15.0:

```
leanprover/lean4:v4.15.0
```

The `lake-manifest.json` pins all dependencies including Mathlib v4.24.0.

## Checksum Verification

The `reports/SHA256SUMS.txt` contains checksums of all source files (excluding `.lake/`, `build/`, `vendor/`).

Verify with:
```bash
sha256sum -c reports/SHA256SUMS.txt
```
