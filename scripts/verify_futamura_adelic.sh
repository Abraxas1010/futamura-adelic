#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

mkdir -p reports artifacts

TRANSCRIPT="reports/BUILD_TRANSCRIPT_STRICT.txt"
GREP_OUT="reports/GREP_SORRY_ADMIT.txt"
SHA_OUT="reports/SHA256SUMS.txt"
GITCFG="reports/GITCONFIG_EFFECTIVE.txt"

echo "[verify_futamura_adelic] root=$ROOT_DIR" | tee "$TRANSCRIPT"

{
  echo
  echo "[versions] lean"
  lean --version
  echo
  echo "[versions] lake"
  lake --version

  echo
  echo "[env] disable mathlib cache on update (for portability)"
  export MATHLIB_NO_CACHE_ON_UPDATE="${MATHLIB_NO_CACHE_ON_UPDATE:-1}"
  echo "MATHLIB_NO_CACHE_ON_UPDATE=$MATHLIB_NO_CACHE_ON_UPDATE"

  echo
  echo "[git] configure URL policy"
  if [[ "${FUTAMURA_ADELIC_DISABLE_VENDOR:-0}" != "1" ]] && \
     [[ -d "$ROOT_DIR/vendor/git/github.com/leanprover-community/mathlib4" ]]; then
    echo "[git] using vendor mirrors under vendor/git/ (offline-capable)"
    cat >"$GITCFG" <<EOF
[url "vendor/git/github.com/"]
  insteadOf = https://github.com/
EOF
  else
    if [[ "${FUTAMURA_ADELIC_DISABLE_VENDOR:-0}" == "1" ]]; then
      echo "[git] vendor mirrors disabled by FUTAMURA_ADELIC_DISABLE_VENDOR=1; using network URLs"
    else
      echo "[git] no vendor mirrors found; using network URLs"
    fi
    cat >"$GITCFG" <<EOF
# no URL rewrites
EOF
  fi

  export GIT_CONFIG_GLOBAL="$ROOT_DIR/$GITCFG"
  export GIT_CONFIG_NOSYSTEM=1
  echo "GIT_CONFIG_GLOBAL=$GIT_CONFIG_GLOBAL"
  echo "GIT_CONFIG_NOSYSTEM=$GIT_CONFIG_NOSYSTEM"
  echo
  echo "[gitconfig]"
  cat "$GITCFG"

  echo
  echo "[lake] update"
  if [[ "${FUTAMURA_ADELIC_SKIP_UPDATE:-0}" == "1" ]]; then
    echo "skipping: FUTAMURA_ADELIC_SKIP_UPDATE=1"
  else
    lake update
  fi

  echo
  echo "[lake] build executables (strict)"
  lake build --wfail tropical_relu_demo
  lake build --wfail free_energy_demo
  lake build --wfail rg_flow_demo
  lake build --wfail sheaf_diffusion_demo
  lake build --wfail adelic_futamura_demo
  lake build --wfail organic_alignment_stack_test

  echo
  echo "[run] tropical_relu_demo"
  lake exe tropical_relu_demo
  echo "[run] free_energy_demo"
  lake exe free_energy_demo
  echo "[run] rg_flow_demo"
  lake exe rg_flow_demo
  echo "[run] sheaf_diffusion_demo"
  lake exe sheaf_diffusion_demo
  echo "[run] adelic_futamura_demo"
  lake exe adelic_futamura_demo
  echo "[run] organic_alignment_stack_test"
  lake exe organic_alignment_stack_test

  echo
  echo "[robustness] minimal environment (PATH=\"\")"
  env -i PATH="" "$ROOT_DIR/.lake/build/bin/tropical_relu_demo" >/dev/null
  env -i PATH="" "$ROOT_DIR/.lake/build/bin/free_energy_demo" >/dev/null
  env -i PATH="" "$ROOT_DIR/.lake/build/bin/rg_flow_demo" >/dev/null
  env -i PATH="" "$ROOT_DIR/.lake/build/bin/sheaf_diffusion_demo" >/dev/null
  env -i PATH="" "$ROOT_DIR/.lake/build/bin/adelic_futamura_demo" >/dev/null
  env -i PATH="" "$ROOT_DIR/.lake/build/bin/organic_alignment_stack_test" >/dev/null

  echo
  echo "[portability] dynamic deps (best effort)"
  if command -v ldd >/dev/null 2>&1; then
    ldd "$ROOT_DIR/.lake/build/bin/tropical_relu_demo" | tee reports/LDD_tropical_relu_demo.txt
    ldd "$ROOT_DIR/.lake/build/bin/free_energy_demo" | tee reports/LDD_free_energy_demo.txt
    ldd "$ROOT_DIR/.lake/build/bin/rg_flow_demo" | tee reports/LDD_rg_flow_demo.txt
    ldd "$ROOT_DIR/.lake/build/bin/sheaf_diffusion_demo" | tee reports/LDD_sheaf_diffusion_demo.txt
    ldd "$ROOT_DIR/.lake/build/bin/adelic_futamura_demo" | tee reports/LDD_adelic_futamura_demo.txt
    ldd "$ROOT_DIR/.lake/build/bin/organic_alignment_stack_test" | tee reports/LDD_organic_alignment_stack_test.txt
  else
    echo "skipping: ldd not found"
  fi
} 2>&1 | tee -a "$TRANSCRIPT"

echo "[audit] grep for markers under HeytingLean/" | tee "$GREP_OUT"
if command -v rg >/dev/null 2>&1; then
  rg -n --type lean -S "\\b(sorry|admit)\\b" HeytingLean >>"$GREP_OUT" 2>&1 || true
  if rg -n --type lean -S "\\b(sorry|admit)\\b" HeytingLean >/dev/null 2>&1; then
    echo "[audit] FAILED: found forbidden markers" | tee -a "$TRANSCRIPT"
    exit 1
  fi
else
  echo "warning: rg not found; skipping grep check" | tee -a "$GREP_OUT"
fi

echo "[hashes] sha256 over bundle (excluding .lake/, build/, vendor/)" | tee -a "$TRANSCRIPT"
rm -f "$SHA_OUT"
(
  cd "$ROOT_DIR"
  find . -type f \
    -not -path './.lake/*' \
    -not -path './build/*' \
    -not -path './vendor/*' \
    -not -path './reports/SHA256SUMS.txt' \
    -print0 \
    | sort -z \
    | xargs -0 sha256sum
) >"$SHA_OUT"

echo "[verify_futamura_adelic] OK" | tee -a "$TRANSCRIPT"

