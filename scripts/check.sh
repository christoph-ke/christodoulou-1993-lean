#!/usr/bin/env bash
# Full verification: source checks, frozen-file hashes, build, axiom audit.
# Prerequisite (once): `lake exe cache get` to download the Mathlib build cache.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== source checks"
python3 scripts/check_source.py

echo "== frozen files (byte-identical to the sealed statements)"
if command -v sha256sum > /dev/null; then
  sha256sum --check --strict scripts/frozen-files.sha256
else
  shasum -a 256 --check --strict scripts/frozen-files.sha256
fi

echo "== build"
lake build

echo "== axiom audit"
lake env lean scripts/AxiomAudit.lean | tee .lake/axiom-audit.out
diff -u scripts/AxiomAudit.expected .lake/axiom-audit.out

echo "ALL CHECKS PASSED"
