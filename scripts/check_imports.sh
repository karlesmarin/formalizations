#!/bin/sh
# encaje: guarda de CI del repositorio de formalizaciones (no es herramienta de Excovery: vive con el repositorio)
# Every module under Formalizations/ must be imported by Formalizations.lean: a module left out is neither built by
# the CI nor documented (docs.yml), and nobody would find it. Fails listing the modules that are missing.
set -e
cd "$(dirname "$0")/.."
MISSING=$(find Formalizations -name '*.lean' | sed 's#\.lean$##; s#/#.#g' | sort | while read -r m; do
  grep -q "^public import $m\$\|^import $m\$" Formalizations.lean || echo "$m"
done)
if [ -n "$MISSING" ]; then echo "FAIL: modules not imported by Formalizations.lean:"; echo "$MISSING"; exit 1; fi
echo "OK: every module is imported by Formalizations.lean"
