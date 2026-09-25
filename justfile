PAPERS := "coefficient-mass coefficient-mass-attainment coefficient-mass-complex coefficient-mass-rows"
CHKTEX_OFF := "-n1 -n2 -n3 -n8 -n9 -n12 -n17 -n24 -n25 -n36 -n40 -n44"

# lint, then every test: citations, roadmap labels, certificate sweeps
check: lint test

lint:
    uv run ruff format --check tests tools
    uv run ruff check tests tools
    uv run codespell papers tests tools CoefficientMass README.md ROADMAP.md

# chktex on the papers; the disabled warnings are ones the house style
# contradicts (`~` before references, dashes in DOIs, `{}` around brackets)
tex:
    #!/usr/bin/env bash
    set -euo pipefail
    out=$(chktex -q -v0 {{CHKTEX_OFF}} papers/*.tex)
    if [ -n "$out" ]; then echo "$out" >&2; exit 1; fi

# every test, the certificate sweeps included (~10s)
test:
    uv run pytest -q

# the coefficient-mass sweep with its printed tallies
sweep:
    uv run python tests/sweep.py

# compile the papers, failing on an undefined reference or citation
pdf:
    #!/usr/bin/env bash
    set -euo pipefail
    command -v tectonic >/dev/null 2>&1 || {
        echo "tectonic is required (brew install tectonic)" >&2
        exit 1
    }
    for paper in {{PAPERS}}; do
        tectonic "papers/$paper.tex" 2>&1 | tee "papers/$paper.build.log"
        if grep -E "(Reference|Citation) .* undefined" "papers/$paper.build.log"; then
            echo "$paper: undefined reference" >&2
            exit 1
        fi
    done

# print pinned numbering for a citing repo, e.g. `just pin coefficient-mass:3.4`
pin +refs:
    uv run python tools/numbering.py {{refs}}

# build the Lean statements warning-free and run the lean-guards checks
lean:
    lake --wfail build
    lake lint
    ./scripts/check_all.sh
