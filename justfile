PAPERS := "coefficient-mass coefficient-mass-attainment coefficient-mass-complex coefficient-mass-rows"

# lint, citation checks, and the certificate sweep
check: lint test sweep

lint:
    ruff format --check tests
    ruff check tests

# every numbered cross-reference between the papers names the right result
test:
    python -m pytest -q

# the seeded certificate sweeps and exact worked numbers (~2s)
sweep:
    python tests/sweep.py

# compile the papers; PDFs are ignored generated files
pdf:
    #!/usr/bin/env bash
    set -euo pipefail
    command -v tectonic >/dev/null 2>&1 || {
        echo "tectonic is required (brew install tectonic)" >&2
        exit 1
    }
    for paper in {{PAPERS}}; do tectonic "$paper.tex"; done

# print pinned numbering for a citing repo, e.g. `just pin coefficient-mass:3.4`
pin +refs:
    python tests/numbering.py {{refs}}
