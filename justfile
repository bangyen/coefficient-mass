PAPERS := "coefficient-mass coefficient-mass-attainment coefficient-mass-complex coefficient-mass-rows"

# lint, then every test: citations, roadmap labels, certificate sweeps
check: lint test

lint:
    uv run ruff format --check tests tools
    uv run ruff check tests tools

# every test, the certificate sweeps included (~5s)
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
        tectonic "$paper.tex" 2>&1 | tee "$paper.build.log"
        if grep -E "(Reference|Citation) .* undefined" "$paper.build.log"; then
            echo "$paper: undefined reference" >&2
            exit 1
        fi
    done

# print pinned numbering for a citing repo, e.g. `just pin coefficient-mass:3.4`
pin +refs:
    uv run python tools/numbering.py {{refs}}
