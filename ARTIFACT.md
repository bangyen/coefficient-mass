# Reproducing the artifact

The repository supports macOS and Linux. A cold build requires network access
to obtain Python packages, the pinned Lean/Mathlib toolchain and, on first PDF
build, TeX packages. The release supplement is self-contained with respect to
repository sources and the proof-guard submodule, but not third-party package
caches.

## Prerequisites

- Git with submodule support
- Python 3.12 or newer
- [uv](https://docs.astral.sh/uv/)
- [just](https://just.systems/)
- Lean via [elan](https://github.com/leanprover/elan)
- Tectonic for PDFs
- ChkTeX for `just tex` (optional)

## Cold-machine verification

```bash
git clone --recurse-submodules https://github.com/bangyen/coefficient-mass.git
cd coefficient-mass
git checkout v1.0.3
uv sync --locked
just check
lake exe cache get
just lean
just pdf
```

Expected success signals are `505 passed` from `just check`, a warning-free
Lean build followed by successful proof guards from `just lean`, and eight
PDFs in `papers/` from `just pdf`. On the reference release runner, the Python
checks take about 1–2 minutes; the first Lean and TeX builds take longer while
downloading caches. TeX may report known box-layout warnings, but the build
fails on undefined citations or references.

The exact Python dependency graph is in `uv.lock`; the Lean toolchain and
Mathlib commit are in `lean-toolchain` and `lake-manifest.json`. The Git tag,
not a mutable branch head, identifies the claimed artifact state.

## Release-supplement verification

The release publishes `SHA256SUMS` beside the source and submission bundles.
After downloading both the checksum file and source bundle, check for transfer
corruption with one of:

```bash
sha256sum --check SHA256SUMS --ignore-missing  # Linux
shasum -a 256 --check SHA256SUMS               # macOS
```

The checksums travel with the release and therefore detect corruption, not a
compromised release account. Git tag verification is the independent source
identity check.

The source supplement already contains the recursively pinned `scripts/`
submodule. It can be built without a Git checkout:

```bash
tar -xzf coefficient-mass-1.0.3-source.tar.gz
cd coefficient-mass-1.0.3
uv sync --locked
just check
lake exe cache get
just lean
just pdf
```

Third-party tools and package caches still require the network access noted
above.
