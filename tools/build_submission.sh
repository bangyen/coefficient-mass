#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

tracked_state=$(git status --porcelain --untracked-files=all)
if [[ -n "$tracked_state" ]]; then
  echo "submission packaging requires a clean worktree so HEAD, metadata and sources agree" >&2
  exit 1
fi

version=$(sed -n 's/^version = "\([^"]*\)"/\1/p' pyproject.toml)
if [[ -z "$version" ]]; then
  echo "could not read project version" >&2
  exit 1
fi
if [[ ! -f papers/coefficient-mass.pdf ]]; then
  echo "papers/coefficient-mass.pdf is missing; run 'just pdf' first" >&2
  exit 1
fi
if [[ ! -f scripts/check_all.sh ]]; then
  echo "proof-guard submodule is missing; run 'git submodule update --init'" >&2
  exit 1
fi

uv run pytest -q tests/test_metadata.py
tectonic papers/coefficient-mass.tex >/dev/null

stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
source_root="$stage/coefficient-mass-$version"
mkdir -p "$source_root/scripts" dist/release dist/jnt dist/arxiv

git archive --format=tar HEAD | tar -xf - -C "$source_root"
git -C scripts archive --format=tar HEAD | tar -xf - -C "$source_root/scripts"

tar -czf "dist/release/coefficient-mass-$version-source.tar.gz" \
  -C "$stage" "coefficient-mass-$version"

cp papers/coefficient-mass.pdf "dist/jnt/coefficient-mass-$version.pdf"
cp papers/coefficient-mass.tex "dist/jnt/coefficient-mass-$version.tex"
cp submission/jnt/cover-letter.md dist/jnt/
cp submission/jnt/title-page.md dist/jnt/
cp submission/jnt/metadata.yml dist/jnt/
cp submission/suggested-reviewers.md dist/jnt/
cp SUBMISSION.md ARTIFACT.md dist/jnt/
cp "dist/release/coefficient-mass-$version-source.tar.gz" dist/jnt/

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "dist/release/coefficient-mass-$version-source.tar.gz" \
    | sed 's#dist/release/##' > dist/jnt/SHA256SUMS
else
  shasum -a 256 "dist/release/coefficient-mass-$version-source.tar.gz" \
    | sed 's#dist/release/##' > dist/jnt/SHA256SUMS
fi

cp papers/coefficient-mass.tex "dist/arxiv/coefficient-mass-$version.tex"
cp papers/coefficient-mass.pdf "dist/arxiv/coefficient-mass-$version.pdf"
cp submission/arxiv/README.md submission/arxiv/metadata.yml dist/arxiv/

tar -czf "dist/release/coefficient-mass-$version-jnt-submission.tar.gz" \
  -C dist/jnt .
tar -czf "dist/release/coefficient-mass-$version-arxiv-submission.tar.gz" \
  -C dist/arxiv .

checksum_file=dist/release/SHA256SUMS
: > "$checksum_file"
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum dist/release/coefficient-mass-*.tar.gz \
    | sed 's#dist/release/##' >> "$checksum_file"
else
  shasum -a 256 dist/release/coefficient-mass-*.tar.gz \
    | sed 's#dist/release/##' >> "$checksum_file"
fi

echo "built dist/release and dist/jnt for version $version"
