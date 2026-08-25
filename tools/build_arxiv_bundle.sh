#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output_dir="$repo_root/dist"
archive="$output_dir/virasoro-arxiv-v1.tar.gz"
stage="$(mktemp -d)"

cleanup() {
    rm -rf -- "$stage"
}
trap cleanup EXIT HUP INT TERM

mkdir -p "$output_dir" "$stage/anc/tools"

install -m 0644 "$repo_root/paper.tex" "$stage/paper.tex"
install -m 0644 "$repo_root/ARXIV_ANCILLARY_README.md" \
    "$stage/anc/README.md"
install -m 0644 "$repo_root/AUDIT_MANIFEST.md" \
    "$stage/anc/AUDIT_MANIFEST.md"
install -m 0644 "$repo_root/Makefile" "$stage/anc/Makefile"
install -m 0644 "$repo_root/requirements-audit.txt" \
    "$stage/anc/requirements-audit.txt"

for source in \
    audit_confluent_recursion.py \
    audit_direct_principal_parts.py \
    audit_first_resonances.py \
    audit_grade10_confluence.py \
    audit_grade10_direct.py \
    audit_ising_characters.py \
    audit_low_levels.py \
    audit_stocco_comparison.py \
    direct_reconstruction.py \
    exact_shapovalov.py
do
    install -m 0644 "$repo_root/tools/$source" "$stage/anc/tools/$source"
done

tar \
    --sort=name \
    --mtime="2026-08-25 00:00:00 UTC" \
    --owner=0 \
    --group=0 \
    --numeric-owner \
    -czf "$archive" \
    -C "$stage" \
    paper.tex anc

printf 'created %s\n' "$archive"
tar -tzf "$archive"
