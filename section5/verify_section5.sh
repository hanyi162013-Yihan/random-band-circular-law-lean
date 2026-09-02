#!/usr/bin/env bash
# Local-only sequential validation. Run from this project directory.
set -eu
export LEAN_NUM_THREADS=1

section5_phase="${1:-all}"
section5_log_dir="${2:-$(mktemp -d /tmp/section5-validation.XXXXXX)}"
if [ ! -f lakefile.toml ] || [ ! -f Section5ValidationModules.txt ]; then
  echo 'Run this script from the CircularLawSections56 project directory.' >&2
  exit 2
fi
if [ ! -d "$section5_log_dir" ]; then
  echo 'The supplied log directory does not exist.' >&2
  exit 2
fi
case "$section5_phase" in build|strict|audit|kernel|all) ;; *) exit 2 ;; esac
echo "Section 5 validation phase: $section5_phase; logs: $section5_log_dir"

if [ -n "$(LC_ALL=C sort Section5ValidationModules.txt | uniq -d)" ]; then
  echo 'Duplicate entries in the Section 5 validation manifest.' >&2
  exit 2
fi
while IFS= read -r section5_module || [ -n "$section5_module" ]; do
  [ -n "$section5_module" ] || continue
  if [ ! -f "CircularLawSections56/Section5/$section5_module.lean" ] ||
    ! rg -Fqx "import CircularLawSections56.Section5.$section5_module" CircularLawSections56/Section5.lean; then
    echo "Missing source or umbrella import: $section5_module" >&2
    exit 2
  fi
done < Section5ValidationModules.txt

if [ "$section5_phase" = build ] || [ "$section5_phase" = all ]; then
  lake --no-cache build CircularLawSections56 > "$section5_log_dir/build.log" 2>&1
  echo 'PASS integrated build'
fi

if [ "$section5_phase" = strict ] || [ "$section5_phase" = all ]; then
  section5_failed=0
  while IFS= read -r section5_module || [ -n "$section5_module" ]; do
    [ -n "$section5_module" ] || continue
    if lake --no-cache env lean -DwarningAsError=true \
      "CircularLawSections56/Section5/$section5_module.lean" \
      > "$section5_log_dir/strict-$section5_module.log" 2>&1; then
      echo "PASS strict $section5_module"
    else
      echo "FAIL strict $section5_module"
      sed -n '1,100p' "$section5_log_dir/strict-$section5_module.log"
      section5_failed=1
    fi
  done < Section5ValidationModules.txt
  [ "$section5_failed" = 0 ] || exit 1
fi

if [ "$section5_phase" = audit ] || [ "$section5_phase" = all ]; then
  for section5_check in AxiomAudit FullSection5AxiomAudit Section5Regression; do
    lake --no-cache env lean -DwarningAsError=true "$section5_check.lean" \
      > "$section5_log_dir/$section5_check.log" 2>&1
    echo "PASS $section5_check"
  done
fi

if [ "$section5_phase" = kernel ] || [ "$section5_phase" = all ]; then
  # One worker, one process, no --fresh: reuse imported dependencies and replay
  # every declaration in every Section 5 module, including private declarations.
  if ! lake --no-cache env leanchecker --verbose CircularLawSections56.Section5 \
    > "$section5_log_dir/kernel-all.log" 2>&1; then
    echo 'FAIL kernel replay'
    tail -100 "$section5_log_dir/kernel-all.log"
    exit 1
  fi
  # A replaying line is not a success by itself; this coverage check is reached
  # only after the checker has returned exit status zero.
  section5_expected=1
  if ! rg -Fqx 'replaying CircularLawSections56.Section5' "$section5_log_dir/kernel-all.log"; then
    echo 'FAIL kernel coverage: missing Section 5 umbrella'
    exit 1
  fi
  while IFS= read -r section5_path; do
    section5_module="${section5_path%.lean}"
    section5_module="${section5_module//\//.}"
    if ! rg -Fqx "replaying $section5_module" "$section5_log_dir/kernel-all.log"; then
      echo "FAIL kernel coverage: missing $section5_module"
      exit 1
    fi
    section5_expected=$((section5_expected + 1))
  done < <(rg --files CircularLawSections56/Section5 -g '*.lean' | LC_ALL=C sort)
  section5_replayed="$(rg -c '^replaying ' "$section5_log_dir/kernel-all.log" || true)"
  if [ "${section5_replayed:-0}" -ne "$section5_expected" ]; then
    echo "FAIL kernel coverage: expected $section5_expected modules, saw ${section5_replayed:-0}"
    exit 1
  fi
  echo "PASS kernel replay: $section5_expected modules; exact source/umbrella coverage"
fi
