# Transformal semantic-judge evidence (2026-09-12)

This directory is the self-contained public evidence bundle accompanying the
Transformal advisor report. It contains only the report, the three discussed
benchmark cases, their raw model traces, and the corresponding judge results.

- [Short advisor report](advisor-report.md)
- [Detailed failure-case appendix](failure-case-evidence.md)
- [Complete 192-case benchmark report](reports/benchmark-192.md)
- [Five-repository translation audit](reports/five-repository-translation-audit.md)
- [Judge v27 implementation snapshot](implementation/judge-v27.py)

For each showcased case, `inputs/` contains the exact compact benchmark input;
`results/raw-llm/`, `results/codex/`, and `results/judge-v24/` contain the
unaltered recorded artifacts. Paths inside those JSON files record the original
evaluation environment and need not exist on another machine.

Original formal-source files are linked at immutable upstream commits from the
appendix. The locally generated EIP-20 Lean printer has no upstream revision,
so its exact snapshot is included under `source-snapshots/`.
