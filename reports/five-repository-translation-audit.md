# Pipeline-fixed five-repository evaluation

Date: 2026-08-02 (America/Los_Angeles)

## Outcome

The mechanical Lean declaration-discovery fix removed the earlier
`irreducible_def`/declaration-kind failure: all five experiments reached a
terminal translation and judge state without manual edits or restarts. It did
not, however, make the full pipeline semantically reliable. Coq-SKI and
Weak-Up-To translated all indexed declarations; KA-FMP and Coinduction stopped
safely on source-extraction/namespace blockers; UniMath compiled completely but
lost proof-relevant hProp, identity-path, and HoTT-embedding semantics in 45
indexed declarations. The judge substantially overestimated UniMath alignment.

All runs started in separate tmux sessions within the same second at
2026-08-01 20:04:57--20:04:58 PDT. Every translation and matched judge call
used ChatGPT subscription authentication (`codex_subscription` /
`subscription_cli`), GPT-5.6 Sol, and `high` reasoning. No raw API call was
used.

## Requested scores

The denominator is each run's frozen Coq source index. This avoids target-side
test/helper inventory contamination. "Judge translation" is the generated
report's conservative aligned-source score. "Manual translation" is semantic
source-to-Lean alignment, allowing justified library-aware equivalence but not
missing items or foundational erasure. "Manual judge" is semantic
classification accuracy over source items; schema/evidence defects are
reported separately below.

| Repository | Judge translation | Manual translation | Manual judge | Translation state |
|---|---:|---:|---:|---|
| Coq-SKI | **100.0000% (257/257)** | **100.0000% (257/257)** | **100.0000% (257/257)** | 8/8 modules; full build/test pass |
| Weak-Up-To | **100.0000% (194/194)** | **100.0000% (194/194)** | **100.0000% (194/194)** | 10/10 modules; full build/test pass |
| KA-FMP | **65.4952% (205/313)** | **65.1757% (204/313)** | **99.6805% (312/313)** | 7/13 modules; root placeholder build passes, full test fails |
| Coinduction | **65.5052% (188/287)** | **66.2021% (190/287)** | **99.3031% (285/287)** | 3/4 scopes; root placeholder build passes, full test fails |
| UniMath Computability | **97.8355% (226/231)** | **80.5195% (186/231)** | **82.6840% (191/231)** | 15/15 modules; full build/test pass |

Micro-aggregated over the 1,282 indexed source declarations, the three columns
are respectively 83.4633% (1070/1282), 80.4212% (1031/1282), and 96.6459%
(1239/1282). The high aggregate judge accuracy is dominated by easy aligned or
obviously missing items; UniMath is the discriminating semantic-audit case.

## Secondary strict translation score

This stricter measure additionally requires compilation, source-faithful
opacity, direct/provenance closure where no explicit bridge exists, and no
`Classical.choice` dependency stronger than the constructive Coq source.

| Repository | Strict accepted |
|---|---:|
| Coq-SKI | 83.6576% (215/257) |
| Weak-Up-To | 100.0000% (194/194) |
| KA-FMP | 55.9105% (175/313) |
| Coinduction | 63.0662% (181/287) |
| UniMath Computability | 68.3983% (158/231) |

The strict aggregate is 71.9969% (923/1282). This is separate from statement
semantics so a proof-engineering defect is not mislabeled as a specification
defect.

## Run and coverage evidence

| Repository | Pinned source commit | Translation calls / time | Judge LLM calls / time |
|---|---|---:|---:|
| Coq-SKI | `ef866785105d463e771a16e576faf940e832e91b` | 49 / 2h49m | 257 / 1h34m |
| Weak-Up-To | `6780e1d43bc9583d5e6fe47418980d4dbc8f6527` | 58 / 3h28m | 194 / 1h24m |
| KA-FMP | `d315501d045b3deaecfa8ea450c85deaa5b355fc` | 54 / 4h10m | 207 / 1h35m |
| Coinduction | `81ecd5f1ffa3e46b696d9461c88ad6ca9be5cfc7` | 26 / 2h27m | 198 / 1h42m |
| UniMath Computability | `cad09ce477a2b94595554dc308e9a66d208853bd` | 112 / 5h48m | 231 / 1h46m |

All generated Lean candidates remained unchanged after their recorded
translation completion. Repository-wide forbidden-token scans found no
`sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by` in candidate source.
The post-run pipeline regression suite passes all 54 tests.

## Translation audit

### Coq-SKI

All 257 indexed definitions and theorem statements align. The statement-first
stage correctly caught and repaired the initially invented binder in
`is_const_nxt`. The main non-semantic shortcomings are source opacity/notation
API loss and 42 constructive source theorems whose Lean closure reaches
`Classical.choice`; these account for the lower strict score.

### Weak-Up-To

All 194 indexed items align and compile constructively. The statement-first
stage correctly removed a spurious Section hypothesis from
`wmonotonic_correct_t`. Coq coercion annotations are not reproduced, and the
target judge inventory includes test fixtures, but neither changes the 194
source-item semantic score.

### KA-FMP

Only 206 indexed items received direct target declarations; six scopes remain
blocked after the extractor omitted the core `Equations compute_solution_nat`
definition. The full test fails on the absent `KaFmpProofs.ModuleTests.Solve`
module. Of the directly translated items, two are semantically wrong:

- Coq `Record monotone ... := ...` has no sort annotation and is Type-valued;
  Lean declares `structure monotone ... : Prop`, erasing its data/elimination
  surface.
- `matrix_iterate_monotone` inherits that Type-to-Prop defect.

The judge catches `monotone` but marks `matrix_iterate_monotone` aligned, so it
overstates alignment by one. It also correctly rejects a spurious mechanical
match from `term_matches_step` to an unrelated star/repetition theorem, but the
verdict is schema-invalid because the prompt permits `wrong_match` with
`not_aligned` while the validator forbids it.

The official denominator also misses 27 `Equations` declarations and several
instances/morphism registrations, so 204/313 is not a claim that 65% of every
source command was reproduced.

### Coinduction

The lattice, tower/relations, and mathematical tactics declarations translate;
the 106-item companion scope is blocked. The extractor records aborted `Ct`
and `Cflat` drafts, drops module paths, and the planned Lean namespace flattens
distinct `tower.gfp` and `companion.gfp` families. Refusing to fabricate this
scope is correct pipeline behavior. The full test fails on the absent
`CoinductionFull.ModuleTests.Companion` module.

Manual semantic credit is 181 direct items plus nine library-aware equivalent
Tower results, or 190/287. The judge accepts seven of those reuses but rejects
the equivalent `gfp_pfp` and `gfp_fp` items despite citing the source
`gfp_tower` bridge and admitting there is no proposition-level counterexample.
Hence 285/287 semantic classification accuracy. Ten useful wrong-match
diagnoses are schema-invalid and disappear from the final report; the source's
plugin registrations and exported tactic interface are also not translated.

### UniMath Computability

All 15 planned modules and 231 indexed items compile and the aggregate tests
pass, but compilation hides a foundational semantic gap. The run repeatedly
maps UniMath `hProp` carriers to Lean `Prop`, proof-relevant identity data to
proof-irrelevant Lean equality (sometimes merely wrapped in `PLift`), and HoTT
`incl`/embedding structure to point injectivity. This is acceptable only for
items used purely logically or already propositionally truncated. It is not
faithful when public inputs/results expose witnesses, paths, or embeddings.

The 45-item manual truth set consists of:

- 1 option/path item;
- 6 generic injectivity/path-equivalence items;
- 1 decidable fiber item;
- 8 dependent hProp-decision items;
- 10 list membership/path-witness items;
- 8 stability/double-negation items;
- 8 one-one/HoTT-embedding items; and
- 3 Myhill correspondence path-data items.

Concrete witnesses include:

- `DNEG_ELIM`: the source contract accepts a subsingleton data carrier such as
  `Unit`; the target requires `P : Prop`, so the same application is ill-typed.
- `isdeceq_isdecsurj`: a positive source decision contains a concrete `stn 2`
  fiber index; the target's `Decidable (Exists ...)` proof cannot eliminate
  that witness into data.
- `oneonereduction`: the constant map `Unit -> Type` landing at `Bool` is
  point-injective in Lean but not a UniMath `incl` under univalence, because
  Bool has the identity and negation loops.
- `is_in`/Myhill correspondence: source universe-level identity and negation
  paths remain distinguishable; Lean `Eq` plus `PLift` is subsingleton.

The judge's terminal confusion matrix is TP 5, TN 186, FP 0, FN 40. It has
100% mismatch precision (5/5) but only 11.1111% mismatch recall (5/45). The five
correct detections are `is_in`, `isdeceq_isdecsurj`, `oneonereduction`,
`corr_prop2`, and `corr_prop3`. All claim counterexamples, but none contains an
executable Coq test; three target-only Lean probes are compiler-verified and two
are narrative-only. Independent manual source/target-model probes validate the
fiber, hProp decision, and double-negation erasure families.

## Judge implementation audit

| Repository | Schema-valid jobs | Claimed counterexamples | At least target/compiler-verified |
|---|---:|---:|---:|
| Coq-SKI | 100.0000% (258/258) | 0 | 0 |
| Weak-Up-To | 100.0000% (266/266) | 0 | 0 |
| KA-FMP | 99.8165% (544/545) | 1 | 1 |
| Coinduction | 96.8750% (310/320) | 0 | 0 |
| UniMath Computability | 100.0000% (340/340) | 5 | 3 |

This table is artifact/schema quality over every planned job, not semantic
source-item accuracy. In particular, deterministic unmatched jobs validate
even when they carry the wrong failure category and no absence witness.

- Canonical source denominator: correct and complete for the frozen indexes.
- Target inventory: not benchmark-ready. UniMath has 109 target-only jobs: 77
  test-fixture declarations, 15 Proof-layer declarations, and 17 Spec-layer
  declarations. Weak-Up-To has the same contamination pattern.
- Unmatched handling: deterministic and reproducible, but uses the backwards
  `missing_source_item` category for a present source with a missing target and
  supplies no executable absence witness.
- Wrong-match contract: inconsistent. The prompt permits
  `wrong_match/not_aligned` with a witness, while validation requires every
  wrong match to use `not_judged`. This discards one KA-FMP and ten Coinduction
  semantic diagnoses.
- Counterexamples: useful as audit leads, but the environment lacks a Coq/Rocq
  executable checker. Cross-system counterexamples are therefore not yet
  mechanically established end to end.
- Foundational policy: absent. The judge commonly declares hProp/Prop,
  `PLift Eq`, and HoTT-incl/point-injectivity changes aligned without demanding
  a bridge theorem or an elimination-surface check.
- Completion checks: lexical forbidden-token scans are insufficient. They miss
  transitive `Classical.choice`, source `Qed` opacity, and no-op repair rounds.

## Recommended fixes

1. Extract the elaborated Coq environment, not only lexical commands: include
   `Equations`, Program/Global instances, canonical structures, module paths,
   `Abort` semantics, coercions, opacity, and exported tactic/plugin surfaces.
2. Freeze an explicit per-repository representation policy before translation.
   Every foundation-changing mapping must carry a checked equivalence/refinement
   lemma and an allowed-elimination contract; otherwise statement review fails.
3. Index one canonical target declaration layer and exclude `ModuleTests`,
   duplicate Spec/Proof wrappers, and private helpers from translation scoring.
4. Make prompt, schema, validator, and report aggregation agree on wrong matches
   and missing-target categories; add deterministic compile/name-absence
   witnesses.
5. Persist completion findings as mechanical retry obligations, and require
   file/hash changes or an explicit proof that no change is needed before a
   later reviewer can clear them.
6. Run `#print axioms` (or equivalent environment inspection) for every public
   declaration and compare source/target opacity and trusted closure.

## Artifacts

- Detailed manual audit: `pipeline/runs/pipeline-fixed-20260801-manual-audit.md`
- UniMath semantic truth set:
  `pipeline/runs/unimath-computability-pipeline-fixed-20260801/manual/semantic-gap-truth-set.tsv`
- Per-repository generated reports:
  `pipeline/runs/<repository>-pipeline-fixed-20260801/artifacts/judge-report.md`
- Translation metadata:
  `pipeline/runs/<repository>-pipeline-fixed-20260801/translation/translation-run.json`
