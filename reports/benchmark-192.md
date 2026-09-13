# Hard-organic-192: three-method fresh rerun and failure audit

Date: 2026-09-06 (America/Los_Angeles)

## Executive result

All three methods were freshly run with Codex subscription on the full frozen 192-case suite. `aligned` is treated as the positive class; abstentions and invalid evidence count as wrong in strict accuracy.

| Method | TP / TN / FP / FN | Abstain / invalid | Strict accuracy | Coverage | Selective accuracy | Balanced recall |
|---|---:|---:|---:|---:|---:|---:|
| Raw LLM, no tools | 91 / 24 / 4 / 28 | 45 / 0 | 115/192 = **59.90%** | 76.56% | 78.23% | 68.09% |
| Codex agent | 78 / 25 / 3 / 27 | 59 / 0 | 103/192 = **53.65%** | 69.27% | 77.44% | 65.74% |
| Transformal judge v24 | 124 / 28 / 1 / 30 | 0 / 9 | 152/192 = **79.17%** | 95.31% | 83.06% | **84.94%** |

| Method | `aligned` precision / recall | `not_aligned` precision / recall |
|---|---:|---:|
| Raw LLM | 95.79% / 56.17% | 46.15% / 80.00% |
| Codex agent | 96.30% / 48.15% | 48.08% / 83.33% |
| Transformal judge v24 | **99.20%** / **76.54%** | **48.28%** / **93.33%** |

This is a deliberately skewed diagnostic challenge set: 162 aligned and 30 not-aligned cases, including 133 retained historical false-positive challenges. The trivial always-`aligned` rule therefore gets 84.38% strict accuracy but only 50% balanced recall and detects no mismatch. Strict accuracy alone is misleading here; the useful findings are v24's 93.33% mismatch recall, 99.20% acceptance precision, and 95.31% evidence coverage.

The raw score did **not** remain below 40% after few-shot prompting; the honest fresh result is 59.90%. This benchmark supports the claim that direct judging is brittle, not a claim that the underlying model has low general capability.

## Controlled protocol and integrity

- Frozen suite: [`hard-organic-192-v1.0.0`](../data/suites/hard-organic-192-v1.0.0/manifest.json), 192 unique organic source/translation pairs, 184 Coq and 8 Isabelle, with ground truth hidden during inference.
- Raw and Codex used the same `gpt-5.6-sol`, `high` effort, and the same six demonstrations. Raw disabled all tools. Codex enabled its agent tools.
- Raw used the suite's `raw-view` projection because the direct CLI has a request-size ceiling. All 192 case IDs, labels, `source.item`, and `target.item` objects match the canonical suite exactly, but dependency context was compacted. This is a real input-view confound and must be disclosed.
- The Codex runner's blind sandbox exposes only the temporary case directory as source, target, and work root ([runner lines 539–549](../tools/run_eval.py#L539)). Thus “tools enabled” did **not** give Codex the actual repositories or Coq/Lean/Isabelle compilers. It is an agent-format baseline, not a test of full repository-enabled Codex.
- Transformal v24 used the canonical payloads, pinned repository states, source and target compilers, evidence repair, and fail-closed evidence validation. All 183 definitive outputs have compiler-verified observation chains; nine proposed outputs were rejected as invalid.
- The four v24 shards contain exactly the canonical 192 IDs with exact payload hashes. No case is missing or duplicated.

Run artifacts:

- [Raw full run](../eval_runs/raw-gpt56sol-high-hard-organic-192-rawview-full-fewshot-rerun-20260906/score.md)
- [Codex full run](../eval_runs/codex-agent-gpt56sol-high-hard-organic-192-full-fewshot-rerun-20260906/score.md)
- Transformal v24: [shard 1](../eval_runs/ours-v24-full192-shard01-20260906/score.md), [shard 2](../eval_runs/ours-v24-full192-shard02-20260906/score.md), [shard 3](../eval_runs/ours-v24-full192-shard03-20260906/score.md), [shard 4](../eval_runs/ours-v24-full192-shard04-20260906/score.md)

## Raw-LLM pass@3 experiment

The frozen subset contains 58/192 cases (30.21%), selected once with seed `20260904`: 51 aligned, seven not aligned, 56 Coq, and two Isabelle. Pass 1 reuses the fresh full run; passes 2 and 3 are independent fresh subscription calls with the same prompt and demonstrations.

| Evaluation | Correct | Accuracy |
|---|---:|---:|
| Pass 1 | 28/58 | 48.28% |
| Pass 2 | 30/58 | 51.72% |
| Pass 3 | 27/58 | 46.55% |
| Oracle pass@2 | 32/58 | 55.17% |
| Oracle pass@3 | 33/58 | **56.90%** |
| Majority@3 | 28/58 | **48.28%** |

The important stability statistics are:

- 45/58 (77.59%) returned the same verdict on all three passes.
- 21/58 (36.21%) were unanimously wrong.
- 25/58 (43.10%) were wrong on all three passes, including four whose wrong outputs varied.
- On the 51 aligned cases, oracle pass@3 solved only 29; 22 remained wrong on every pass.
- On the seven mismatches, all three individual passes got four correct, and oracle pass@3 still got only four.

Therefore the failure is mostly systematic, not unlucky decoding. Oracle pass@3 is also retrospective and non-deployable; majority voting gave no gain. Passes 4–5 were not run because pass@3 already answered the stated question while avoiding 116 additional calls.

Subset and run artifacts:

- [Frozen subset](hard-organic-192-few-shot-pilot-selection-v1.json)
- [Pass 2](../eval_runs/raw-pass5-pilot30-pass02-20260906/run.json)
- [Pass 3](../eval_runs/raw-pass5-pilot30-pass03-20260906/run.json)

## Why a strong prover/coder still fails as judge

The bottleneck is usually **choosing and validating the cross-language semantic relation**, not performing the calculation after that relation is fixed. Proving skill answers “does this proposition follow under this encoding?” Judging must first answer harder specification questions: which binders correspond, which representation fields are observable, whether an interface is an input or an output space, and whether a helper-level difference can change the judged item's contract.

Four observations support this explanation:

1. Raw and Codex agree on 161/192 predictions (83.85%). Raw alone is correct on 19 cases and Codex alone on seven; exact paired McNemar gives `p ≈ 0.029`. Codex is worse mainly because it abstains more (59 vs. 45), not because it makes more definitive mistakes (30 vs. 32).
2. Every decisive raw error (32/32) and Codex error (30/30) has reported confidence at least 0.98. More internal confidence is not the missing component.
3. The agent baseline cannot reach the actual repositories or compilers. Tool-use skill is therefore largely inert in this setup.
4. v24 beats raw on 45 paired cases and Codex on 57, while each baseline beats v24 on only eight. The gain comes from repository closure, explicit bridge/observer obligations, two-sided compiler replay, and fail-closed validation—not from a different base model.

### Evidence A — correct arithmetic, wrong input bridge: `FLT_exp`

Case: `screen-f1b5484047633cfe08dd`, official label `aligned`.

- Coq exports `(emin, prec, e)` and computes `max (e - prec) emin`.
- Lean exports `(prec, emin, e)` and computes the same formula.
- Raw compares the same positional triple `(2,3,10)` and reports `7` versus `8`; Codex similarly compares `(0,10,5)` positionally and reports `0` versus `10`.
- Those are not the same abstract inputs. The role-preserving bridge is `(emin,prec,e) ↦ (prec,emin,e)`.
- v24 compiler-replayed three role-aligned points, including Coq `(-10,3,5)` and Lean `(3,-10,5)`, both producing `2`, and accepted the translation.

This is not an inability to calculate `max`; both baselines calculate it correctly. They chose the wrong correspondence before calculating. Full proof harnesses are in the [v24 result](../eval_runs/ours-v24-full192-shard01-20260906/pipeline_workspaces/pipeline-runs-flocq-current-floatspec-subscription-20260808/judge/results/screen-f1b5484047633cfe08dd.json).

### Evidence B — correct helper difference, wrong semantic observer: `round_N_ge_midp`

Case: `screen-2adaa56d24408d354e80`, official label `aligned`.

Raw and Codex correctly notice that, at a tie with `choice = false`, the Coq helper rounds `1/2` to `0` while the Lean helper chooses `1`. Raw then explicitly says that “both values happen to satisfy the theorem's lower-bound conclusion” but still emits `not_aligned`.

The judged theorem observes the proposition `u ≤ rounded(v)`. At the proposed input, both instantiated conclusions are true, so the helper difference is not a counterexample to this theorem. v24 initially made the same semantic-relevance mistake, but the evidence gate rejected the target observation chain; the case became `invalid`, not a certified rejection. This cleanly separates LLM proposal quality from evidence validation. See the [full attempted counterexample and validator output](../eval_runs/ours-v24-full192-shard01-20260906/pipeline_workspaces/pipeline-runs-flocq-current-floatspec-subscription-20260808/judge/results/screen-2adaa56d24408d354e80.json).

### Evidence C — insufficient static closure, not insufficient reasoning: `showTokenState`

Case: `judge-3e5eaf1b07793615dc02`, official label `not_aligned`.

Raw and Codex both abstain because the supplied static closure omits the concrete source `Show` and finite-map renderer bodies. With repository access, v24 compiles the same empty state on both sides:

```text
Coq: State{total_supply: 0, balances: [], allowances: []}
Lean: State{total_supply: 0, balances: {}, allowances: {}}
```

This is a valid behavioral counterexample. The difference is access to the semantic oracle, not theorem-proving ability. Full two-sided programs are in the [v24 result](../eval_runs/ours-v24-full192-shard03-20260906/pipeline_workspaces/pipeline-runs-judge-v12-executed-eip20-r2-20260816/judge/results/judge-3e5eaf1b07793615dc02.json).

### Evidence D — stable observer-policy error across pass@3: `Bone`

Case: `screen-07b849a573d12de5cc22`, official label `aligned`.

All three raw passes return `not_aligned` at confidence 1.0 or effectively 1.0. They compute that Coq can expose finite payload `(false,2,-1)` while Lean exposes `(false,1,0)`, and they also explicitly recognize that both denote the real number `1`. Repeated sampling does not change which observer they privilege.

This case is useful but **policy-disputed**: under the benchmark's real-value/proof-erasure observer it is a false rejection; if raw constructor fields are part of the promised public API, it should be relabeled. It demonstrates that the hard question is observer choice, not computation, and it belongs in the manual re-adjudication queue rather than serving as a universal proof of model error.

### Evidence E — interface direction error: `poly_carrier`

Case: `judge-0968b0eb95a3c543e7c1`, official label `not_aligned`.

Raw and Codex both accept it by calling Lean's extra trivial-semiring inhabitants a harmless “target-domain extension.” But the judged artifact is a class/interface declaration: its inhabitants are semantic outputs of the declaration, not merely extra inputs to a total function. Isabelle inherits `zero_neq_one`; Lean constructs `poly_carrier PUnit`, where zero equals one. v24 replayed the Isabelle rejection and Lean construction and correctly rejected the translation. See the [compiler-backed result](../eval_runs/ours-v24-full192-shard04-20260906/pipeline_workspaces/pipeline-runs-isabelle-abstract-rewriting-judge-calibrated-v11-final-20260813/judge/results/judge-0968b0eb95a3c543e7c1.json).

## Failure modes by method

### Raw LLM

- **45 abstentions:** predominantly missing closure/bridge or inability to establish a universal relation from the payload.
- **28 false rejections:** positional instead of semantic binder matching; raw-representation observers used where the benchmark expects a quotient/value observer; helper-level differences treated as theorem-level divergence; added proof/typeclass packaging treated as a source-domain loss.
- **4 false acceptances:** interface/output-space extensions treated as harmless target input extensions (`poly_carrier`, `iffT` through its `equiv_data` carrier, `Fbound`, and `FLX_format`).
- **Calibration failure:** all 32 decisive errors have confidence 0.98–1.0.

### Codex agent

- **59 abstentions:** 14 more than raw; this explains most of its lower strict score.
- **27 false rejections and three false acceptances:** largely the same bridge/observer errors as raw; 23 of the false rejections overlap raw's false rejections.
- **Tools did not help:** the sandbox contained only the case payload, not the actual repositories/compiler environments.
- **Calibration failure:** all 30 decisive errors have confidence 0.98–1.0.

### Transformal v24

- **30 official false rejections:** compiler-valid facts were sometimes attached to the wrong observer. Example: `boundRrOpp` proves symmetry on both sides, while v24 rejects because the internal `boundR 0` representations differ. Compilation validates each fact but cannot by itself decide whether that subterm is the intended semantic observer.
- **1 false acceptance:** `iffT` through its `equiv_data` carrier (`Type` versus `Sort`) remains an interface-policy miss.
- **9 invalid/fail-closed cases:** three proposed counterexamples had a rejected/contradicted side; two aligned-example groups failed an overly rigid target input-expression binding check; two EIP20 example groups failed their source harnesses; one model response remained `uncertain`; one call produced no final verdict.
- **Evidence gate value:** one of the three rejected counterexamples is a true mismatch, so fail-closed validation loses recall, but the other two prevent unsupported false rejections from becoming certified verdicts.

## Ground-truth audit warning

The table above uses the frozen official labels; no label was changed after seeing these runs. Fresh two-sided compiler evidence nevertheless contradicts at least four positive labels and they should be manually re-adjudicated before publication:

| Case | Frozen label | Fresh compiler evidence |
|---|---|---|
| `screen-1e45cd153620e1e8d15b` (`Zdiv_eucl_unique`) | aligned | On `(7,-3)`, Coq produces `(-3,-2)` and Lean produces `(-2,1)` because their signed division conventions differ. |
| `screen-d9c0c6d6b2f0a3bd5989` (`Fsqrt_correct`) | aligned | The actual Coq export accepts arbitrary `fexp`; Lean publicly requires `[Valid_exp beta fexp]`. |
| `screen-2bdab37ce0ad3fe97154` (`mult_bpow_exact_FLT`) | aligned | The actual Coq export does not generalize `Prec_gt_0`; Lean publicly requires `[Prec_gt_0 prec]`. |
| `screen-355815b19e3537b18377` (`Fmult_correct`) | aligned | Coq exports the theorem under `0 < radix`, admitting radix `1`; Lean requires `1 < beta`. |

These are not silently corrected in the reported score. Several additional v24 disagreements also concern Section-variable export and observer policy, so the 79.17% number is an official-label score, not yet a publication-ready ground-truth estimate.

## Bottom line

The experiment supports a narrower and more defensible claim than “LLMs cannot reason about proofs”:

> A strong code/proof model is not automatically a reliable cross-language semantic judge. On representation-changing repository translations, the dominant failures are bridge selection, observer relevance, incomplete semantic closure, and verdict calibration. Repeated sampling does little because those errors are systematic. Repository-grounded compiler replay and fail-closed evidence validation materially improve certified coverage, but they still require an explicit policy for public interfaces and semantic observers.
