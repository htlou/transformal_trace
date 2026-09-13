# Judging Whether a Translated Formal Repository Still Means the Same Thing

Date: 2026-09-12

## Summary

Our project translates formal repositories from Coq/Rocq and Isabelle into
Lean. A formal repository contains more than theorem statements: it also
contains datatypes, executable functions, typeclasses or locales,
constructors, notations, proofs, and public interfaces. A useful translation
must preserve the behavior and assumptions that users can observe.

Compilation only shows that each repository is internally valid. To decide
whether a Coq or Isabelle declaration and its Lean translation mean the same
thing, we still need to answer:

1. Which Lean input represents each source input?
2. Which source inputs are valid?
3. Which part of the output is observable?
4. Are we comparing one function, or a larger constructor-and-observer API?

Neither compiler knows these cross-language relations. A translation may
therefore compile while changing signed division, serialization, error
behavior, constructor availability, proof relevance, or theorem assumptions.
Our judge reports `aligned`, `not_aligned`, or `uncertain`; unsupported evidence
never silently becomes an `aligned` result.

On a difficult 192-case diagnostic benchmark, the resulting judge was much
more reliable than asking the same model directly:

| Method | Correct, counting abstentions as wrong | Cases with valid evidence | Real mismatches found |
|---|---:|---:|---:|
| Raw LLM | 59.90% | 76.56% | 80.00% |
| Codex agent | 53.65% | 69.27% | 83.33% |
| Transformal judge | **79.17%** | **95.31%** | **93.33%** |

The main conclusion is not that LLMs are poor at formal reasoning. The same
models can be strong proof and implementation generators. The difficulty is
that proof generation starts from a fixed statement, whereas semantic judging
must first discover what the correct comparison should be.

## 1. How the judge works

The judge is best understood as an evidence-producing loop:

```text
translation-provided or judge-extracted metadata
                 ↓
 match declarations and collect relevant context
                 ↓
      LLM writes tests for both languages
                 ↓
 validate the tests and run both native compilers
                 ↓
     accept, repair, reject, or remain uncertain
```

### Step 1: obtain metadata from the compilers or input

In our normal pipeline, the translation stage is expected to provide the judge
with metadata about the source and target declarations. This includes names,
types, dependencies, definition equations, theorem assumptions, proposed
source-target matches, and a small amount of relevant context.

The judge can also recover this metadata on its own when it is used outside the
translation pipeline. It builds and inspects the source and target repositories
through their native compilers, then proposes matches using declaration names,
roles, modules, and compiled interfaces. Proposed matches remain hypotheses,
not evidence that the declarations mean the same thing.

### Step 2: help the LLM search for useful evidence

The current program-synthesis support consists of increasingly strong forms of
extra information around the LLM:

| Layer | What it contributes | Typical failure addressed |
|---|---|---|
| Compiler grounding | Exact types, arguments, dependencies, and interface differences | Comparing the wrong declarations or arguments |
| Symbolic exposure | Reduced Coq terms, Lean equations, and simple branch conditions | Missing behavior hidden behind helper definitions |
| Bounded witness generation | Values near branch boundaries, rounding probes, and typed call skeletons | Missing edge cases or constructing invalid inputs |
| Deterministic validation | Binding, trust, compiler, and observed-output checks | Tests that compile but do not establish the claimed result |
| Diagnostic repair | The failed program and exact compiler error | Incomplete or malformed counterexamples |

These are tools used to support synthesis; Codex itself is not one of the
layers. The current symbolic component is deliberately bounded. It is not a
general symbolic executor or a complete equivalence checker.

### Step 3: require executable evidence from both sides

For an `aligned` answer, the LLM must construct at least three corresponding
examples that agree. For `not_aligned`, it must construct a concrete input that
is valid on both sides and produces observably different results.

Each example must include complete inputs and standalone Coq, Isabelle, and/or
Lean code. A deterministic checker verifies that the code invokes the exact
declaration under review and connects that invocation to the claimed result.
The pipeline then replays the observation using `coqc`, `isabelle build`, or
`lake env lean`.

Compiler success establishes that each observation is valid within its own
formal system. It does not by itself prove that the two inputs represent the
same abstract value. In hierarchical runs, a separate reviewer checks that
cross-language bridge, the relevance of the chosen output, and whether the
finite evidence justifies the verdict.

## 2. How raw LLM and Codex fail

The benchmark contains 192 real source/translation pairs: 162 aligned and 30
not aligned. It is intentionally difficult and includes many earlier judge
failures. Because it is imbalanced, always answering `aligned` would obtain
84.38% accuracy while finding no errors. We therefore emphasize mismatch
recall and verified evidence, not accuracy alone.

The raw baseline received a compact textual view and no tools. The Codex
baseline had an agent interface, but its sandbox did not contain the actual
repositories or theorem provers. It therefore measures agent-style reasoning,
not a fully repository-enabled Codex run. Both used the same `gpt-5.6-sol`
model and demonstrations as the Transformal comparison.

Three cases show why direct judging is brittle.

### Wrong input relation

The Coq function `FLT_exp` takes `(emin, precision, exponent)`, while Lean
takes `(precision, emin, exponent)`. Raw LLM and Codex passed the same
positional tuple to both programs, obtained different numbers, and confidently
reported a mismatch. Their arithmetic was correct; the compared inputs were
not the same abstract input. The judge used compiler-visible argument roles
and tested the reordered values. The [evidence appendix](failure-case-evidence.md#flt-exp)
contains the complete compared code and both baseline outputs.

### Wrong observable result

For `round_N_ge_midp`, raw LLM and Codex found an input where a helper function
returns different integers. However, the theorem under review only states a
lower-bound property, and that property remains true on both sides. The models
found a real difference, but not a difference observable through the judged
theorem. The evidence validator prevented this from becoming a certified
counterexample. The [evidence appendix](failure-case-evidence.md#round-n-ge-midp)
shows the helper and theorem code, verbatim outputs, and validation result.

### Missing repository context

For `showTokenState`, the compact prompt omitted the source renderer and map
printing definitions, so raw LLM and sandboxed Codex abstained. With repository
and compiler access, the judge produced the actual difference:

```text
Coq:  State{total_supply: 0, balances: [], allowances: []}
Lean: State{total_supply: 0, balances: {}, allowances: {}}
```

This was not solved by more fluent reasoning. It was solved by making the
relevant program executable. The [evidence appendix](failure-case-evidence.md#show-token-state)
contains the supplied code, missing repository definitions, both baseline
outputs, and the compiler-checked counterexample.

Repeated sampling did not repair these problems. On a 58-case subset, three
raw-model passes produced the same verdict in 45 cases and were unanimously
wrong in 21. Majority voting remained at 48.28%. Every definitive raw or Codex
error in the full benchmark carried reported confidence of at least 0.98.
These are stable semantic-policy errors, not mainly random mistakes.

## 3. Why proof generation can succeed while semantic judging fails

Proof and implementation generation start from a fixed, machine-checkable
goal. Compiler errors provide immediate local feedback, allowing the model to
repair its work. Semantic judging must instead infer the cross-language
specification: which inputs correspond, what output is observable, and which
interface must be preserved. A wrong relation can still produce two compiling
repositories, so neither compiler exposes the mistake.

Target-language simplifications deepen the problem: replacing a rich Coq
structure with a simpler Lean proposition may make proofs easier while erasing
data or proof-relevant information. Moreover, one counterexample can refute
alignment, but a few agreeing examples cannot prove it. Successful generation
therefore validates the Lean artifact, not its fidelity to the source.

## 4. What happened on translated repositories?

We manually audited 1,282 declarations across five translated repositories.
“Semantic alignment” asks whether their statements and behavior were
preserved. “Strict acceptance” additionally requires preservation of properties
such as constructive proof closure and opacity.

| Repository | Semantic alignment | Strict acceptance | Judge agreement with audit |
|---|---:|---:|---:|
| Coq-SKI | 257/257 | 215/257 | 257/257 |
| Weak-Up-To | 194/194 | 194/194 | 194/194 |
| KA-FMP | 204/313 | 175/313 | 312/313 |
| Coinduction | 190/287 | 181/287 | 285/287 |
| UniMath Computability | 186/231 | 158/231 | 191/231 |
| **Total** | **80.42%** | **72.00%** | **96.65%** |

The easy repositories translated faithfully. KA-FMP and Coinduction stopped
on unresolved extraction or namespace problems instead of inventing missing
content, so absent declarations reduce their scores.

UniMath is the important warning. All 15 generated modules built and passed
their tests, but manual review found 45 losses involving data-bearing
propositions, identity paths, and higher-order embeddings. The historical
judge caught only five of those losses. In other words, build success was
excellent evidence that the Lean repository was internally valid, but poor
evidence that its foundational semantics were unchanged.

The aggregate 96.65% judge agreement is also easier than it appears because
most items were aligned or obviously absent. Performance on UniMath shows that
foundational representation changes remain the main open problem.

## 5. Conclusion

LLMs are useful components of a semantic judge, but unreliable final
authorities. Their strength is synthesizing proofs, programs, and candidate
counterexamples once the comparison has been made explicit. Their weakness is
selecting that comparison across two different formal systems.

Our judge improves reliability by turning semantic claims into replayable,
compiler-checked evidence and by refusing unsupported conclusions. Its best
outputs are concrete counterexamples and clearly localized questions about
input bridges or observable behavior. It is not yet a general proof of
cross-prover equivalence.

The reported 192-case comparison evaluates judge v24; the current
implementation is v27 and still needs a full same-protocol rerun. The benchmark
is a deliberately skewed diagnostic set, not an estimate for all formal
repositories.

## Evidence

- [Complete code and raw outputs for the three examples](failure-case-evidence.md)
- [Complete 192-case comparison](reports/benchmark-192.md)
- [Five-repository translation audit](reports/five-repository-translation-audit.md)
- [Current judge implementation snapshot](implementation/judge-v27.py)
