# Evidence Appendix: Three LLM Semantic-Judging Failures

Date: 2026-09-12

This appendix supports the three failure examples in
the [short advisor report](advisor-report.md).
For each case, it records:

- the complete declaration under judgment;
- the helper code needed to understand the disputed behavior;
- the exact `raw_output` returned by the raw-LLM and Codex baselines;
- the correct interpretation and the evidence produced by judge v24.

“Complete code” here means the complete compared declaration and the directly
relevant definitions, not every imported library in either repository. The
linked frozen case JSON contains the entire benchmark payload supplied to the
models.

The two baselines used the same `gpt-5.6-sol` model at high reasoning effort
with the same six demonstrations. “Raw LLM” had no tools. “Codex” ran in a
temporary blind sandbox containing the case payload, but not the real
repositories or theorem provers.

## FLT-exp

Case ID: `screen-f1b5484047633cfe08dd`

Official label: `aligned`

Artifacts:

- [Frozen model input](inputs/screen-f1b5484047633cfe08dd.json)
- [Raw-LLM result](results/raw-llm/screen-f1b5484047633cfe08dd.json)
- [Codex result](results/codex/screen-f1b5484047633cfe08dd.json)
- [Judge v24 result and compiler replays](results/judge-v24/screen-f1b5484047633cfe08dd.json)

### Source code: Coq

The declaration occurs inside a section. The compiler exports the argument
order `(emin, prec, e)`; `beta` and the precision proof do not occur in the
definition's exported type.

```coq
Section RND_FLT.

Variable beta : radix.
Variable emin prec : Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Definition FLT_exp e := Z.max (e - prec) emin.
```

Source: [FLoCq `Core/FLT.v` at the evaluated commit](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/FLT.v#L41)

### Target code: Lean

The Lean core definition binds the contextual values in the order
`(prec, emin)`, so its exported order is `(prec, emin, e)`.

```lean
namespace FloatSpec.Core.FLT

variable (prec emin : Int) [Prec_gt_0 prec]

def FLT_exp (e : Int) : Int :=
  max (e - prec) emin
```

The compatibility API makes the intended role-preserving reordering explicit:

```lean
abbrev FLT_exp (emin prec : Int) : Int → Int :=
  FloatSpec.Core.FLT.FLT_exp prec emin
```

Sources: [FloatSpec `Core/FLT.lean`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/67b5ab23d63593497379e028c48d0ef693d59bb5/FloatSpec/src/Core/FLT.lean#L43)
and [`Compat.lean`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/67b5ab23d63593497379e028c48d0ef693d59bb5/FloatSpec/src/Compat.lean#L55)

### Raw-LLM output

```json
{"alignment":"not_aligned","confidence":0.99,"rationale":"The exponent formula is the same only after swapping the two captured integer parameters. The Coq section declares `emin` before `prec`, giving the public order `emin → prec → e`, while the Lean core definition has order `prec → emin → e`, as confirmed by the compatibility wrapper `FLT_exp (emin prec) := FloatSpec.Core.FLT.FLT_exp prec emin`. Thus the functions differ when applied positionally; for example, arguments `(1, 2, 10)` yield `max (10 - 2) 1 = 8` in the source but `max (10 - 1) 2 = 9` in the target.","differences":["The `emin` and `prec` public binders are reversed in the target interface."]}
```

### Codex output

```json
{"alignment":"not_aligned","confidence":0.99,"rationale":"The exponent calculation is the same only after swapping the first two integer parameters. Coq section generalization gives the source interface `FLT_exp emin prec e = max (e - prec) emin`, while the target Core definition takes those contextual parameters as `prec` then `emin`, as confirmed by the compatibility wrapper `FLT_exp emin prec := FloatSpec.Core.FLT.FLT_exp prec emin`. Therefore direct applications of the compared declarations can differ; for example, arguments `(1, 2, 3)` yield `1` in the source but `2` in the target.","differences":["The `emin` and `prec` binders occur in opposite orders in the source and target interfaces."]}
```

### Why both answers are wrong

Both models correctly read the formulas and correctly perform the arithmetic.
Their error is treating argument position as the semantic relation. The source
and target inputs must be matched by role:

```text
Coq  (emin, prec, e)  ↦  Lean (prec, emin, e)
```

Judge v24 compiled three role-aligned examples below, at, and above the
`e - prec = emin` boundary. For example:

```text
Coq:  FLT_exp (-10) 3 5 = 2
Lean: FLT_exp 3 (-10) 5 = 2
```

All six proof harnesses passed. The judge returned `aligned` with confidence
0.99.

## Round-N-ge-midp

Case ID: `screen-2adaa56d24408d354e80`

Official label: `aligned`

Artifacts:

- [Frozen model input](inputs/screen-2adaa56d24408d354e80.json)
- [Raw-LLM result](results/raw-llm/screen-2adaa56d24408d354e80.json)
- [Codex result](results/codex/screen-2adaa56d24408d354e80.json)
- [Judge v24 attempted counterexample and validation result](results/judge-v24/screen-2adaa56d24408d354e80.json)

### Source code: Coq

The frozen payload supplied the theorem statement and its section context, but
not its proof or the definition of `Znearest`. For completeness, the source
repository code below includes both. `Znearest` chooses the lower or upper
integer at an exact midpoint according to `choice`:

```coq
Section Znearest.

Variable choice : Z -> bool.

Definition Znearest x :=
  match Rcompare (x - IZR (Zfloor x)) (/2) with
  | Lt => Zfloor x
  | Eq => if choice (Zfloor x) then Zceil x else Zfloor x
  | Gt => Zceil x
  end.
```

The complete theorem under judgment is:

```coq
Section Fcore_ulp.

Variable beta : radix.
Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.
Notation F := (generic_format beta fexp).

Theorem round_N_ge_midp: forall choice u v,
 F u ->  ((u + pred u)/2 < v)%R
      -> (u <= round beta fexp (Znearest choice) v)%R.
Proof with auto with typeclass_instances.
intros choice u v Fu H.
rewrite <- (Ropp_involutive v).
rewrite round_N_opp.
rewrite <- (Ropp_involutive u).
apply Ropp_le_contravar.
apply round_N_le_midp.
now apply generic_format_opp.
apply Ropp_lt_cancel.
rewrite Ropp_involutive.
apply Rle_lt_trans with (2:=H).
unfold pred.
right; field.
Qed.
```

Sources: [FLoCq `Generic_fmt.v`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/Generic_fmt.v#L1648)
and [`Ulp.v`](https://gitlab.inria.fr/flocq/flocq/-/blob/7aab8f55bceec0cfafc3b3bc0e77e0dbb5a70c5f/src/Core/Ulp.v#L2478)

### Target code: Lean

The target helper always chooses the upper neighbor at an exact tie:

```lean
noncomputable def round_N_to_format
    (beta : Int) (fexp : Int → Int) [Valid_exp beta fexp]
    (x : ℝ) (hbeta : 1 < beta) : ℝ :=
  let d := Classical.choose (round_DN_exists beta fexp x hbeta)
  let u := Classical.choose (round_UP_exists beta fexp x hbeta)
  let mid := (d + u) / 2
  if hlt : x < mid then
    d
  else if hgt : mid < x then
    u
  else
    u
```

The complete target theorem under judgment is:

```lean
namespace FloatSpec.Core.Ulp

variable (beta : Int)
variable (fexp : Int → Int)
variable [FloatSpec.Core.Generic_fmt.Valid_exp beta fexp]

theorem round_N_ge_midp
    (choice : Int → Bool) (u v : ℝ)
    (Fu : FloatSpec.Core.Generic_fmt.generic_format beta fexp u)
    (h : (u + pred beta fexp u) / 2 < v) (hβ : 1 < beta) :
    ⦃⌜1 < beta⌝⦄
    (pure (FloatSpec.Core.Generic_fmt.round_N_to_format beta fexp v hβ) : Id ℝ)
    ⦃⇓r => ⌜u ≤ r⌝⦄ := by
  intro _; classical
  simp [wp, PostCond.noThrow, Id.run, pure]
  exact round_N_ge_midp_theorem (beta := beta) (fexp := fexp)
    (choice := choice) (u := u) (v := v) Fu hβ h
```

Sources: [FloatSpec `Generic_fmt.lean`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/67b5ab23d63593497379e028c48d0ef693d59bb5/FloatSpec/src/Core/Generic_fmt.lean#L7197)
and [`Ulp.lean`](https://github.com/Beneficial-AI-Foundation/FloatSpec/blob/67b5ab23d63593497379e028c48d0ef693d59bb5/FloatSpec/src/Core/Ulp.lean#L7409)

### Raw-LLM output

```json
{"alignment":"not_aligned","confidence":0.99,"rationale":"The target does not assert the result for the source's choice-dependent `round beta fexp (Znearest choice) v`. It instead uses `round_N_to_format`, whose definition has no choice parameter and always selects the upper result at ties. Thus the bound variable `choice` is semantically ignored, and the referenced rounding operation has observably different behavior on midpoint inputs.","differences":["Source rounding uses `Znearest choice`; target rounding uses the choice-independent `round_N_to_format`.","At an exact tie, the source may choose either adjacent value according to `choice`, while the target definition always chooses the upper value.","The target adds an explicit radix proof argument and Hoare precondition; these can encode Coq's radix invariant but do not repair the rounding-operation mismatch."]}
```

### Codex output

```json
{"alignment":"not_aligned","confidence":0.98,"rationale":"The target replaces the source’s choice-dependent nearest rounding with a fixed nearest-rounding function. In Coq, the conclusion uses `round beta fexp (Znearest choice) v`, whose result at an exact midpoint depends on `choice`. Lean instead uses `round_N_to_format beta fexp v hβ`, which has no `choice` argument and explicitly returns the upper neighbor on ties. Thus the quantified `choice` binder is semantically inert in the target and observable rounding behavior does not correspond for all inputs.","differences":["Source nearest rounding uses `Znearest choice`; target `round_N_to_format` ignores `choice`.","At midpoint ties, the source can select either adjacent value according to `choice`, while the target always selects the upper value."]}
```

### Why both answers are wrong

The helper-level observation is true: at the selected midpoint with
`choice = false`, Coq returns `0` and Lean returns `1`. But the item under
judgment is a theorem whose observable result is only the proposition
`u ≤ rounded(v)`. With `u = 0`, both `0 ≤ 0` and `0 ≤ 1` are true. The helper
difference therefore does not refute the theorem's conclusion.

Judge v24 initially proposed the same false counterexample. It was not
certified because the target observation failed the deterministic binding
check: `run code does not contain its invocation`. The final benchmark status
was `invalid`, rather than a verified `not_aligned`. This gate prevented the
bad conclusion from being counted as evidence, although it did not itself
solve the deeper observer-selection problem.

## Show-token-state

Case ID: `judge-3e5eaf1b07793615dc02`

Official label: `not_aligned`

Artifacts:

- [Frozen model input](inputs/judge-3e5eaf1b07793615dc02.json)
- [Raw-LLM result](results/raw-llm/judge-3e5eaf1b07793615dc02.json)
- [Codex result](results/codex/judge-3e5eaf1b07793615dc02.json)
- [Judge v24 result and compiler replays](results/judge-v24/judge-3e5eaf1b07793615dc02.json)

### Source code supplied to the baselines: Coq

```coq
#[export]
Instance showTokenState : Show EIP20Token.State :=
{|
  show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
               ++ "balances: " ++ show s.(balances) ++ sep
               ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.
```

The frozen payload contained no source dependencies. In particular, it did
not show the implementation of `Show (FMap A B)`.

### Additional source code recovered from the repository

```coq
Definition sep : string := ", ".

Definition string_of_FMap {A B : Type}
    `{countable.Countable A} `{base.EqDecision A}
    (showA : A -> string) (showB : B -> string) (m : FMap A B) : string :=
  "[" ++
    String.concat "; "
      (map (fun '(a, b) => showA a ++ "-->" ++ showB b)
           (FMap.elements m))
  ++ "]".

#[export]
Instance showFMap {A B : Type}
    `{countable.Countable A} `{base.EqDecision A} `{Show A} `{Show B}
    : Show (FMap A B) :=
{|
  show := string_of_FMap show show
|}.
```

Sources: [ConCert `EIP20TokenPrinters.v`](https://github.com/AU-COBRA/ConCert/blob/341f440abb955b58066c269ebe0a231e8172e403/examples/eip20/EIP20TokenPrinters.v#L41),
[`ChainPrinters.v`](https://github.com/AU-COBRA/ConCert/blob/341f440abb955b58066c269ebe0a231e8172e403/execution/test/ChainPrinters.v#L24), and
[`TestUtils.v`](https://github.com/AU-COBRA/ConCert/blob/341f440abb955b58066c269ebe0a231e8172e403/execution/test/TestUtils.v#L74)

### Target code: Lean

The target dependencies were present in the frozen payload:

```lean
class Show (α : Type) where
  render : α → String

def showValue [Show α] (value : α) : String := Show.render value
def sep : String := ", "

def showMap [LinearOrder κ] [Show κ] [Show ν] (map : FMap κ ν) : String :=
  "{" ++ String.intercalate "; " ((FMap.elements map).map fun (k, v) =>
    showValue k ++ " ↦ " ++ showValue v) ++ "}"

instance showTokenState : Show State := ⟨fun state =>
  "State{total_supply: " ++ showValue state.total_supply ++ sep ++
  "balances: " ++ showMap state.balances ++ sep ++
  "allowances: " ++ showMap state.allowances ++ "}"⟩
```

Source: [evaluated `Printers.lean` snapshot](source-snapshots/EIP20Base/Printers.lean)

### Raw-LLM output

```json
{"alignment":"uncertain","confidence":0.96,"rationale":"The source body delegates all three field renderings to overloaded `show`, but the supplied source closure contains no declarations for `Show`, `sep`, `EIP20Token.State`, or the field-specific instances. Consequently, it is impossible to establish that source map rendering has the same ordering, separators, and nested-map behavior as Lean's explicit `showMap`, or that the source interface carries a context corresponding to Lean's `[ChainBase]` assumption.","differences":["The target explicitly requires `[ChainBase]`; no corresponding source assumption or module parameter is supplied.","The source renders `balances` and `allowances` through instance-resolved `show`, whereas the target calls the concretely defined `showMap`; equivalence of those operations is not supplied.","The source definition of `sep` and the relevant `Show` instances are absent, so exact observable string equality cannot be verified."]}
```

### Codex output

```json
{"alignment":"uncertain","confidence":0.93,"rationale":"The outer rendering template corresponds, but the supplied source closure contains no declarations for `Show`, `sep`, `EIP20Token.State`, or the `Show` instances used for `balances` and `allowances`. Consequently, it is impossible to establish that Coq's generic `show` calls have the same observable behavior as Lean's explicit, sorted `showMap` calls, or that the source has an equivalent implicit `ChainBase` parameter.","differences":["Lean explicitly requires an implicit `[ChainBase]`; no corresponding source parameter or defining context is supplied.","Lean renders both map fields with `showMap`, whose ordering and formatting are defined; Coq uses unresolved generic `show` instances.","The source value of `sep` and the source definitions of the state fields and rendering class are absent."]}
```

### Why the abstentions are understandable but incomplete

Both baselines correctly identify the missing information. Without the source
`FMap` renderer, neither can justify a concrete string comparison. Codex's
tools do not help because its benchmark sandbox does not contain the actual
repositories.

Judge v24 recovers the missing source definitions and compiles one shared
empty-state input on both sides. The address representations do not matter for
empty maps. The native provers establish:

```text
Coq:  State{total_supply: 0, balances: [], allowances: []}
Lean: State{total_supply: 0, balances: {}, allowances: {}}
```

The source map printer uses square brackets, while the target uses braces.
Both proof harnesses passed, so this is a verified behavioral counterexample.

## What the three cases establish

| Case | The model did correctly | The missing judgment |
|---|---|---|
| `FLT_exp` | Read both formulas and calculated their results | Match inputs by semantic role, not position |
| `round_N_ge_midp` | Found a genuine helper-level difference | Observe the theorem conclusion, not an internal value |
| `showTokenState` | Recognized that necessary source definitions were absent | Retrieve repository closure and execute both sides |

The failures occur before or around formal calculation: choosing the relation,
choosing the observer, and obtaining the semantic closure. This is why strong
proof generation alone does not make the same model a reliable semantic judge.
