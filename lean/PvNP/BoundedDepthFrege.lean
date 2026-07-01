import PvNP.CNFModel

/-!
# A faithful bounded-depth (AC0) formula model and a sound bounded-depth proof system

This file builds the GENUINE FOUNDATION for the next Cook–Reckhow rung above
resolution: a faithful **bounded-depth propositional formula model** with real
Boolean semantics, a **bounded-depth Frege-style (Tait sequent) proof system**
with semantically valid inference rules, and a real **soundness theorem**.

## HONEST SCOPE STATEMENT (read this)
This is **FOUNDATION ONLY**.  It provides:
* a faithful formula type `BDFormula n` that `eval`s to an actual `Bool`;
* a real `depth` measure (the "bounded-depth" alternation/nesting measure);
* a Tait-style sequent proof system `BDProof` whose every rule is proven to
  preserve truth (soundness), with a `BDRefutation F` deriving falsity from a
  finite set of formula-hypotheses;
* the soundness theorem `bdFrege_sound`: a `BDRefutation F` witnesses real
  unsatisfiability of `F` — exactly analogous to `resolutionRefutation_unsat`.

This file does **NOT** prove any lower bound, does **NOT** invoke or formalize a
switching lemma, and does **NOT** claim P ≠ NP.  Soundness alone proves no
hardness.  A lower bound would require the switching lemma and is a later effort.

The assignment type `Fin n → Bool` and the satisfaction style are reused from
`PvNP.CNFModel` to match the existing resolution foundation
(`resolution_sound` / `resolutionRefutation_unsat`).
-/

namespace PvNP
namespace BoundedDepthFrege

open CNFModel

/-! ## 1. Faithful bounded-depth formula type -/

/--
A bounded-depth propositional formula over variables `Fin n`.

Gates: a literal `lit` (variable with a polarity, matching `CNFModel.Literal`),
the Boolean constants `tru`/`fls`, and **unbounded fan-in** `and`/`or` gates
taking a `List` of subformulas.  Unbounded fan-in is exactly what distinguishes
the bounded-depth (AC0) setting from binary-gate formulas.

This is a faithful model: see `eval` below for the real Boolean semantics.
-/
inductive BDFormula (n : Nat) : Type where
  | tru : BDFormula n
  | fls : BDFormula n
  | lit : Literal n → BDFormula n
  | and : List (BDFormula n) → BDFormula n
  | or  : List (BDFormula n) → BDFormula n
  deriving Repr

/-!
### A custom induction principle for the nested-`List` inductive

Lean's default recursor for `BDFormula` (a nested inductive over `List`) is
awkward to use directly with the `induction` tactic.  We give an explicit,
fully-honest induction principle `BDFormula.recAux` proved by structural
recursion using `List`'s own induction; every `def`/proof over `BDFormula` then
goes through it, so termination is never in doubt.
-/

/-- Custom dependent recursor: to prove `motive F` for all `F`, handle the leaf
cases and the gate cases given that the property already holds for every child
(packaged via a list-level predicate built from `motive`). -/
@[elab_as_elim]
def BDFormula.recAux {n : Nat} {motive : BDFormula n → Prop}
    (htru : motive .tru)
    (hfls : motive .fls)
    (hlit : ∀ l, motive (.lit l))
    (hand : ∀ l, (∀ f ∈ l, motive f) → motive (.and l))
    (hor  : ∀ l, (∀ f ∈ l, motive f) → motive (.or l)) :
    ∀ F, motive F
  | .tru => htru
  | .fls => hfls
  | .lit l => hlit l
  | .and l => hand l (fun f hf => BDFormula.recAux htru hfls hlit hand hor f)
  | .or  l => hor  l (fun f hf => BDFormula.recAux htru hfls hlit hand hor f)
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem hf
      omega

/-!
### Real recursive Boolean semantics

Unbounded-fan-in gates evaluate via `List.all` / `List.any` over the recursive
`eval` of the children.  We define the list-aggregation through explicit helpers
so structural recursion is transparent.
-/

/--
Real recursive Boolean semantics.  `and` gates use `List.all`, `or` gates use
`List.any`, over the recursive `eval` of each child.
-/
def eval {n : Nat} (a : Assignment n) : BDFormula n → Bool
  | .tru => true
  | .fls => false
  | .lit l => litEval a l
  | .and l => l.attach.all (fun f => eval a f.1)
  | .or  l => l.attach.any (fun f => eval a f.1)
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

/-- Bridge: `all` over `attach` equals `all` over the original list. -/
theorem attach_all_eq {α : Type _} (l : List α) (p : α → Bool) :
    (l.attach.all (fun f => p f.val)) = l.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩ (List.mem_attach l _)
  · intro h x _
    exact h x.1 x.2

/-- Bridge: `any` over `attach` equals `any` over the original list. -/
theorem attach_any_eq {α : Type _} (l : List α) (p : α → Bool) :
    (l.attach.any (fun f => p f.val)) = l.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨x, hx, hpx⟩
    exact ⟨⟨x, hx⟩, List.mem_attach l _, hpx⟩

theorem eval_tru {n : Nat} (a : Assignment n) :
    eval a (BDFormula.tru) = true := by simp only [eval]

theorem eval_fls {n : Nat} (a : Assignment n) :
    eval a (BDFormula.fls) = false := by simp only [eval]

theorem eval_lit {n : Nat} (a : Assignment n) (l : Literal n) :
    eval a (BDFormula.lit l) = litEval a l := by simp only [eval]

/-- `and` evaluation is `List.all` over the children (attach erased). -/
theorem eval_and {n : Nat} (a : Assignment n) (l : List (BDFormula n)) :
    eval a (BDFormula.and l) = l.all (fun f => eval a f) := by
  rw [show eval a (BDFormula.and l)
        = l.attach.all (fun f => eval a f.1) by simp only [eval]]
  exact attach_all_eq l (fun f => eval a f)

/-- `or` evaluation is `List.any` over the children (attach erased). -/
theorem eval_or {n : Nat} (a : Assignment n) (l : List (BDFormula n)) :
    eval a (BDFormula.or l) = l.any (fun f => eval a f) := by
  rw [show eval a (BDFormula.or l)
        = l.attach.any (fun f => eval a f.1) by simp only [eval]]
  exact attach_any_eq l (fun f => eval a f)

/--
The alternation/nesting depth — the "bounded-depth" measure.  Leaves have depth
`0`; an `and`/`or` gate is one deeper than its deepest child.
-/
def depth {n : Nat} : BDFormula n → Nat
  | .tru => 0
  | .fls => 0
  | .lit _ => 0
  | .and l => 1 + (l.attach.map (fun f => depth f.1)).foldr Nat.max 0
  | .or  l => 1 + (l.attach.map (fun f => depth f.1)).foldr Nat.max 0
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

/-- `F` is satisfiable when some assignment makes it evaluate to `true`. -/
def satisfiable {n : Nat} (F : BDFormula n) : Prop :=
  ∃ a : Assignment n, eval a F = true

/-- `F` is a tautology when every assignment makes it evaluate to `true`. -/
def tautology {n : Nat} (F : BDFormula n) : Prop :=
  ∀ a : Assignment n, eval a F = true

/-! ## 2. Bounded-depth Frege / Tait-style sequent proof system

We use a one-sided (Tait) sequent calculus.  A *sequent* is a `List (BDFormula
n)` read **disjunctively**: it asserts that at least one listed formula is true.
A proof of a sequent `Γ` is a derivation; soundness means a provable `Γ` is
valid (true under every assignment).  The empty sequent `[]` has disjunction
`false`, so it is never provable — that is what gives refutational power.

The rules below are a small but genuinely sound core: two leaf axioms (constant
`tru` and excluded-middle on a literal), weakening, `or`-introduction, and
`and`-introduction.  Every rule is proven truth-preserving in §3.
-/

/-- Semantic validity of a sequent (read disjunctively): some listed formula is
true under `a`.  `sequentTrue a Γ = Γ.any (eval a)`. -/
def sequentTrue {n : Nat} (a : Assignment n) (Γ : List (BDFormula n)) : Bool :=
  Γ.any (fun f => eval a f)

/-- A sequent is *valid* if it is true under every assignment. -/
def SequentValid {n : Nat} (Γ : List (BDFormula n)) : Prop :=
  ∀ a : Assignment n, sequentTrue a Γ = true

/--
The bounded-depth Frege / Tait sequent proof system.

Each constructor is an inference rule; `BDProof Γ` is a derivation of the
disjunctive sequent `Γ`.  Every rule is semantically sound (proved in §3).
-/
inductive BDProof {n : Nat} : List (BDFormula n) → Prop where
  /-- Constant axiom: any sequent containing `tru` is valid. -/
  | truAx (Γ : List (BDFormula n)) (h : BDFormula.tru ∈ Γ) : BDProof Γ
  /-- Excluded middle on a literal: a sequent containing both polarities of a
      variable is valid. -/
  | litEM (Γ : List (BDFormula n)) (v : Fin n)
      (hpos : BDFormula.lit ⟨v, true⟩ ∈ Γ)
      (hneg : BDFormula.lit ⟨v, false⟩ ∈ Γ) : BDProof Γ
  /-- Weakening: a valid sequent stays valid when more disjuncts are added. -/
  | weaken {Γ Δ : List (BDFormula n)} (h : BDProof Γ)
      (hsub : ∀ f, f ∈ Γ → f ∈ Δ) : BDProof Δ
  /-- `or`-introduction: if the children list of an `or` gate together with the
      context `Γ` is provable (one of them is true), the gate may replace that
      whole child list as a single disjunct. -/
  | orIntro {Γ : List (BDFormula n)} {l : List (BDFormula n)}
      (h : BDProof (l ++ Γ)) : BDProof (BDFormula.or l :: Γ)
  /-- `and`-introduction: if every child of an `and` gate is provable together
      with the same context `Γ`, then either some context disjunct is true or all
      children are true, i.e. the `and` gate is true. -/
  | andIntro {Γ : List (BDFormula n)} {l : List (BDFormula n)}
      (h : ∀ f, f ∈ l → BDProof (f :: Γ)) : BDProof (BDFormula.and l :: Γ)

/-! ## 2a. Type-valued measured proof traces

The Prop-valued `BDProof` surface is enough for soundness, but proof-complexity
work also needs first-class proof objects with explicit resource accessors.  The
following trace type mirrors the existing sound rules and erases back to
`BDProof`; it does not assert completeness or any lower bound. -/

/-- A Type-valued bounded-depth proof trace mirroring the existing `BDProof`
rules.  Its constructors carry the same sound premises, while the trace itself
can be measured by the resource accessors below. -/
inductive BDProofTrace {n : Nat} : List (BDFormula n) → Type where
  /-- Constant axiom trace. -/
  | truAx (Γ : List (BDFormula n)) (h : BDFormula.tru ∈ Γ) : BDProofTrace Γ
  /-- Literal excluded-middle axiom trace. -/
  | litEM (Γ : List (BDFormula n)) (v : Fin n)
      (hpos : BDFormula.lit ⟨v, true⟩ ∈ Γ)
      (hneg : BDFormula.lit ⟨v, false⟩ ∈ Γ) : BDProofTrace Γ
  /-- Weakening trace. -/
  | weaken {Γ Δ : List (BDFormula n)} (h : BDProofTrace Γ)
      (hsub : ∀ f, f ∈ Γ → f ∈ Δ) : BDProofTrace Δ
  /-- `or`-introduction trace. -/
  | orIntro {Γ : List (BDFormula n)} {l : List (BDFormula n)}
      (h : BDProofTrace (l ++ Γ)) : BDProofTrace (BDFormula.or l :: Γ)
  /-- `and`-introduction trace with one trace per child premise. -/
  | andIntro {Γ : List (BDFormula n)} {l : List (BDFormula n)}
      (h : ∀ f, f ∈ l → BDProofTrace (f :: Γ)) : BDProofTrace (BDFormula.and l :: Γ)

namespace BDProofTrace

/-- Erase a Type-valued trace to the existing Prop-valued proof surface. -/
def erase {n : Nat} {Γ : List (BDFormula n)} : BDProofTrace Γ → BDProof Γ
  | .truAx Γ h => BDProof.truAx Γ h
  | .litEM Γ v hpos hneg => BDProof.litEM Γ v hpos hneg
  | .weaken h hsub => BDProof.weaken (erase h) hsub
  | .orIntro h => BDProof.orIntro (erase h)
  | .andIntro h => BDProof.andIntro (fun f hf => erase (h f hf))

/-- Count trace nodes, summing all `and`-premise branches. -/
def size {n : Nat} {Γ : List (BDFormula n)} : BDProofTrace Γ → Nat
  | .truAx _ _ => 1
  | .litEM _ _ _ _ => 1
  | .weaken h _ => 1 + size h
  | .orIntro h => 1 + size h
  | @BDProofTrace.andIntro _ Γ l h =>
      1 + (l.attach.map (fun f => size (h f.1 f.2))).foldr Nat.add 0

/-- Alias for the first line-count resource surface. -/
def lineCount {n : Nat} {Γ : List (BDFormula n)} (π : BDProofTrace Γ) : Nat :=
  size π

/-- Maximum inference nesting depth of the trace. -/
def derivationDepth {n : Nat} {Γ : List (BDFormula n)} : BDProofTrace Γ → Nat
  | .truAx _ _ => 1
  | .litEM _ _ _ _ => 1
  | .weaken h _ => 1 + derivationDepth h
  | .orIntro h => 1 + derivationDepth h
  | @BDProofTrace.andIntro _ Γ l h =>
      1 + (l.attach.map (fun f => derivationDepth (h f.1 f.2))).foldr Nat.max 0

/-- Maximum formula depth in a sequent. -/
def sequentMaxFormulaDepth {n : Nat} (Γ : List (BDFormula n)) : Nat :=
  (Γ.attach.map (fun f => depth f.1)).foldr Nat.max 0

/-- Conclusion-sequent maximum formula depth exposed as a trace resource. -/
def maxFormulaDepth {n : Nat} {Γ : List (BDFormula n)} (_π : BDProofTrace Γ) : Nat :=
  sequentMaxFormulaDepth Γ

end BDProofTrace

/-! ## 3. Soundness of the proof system -/

/-- `sequentTrue` over a cons. -/
theorem sequentTrue_cons {n : Nat} (a : Assignment n)
    (f : BDFormula n) (Γ : List (BDFormula n)) :
    sequentTrue a (f :: Γ) = (eval a f || sequentTrue a Γ) := by
  simp [sequentTrue]

/-- `sequentTrue` over an append. -/
theorem sequentTrue_append {n : Nat} (a : Assignment n)
    (Γ Δ : List (BDFormula n)) :
    sequentTrue a (Γ ++ Δ) = (sequentTrue a Γ || sequentTrue a Δ) := by
  simp [sequentTrue, List.any_append]

/-- Membership gives a disjunct. -/
theorem sequentTrue_of_mem {n : Nat} (a : Assignment n)
    {f : BDFormula n} {Γ : List (BDFormula n)}
    (hmem : f ∈ Γ) (hf : eval a f = true) :
    sequentTrue a Γ = true := by
  simp only [sequentTrue, List.any_eq_true]
  exact ⟨f, hmem, hf⟩

/-- **Soundness of the bounded-depth Frege/Tait system.** Every provable sequent
is valid (true under every assignment). -/
theorem bdProof_sound {n : Nat} {Γ : List (BDFormula n)} (h : BDProof Γ) :
    SequentValid Γ := by
  induction h with
  | truAx Γ hmem =>
      intro a
      exact sequentTrue_of_mem a hmem (eval_tru a)
  | litEM Γ v hpos hneg =>
      intro a
      cases hv : a v with
      | true =>
          refine sequentTrue_of_mem a hpos ?_
          rw [eval_lit]; simp [litEval, hv]
      | false =>
          refine sequentTrue_of_mem a hneg ?_
          rw [eval_lit]; simp [litEval, hv]
  | weaken h hsub ih =>
      intro a
      have hΓ := ih a
      simp only [sequentTrue, List.any_eq_true] at hΓ ⊢
      rcases hΓ with ⟨f, hfmem, hfeval⟩
      exact ⟨f, hsub f hfmem, hfeval⟩
  | @orIntro Γ l h ih =>
      intro a
      have hlΓ := ih a
      rw [sequentTrue_append] at hlΓ
      rw [sequentTrue_cons, eval_or]
      have hrw : sequentTrue a l = l.any (fun f => eval a f) := rfl
      rw [← hrw]
      exact hlΓ
  | @andIntro Γ l h ih =>
      intro a
      rw [sequentTrue_cons, eval_and]
      by_cases hΓ : sequentTrue a Γ = true
      · rw [hΓ, Bool.or_true]
      · have hall : l.all (fun f => eval a f) = true := by
          rw [List.all_eq_true]
          intro f hfmem
          have hfval := ih f hfmem a
          rw [sequentTrue_cons] at hfval
          rcases Bool.or_eq_true _ _ |>.mp hfval with hf | hg
          · exact hf
          · exact absurd hg hΓ
        rw [hall, Bool.true_or]

/-- Soundness for Type-valued measured traces, by erasure to `BDProof`. -/
theorem bdProofTrace_sound {n : Nat} {Γ : List (BDFormula n)}
    (π : BDProofTrace Γ) :
    SequentValid Γ :=
  bdProof_sound π.erase

/-! ## 4. Refutations and the unsatisfiability deliverable

A `BDRefutation F` refutes a finite list of hypotheses `F : List (BDFormula n)`.
It is a `BDProof` of the sequent listing the De Morgan negation of every
hypothesis.  Since every hypothesis being true forces every negated hypothesis
to be false, validity of the negation-sequent (from soundness) contradicts joint
satisfaction — yielding real unsatisfiability of `F`.
-/

/-- De Morgan / structural negation of a bounded-depth formula.  Real semantics:
`eval a (neg F) = ! eval a F` (proved in `eval_neg`). -/
def neg {n : Nat} : BDFormula n → BDFormula n
  | .tru => .fls
  | .fls => .tru
  | .lit l => .lit ⟨l.var, !l.sign⟩
  | .and l => .or  (l.attach.map (fun f => neg f.1))
  | .or  l => .and (l.attach.map (fun f => neg f.1))
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

/-- Pointwise-agreement congruence for `List.any` (proved by list induction,
since mathlib has no direct `any_congr` here). -/
theorem any_congr_mem {α : Type _} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.any_cons, List.any_cons]
      rw [h x (List.mem_cons_self x xs)]
      rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Pointwise-agreement congruence for `List.all`. -/
theorem all_congr_mem {α : Type _} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.all_cons, List.all_cons]
      rw [h x (List.mem_cons_self x xs)]
      rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- **`neg` is the real Boolean negation.** -/
theorem eval_neg {n : Nat} (a : Assignment n) (F : BDFormula n) :
    eval a (neg F) = ! eval a F := by
  induction F using BDFormula.recAux with
  | htru => simp only [neg, eval_fls, eval_tru, Bool.not_true]
  | hfls => simp only [neg, eval_fls, eval_tru, Bool.not_false]
  | hlit l =>
      cases hs : l.sign <;> simp [neg, eval_lit, litEval, hs]
  | hand l ih =>
      -- neg (and l) = or (map neg over attach); eval or = any; eval and = all.
      rw [show neg (BDFormula.and l)
            = BDFormula.or (l.attach.map (fun f => neg f.1)) from by
              rw [neg]]
      rw [eval_or, eval_and]
      rw [List.attach_map_val l (fun f => neg f)]
      -- goal: (l.map neg).any (eval a) = ! l.all (eval a)
      rw [List.any_map, List.not_all_eq_any_not]
      apply any_congr_mem
      intro f hf
      simpa [Function.comp] using ih f hf
  | hor l ih =>
      rw [show neg (BDFormula.or l)
            = BDFormula.and (l.attach.map (fun f => neg f.1)) from by
              rw [neg]]
      rw [eval_and, eval_or]
      rw [List.attach_map_val l (fun f => neg f)]
      -- goal: (l.map neg).all (eval a) = ! l.any (eval a)
      rw [List.all_map, List.not_any_eq_all_not]
      apply all_congr_mem
      intro f hf
      simpa [Function.comp] using ih f hf

/-- A bounded-depth refutation of a finite hypothesis list `F`: a proof in the
sound system that the sequent of negated hypotheses is valid. -/
structure BDRefutation {n : Nat} (F : List (BDFormula n)) : Prop where
  proof : BDProof (F.map neg)

/-- A Type-valued bounded-depth refutation trace with explicit measurable proof
data before erasure to the Prop-valued `BDRefutation` surface. -/
structure BDRefutationTrace {n : Nat} (F : List (BDFormula n)) : Type where
  proof : BDProofTrace (F.map neg)

namespace BDRefutationTrace

/-- Erase a Type-valued refutation trace to the existing Prop-valued refutation. -/
def erase {n : Nat} {F : List (BDFormula n)}
    (π : BDRefutationTrace F) : BDRefutation F where
  proof := π.proof.erase

/-- Node-count resource for a refutation trace. -/
def size {n : Nat} {F : List (BDFormula n)} (π : BDRefutationTrace F) : Nat :=
  π.proof.size

/-- Line-count resource for a refutation trace. -/
def lineCount {n : Nat} {F : List (BDFormula n)} (π : BDRefutationTrace F) : Nat :=
  π.proof.lineCount

/-- Derivation-depth resource for a refutation trace. -/
def derivationDepth {n : Nat} {F : List (BDFormula n)} (π : BDRefutationTrace F) : Nat :=
  π.proof.derivationDepth

/-- Conclusion-sequent formula-depth resource for a refutation trace. -/
def maxFormulaDepth {n : Nat} {F : List (BDFormula n)} (π : BDRefutationTrace F) : Nat :=
  π.proof.maxFormulaDepth

end BDRefutationTrace

/-- A proof-carrying measured refutation trace together with explicit resource
budgets.  The budget fields are data only; the proof fields certify that the
existing measured trace accessors stay within those supplied budgets. -/
structure BDRefutationTraceProfile {n : Nat} (F : List (BDFormula n)) : Type where
  trace : BDRefutationTrace F
  sizeBudget : Nat
  lineCountBudget : Nat
  derivationDepthBudget : Nat
  maxFormulaDepthBudget : Nat
  size_le_budget : trace.size ≤ sizeBudget
  lineCount_le_budget : trace.lineCount ≤ lineCountBudget
  derivationDepth_le_budget : trace.derivationDepth ≤ derivationDepthBudget
  maxFormulaDepth_le_budget : trace.maxFormulaDepth ≤ maxFormulaDepthBudget

namespace BDRefutationTraceProfile

/-- Erase a profiled measured refutation trace to the existing Prop-valued
refutation surface. -/
def erase {n : Nat} {F : List (BDFormula n)}
    (π : BDRefutationTraceProfile F) : BDRefutation F :=
  π.trace.erase

end BDRefutationTraceProfile

/-- **`bdFrege_sound` — the deliverable.** A `BDRefutation F` witnesses real
unsatisfiability: no assignment satisfies every hypothesis in `F`. -/
theorem bdFrege_sound {n : Nat} {F : List (BDFormula n)}
    (π : BDRefutation F) :
    ¬ ∃ a : Assignment n, ∀ f ∈ F, eval a f = true := by
  rintro ⟨a, hsat⟩
  have hvalid : sequentTrue a (F.map neg) = true := bdProof_sound π.proof a
  simp only [sequentTrue, List.any_map, List.any_eq_true] at hvalid
  rcases hvalid with ⟨f, hfmem, hfeval⟩
  rw [Function.comp_apply] at hfeval
  rw [eval_neg] at hfeval
  have hf : eval a f = true := hsat f hfmem
  rw [hf] at hfeval
  simp at hfeval

/-- Soundness for Type-valued measured refutation traces, by erasure to
`BDRefutation`. -/
theorem bdFregeTrace_sound {n : Nat} {F : List (BDFormula n)}
    (π : BDRefutationTrace F) :
    ¬ ∃ a : Assignment n, ∀ f ∈ F, eval a f = true :=
  bdFrege_sound π.erase

/-- Soundness for profiled measured refutation traces, by consuming the measured
trace through the existing trace soundness theorem. -/
theorem bdFregeTraceProfile_sound {n : Nat} {F : List (BDFormula n)}
    (π : BDRefutationTraceProfile F) :
    ¬ ∃ a : Assignment n, ∀ f ∈ F, eval a f = true :=
  bdFregeTrace_sound π.trace

/-! ## 5. Non-vacuity sanity check

A concrete tiny **unsatisfiable** hypothesis set with an actual `BDRefutation`,
showing the system is not vacuous.  Over one variable `x = (0 : Fin 1)`, the
hypotheses `x` and `¬x` are jointly unsatisfiable; the negated-hypothesis sequent
is `[¬x, x]`, refuted by the literal excluded-middle rule. -/

/-- The tiny contradictory hypothesis set `{x, ¬x}` over one variable. -/
def tinyContradiction : List (BDFormula 1) :=
  [BDFormula.lit ⟨0, true⟩, BDFormula.lit ⟨0, false⟩]

/-- A concrete refutation of `{x, ¬x}` via literal excluded middle. -/
def tinyRefutation : BDRefutation tinyContradiction where
  proof := by
    -- `tinyContradiction.map neg = [lit ⟨0,false⟩, lit ⟨0,true⟩]`.
    show BDProof (tinyContradiction.map neg)
    have hmap : tinyContradiction.map neg
        = [BDFormula.lit ⟨0, false⟩, BDFormula.lit ⟨0, true⟩] := by
      simp [tinyContradiction, neg]
    rw [hmap]
    exact BDProof.litEM _ (0 : Fin 1)
      (by simp) (by simp)

/-- Sanity: the tiny set is genuinely unsatisfiable (follows from soundness). -/
theorem tinyContradiction_unsat :
    ¬ ∃ a : Assignment 1, ∀ f ∈ tinyContradiction, eval a f = true :=
  bdFrege_sound tinyRefutation

end BoundedDepthFrege
end PvNP
