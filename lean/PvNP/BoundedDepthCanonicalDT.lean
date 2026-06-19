import PvNP.BoundedDepthDecisionTree

/-!
# The canonical decision tree of a DNF

This file builds the **canonical decision tree** of a DNF formula — the
deterministic core object whose depth a Håstad-style switching lemma bounds under
a random restriction.  It is built on the existing faithful
`PvNP.BoundedDepthFrege` and `PvNP.BoundedDepthDecisionTree` modules, with
**real Boolean semantics** throughout.

## HONEST SCOPE STATEMENT (read this)
This is **switching-lemma INFRASTRUCTURE ONLY**: the *deterministic core object*.
A switching lemma is a **probabilistic** statement — it says that under a *random
restriction* a small DNF collapses, with high probability, to a *shallow*
decision tree.  The probabilistic depth bound is the entire content of the
switching lemma and is **NOT** in this file.

This file provides only:
* a faithful DNF representation `Term n` / `DNF n` with real Boolean semantics
  `termEval` / `dnfEval`;
* a deterministic `assignVar` residualization of a DNF under a single variable
  assignment, with the real semantic preservation lemma `dnfEval_assignVar`;
* the deterministic `canonicalDT : DNF n → DTree n` construction (built on the
  existing `DTree`), terminating via a literal-occurrence measure;
* **the deliverable** `dtEval_canonicalDT`: the canonical decision tree computes
  exactly the DNF's Boolean function, `dtEval a (canonicalDT D) = dnfEval a D`.

This file does **NOT** prove the switching lemma, does **NOT** prove any lower
bound, and does **NOT** claim P ≠ NP.  It is the deterministic representation
layer only.

`Assignment n = Fin n → Bool`, `Literal`, `litEval` are reused from
`PvNP.CNFModel`; `DTree`, `dtEval`, `dtDepth` from
`PvNP.BoundedDepthDecisionTree`.
-/

namespace PvNP
namespace BoundedDepthCanonicalDT

open CNFModel
open BoundedDepthDecisionTree

/-! ## 1. DNF representation and real semantics -/

/-- A **term** is a conjunction of literals. -/
abbrev Term (n : Nat) := List (Literal n)

/-- A **DNF** is a disjunction of terms. -/
abbrev DNF (n : Nat) := List (Term n)

/-- Real semantics of a term: the conjunction of its literals' values. -/
def termEval {n : Nat} (a : Assignment n) (t : Term n) : Bool :=
  t.all (fun l => litEval a l)

/-- Real semantics of a DNF: the disjunction of its terms' values. -/
def dnfEval {n : Nat} (a : Assignment n) (D : DNF n) : Bool :=
  D.any (fun t => termEval a t)

@[simp] theorem termEval_nil {n : Nat} (a : Assignment n) :
    termEval a ([] : Term n) = true := rfl

@[simp] theorem termEval_cons {n : Nat} (a : Assignment n)
    (l : Literal n) (t : Term n) :
    termEval a (l :: t) = (litEval a l && termEval a t) := rfl

@[simp] theorem dnfEval_nil {n : Nat} (a : Assignment n) :
    dnfEval a ([] : DNF n) = false := rfl

@[simp] theorem dnfEval_cons {n : Nat} (a : Assignment n)
    (t : Term n) (D : DNF n) :
    dnfEval a (t :: D) = (termEval a t || dnfEval a D) := rfl

/-! ## 2. Residualization under a single variable assignment

`assignTerm v b t` simplifies a term under `v := b`: each literal on `v` whose
sign matches `b` is satisfied and dropped; a literal on `v` whose sign disagrees
with `b` falsifies the whole term, so the term is removed (`none`).  Literals on
other variables are kept unchanged.

`assignVar v b D` applies this to every term and drops the falsified ones. -/

/-- Simplify a single term under `v := b`.  Returns `none` if the term is
falsified (it contains a literal on `v` of the opposite sign), otherwise `some`
of the term with all `v`-literals (which are satisfied) removed. -/
def assignTerm {n : Nat} (v : Fin n) (b : Bool) : Term n → Option (Term n)
  | [] => some []
  | l :: t =>
      if l.var = v then
        if l.sign = b then
          -- literal satisfied: drop it, continue
          assignTerm v b t
        else
          -- literal falsified: whole term dies
          none
      else
        -- literal on another variable: keep it
        match assignTerm v b t with
        | some t' => some (l :: t')
        | none => none

/-- Residualize a whole DNF under `v := b`: simplify each term, dropping the
falsified ones. -/
def assignVar {n : Nat} (v : Fin n) (b : Bool) (D : DNF n) : DNF n :=
  D.filterMap (assignTerm v b)

/-! ## 3. Semantic preservation of residualization

The load-bearing semantic facts: under any assignment `a` with `a v = b`,
residualizing on `v := b` preserves both `termEval` and `dnfEval`. -/

/-- A satisfied `v`-literal is invisible to `termEval` when `a v = b`: dropping
it (or any agreeing `v`-literal) does not change the term's value; a disagreeing
`v`-literal makes the term false, matching `none`. -/
theorem termEval_assignTerm {n : Nat} (a : Assignment n)
    (v : Fin n) (b : Bool) (hb : a v = b) (t : Term n) :
    (match assignTerm v b t with
      | some t' => termEval a t'
      | none => false) = termEval a t := by
  induction t with
  | nil => simp [assignTerm]
  | cons l t ih =>
      by_cases hlv : l.var = v
      · by_cases hls : l.sign = b
        · -- literal satisfied
          rw [show assignTerm v b (l :: t) = assignTerm v b t by
                simp only [assignTerm, if_pos hlv, if_pos hls]]
          rw [ih]
          -- litEval a l = true, so prepending it is a no-op
          have hlit : litEval a l = true := by
            simp only [litEval, hlv, hb]
            subst hls; cases hs : l.sign <;> simp [hs]
          simp [termEval_cons, hlit]
        · -- literal falsified
          rw [show assignTerm v b (l :: t) = none by
                simp only [assignTerm, if_pos hlv, if_neg hls]]
          have hlit : litEval a l = false := by
            simp only [litEval, hlv, hb]
            cases hs : l.sign <;> simp only [hs] at hls ⊢ <;>
              simp_all
          simp [termEval_cons, hlit]
      · -- literal on another variable: kept
        cases hrec : assignTerm v b t with
        | some t' =>
            rw [show assignTerm v b (l :: t) = some (l :: t') by
                  simp only [assignTerm, if_neg hlv, hrec]]
            simp only [hrec] at ih
            simp only [termEval_cons]
            rw [ih]
        | none =>
            rw [show assignTerm v b (l :: t) = none by
                  simp only [assignTerm, if_neg hlv, hrec]]
            simp only [hrec] at ih
            simp only [termEval_cons]
            rw [← ih]
            simp

/-- **Residualization preserves `dnfEval`.**  When `a v = b`, residualizing the
whole DNF on `v := b` does not change its Boolean value under `a`.  This is the
real semantic preservation lemma (analogous to `eval_restrict`). -/
theorem dnfEval_assignVar {n : Nat} (a : Assignment n)
    (v : Fin n) (b : Bool) (hb : a v = b) (D : DNF n) :
    dnfEval a (assignVar v b D) = dnfEval a D := by
  induction D with
  | nil => simp [assignVar]
  | cons t D ih =>
      rw [show assignVar v b (t :: D)
            = (match assignTerm v b t with
                | some t' => t' :: assignVar v b D
                | none => assignVar v b D) by
            simp only [assignVar, List.filterMap_cons]
            cases assignTerm v b t <;> rfl]
      have hterm := termEval_assignTerm a v b hb t
      cases hrec : assignTerm v b t with
      | some t' =>
          simp only [hrec] at hterm
          simp only [dnfEval_cons, ih, hterm]
      | none =>
          simp only [hrec] at hterm
          simp only [dnfEval_cons, ih, ← hterm, Bool.false_or]

/-! ## 4. Termination measure: total literal occurrences -/

/-- The total number of literal occurrences in a DNF — the strictly-decreasing
measure for the canonical-tree recursion. -/
def dnfSize {n : Nat} (D : DNF n) : Nat :=
  (D.map (·.length)).foldr (· + ·) 0

@[simp] theorem dnfSize_nil {n : Nat} : dnfSize ([] : DNF n) = 0 := rfl

@[simp] theorem dnfSize_cons {n : Nat} (t : Term n) (D : DNF n) :
    dnfSize (t :: D) = t.length + dnfSize D := by
  simp [dnfSize]

/-- `assignTerm` never increases a term's length. -/
theorem length_assignTerm_le {n : Nat} (v : Fin n) (b : Bool)
    (t t' : Term n) (h : assignTerm v b t = some t') :
    t'.length ≤ t.length := by
  induction t generalizing t' with
  | nil => simp only [assignTerm, Option.some.injEq] at h; subst h; simp
  | cons l t ih =>
      simp only [assignTerm] at h
      by_cases hlv : l.var = v
      · by_cases hls : l.sign = b
        · simp only [if_pos hlv, if_pos hls] at h
          exact Nat.le_trans (ih t' h) (Nat.le_succ _)
        · simp only [if_pos hlv, if_neg hls] at h; exact absurd h (by simp)
      · simp only [if_neg hlv] at h
        cases hrec : assignTerm v b t with
        | some t'' =>
            simp only [hrec, Option.some.injEq] at h
            subst h
            simp only [List.length_cons]
            exact Nat.succ_le_succ (ih t'' hrec)
        | none => simp only [hrec] at h; exact absurd h (by simp)

/-- `assignVar` never increases the DNF size. -/
theorem dnfSize_assignVar_le {n : Nat} (v : Fin n) (b : Bool) (D : DNF n) :
    dnfSize (assignVar v b D) ≤ dnfSize D := by
  induction D with
  | nil => simp [assignVar]
  | cons t D ih =>
      simp only [assignVar, List.filterMap_cons] at *
      cases hrec : assignTerm v b t with
      | some t' =>
          simp only [hrec, dnfSize_cons]
          have := length_assignTerm_le v b t t' hrec
          omega
      | none =>
          simp only [hrec, dnfSize_cons]
          omega

/-- **Strict decrease.** When the head term of `D` is `(l :: t)` with `l` a
literal on `v`, residualizing on `v := b` strictly shrinks the size, for either
value `b`.  This is exactly the fact the canonical-tree recursion needs. -/
theorem dnfSize_assignVar_lt {n : Nat} (v : Fin n) (b : Bool)
    (l : Literal n) (t : Term n) (D : DNF n) (hlv : l.var = v) :
    dnfSize (assignVar v b ((l :: t) :: D)) < dnfSize ((l :: t) :: D) := by
  rw [show assignVar v b ((l :: t) :: D)
        = (match assignTerm v b (l :: t) with
            | some t' => t' :: assignVar v b D
            | none => assignVar v b D) by
        simp only [assignVar, List.filterMap_cons]
        cases assignTerm v b (l :: t) <;> rfl]
  have hle := dnfSize_assignVar_le v b D
  by_cases hls : l.sign = b
  · -- head literal satisfied: assignTerm drops `l`, so head term shrinks
    have hhead : assignTerm v b (l :: t) = assignTerm v b t := by
      simp only [assignTerm, if_pos hlv, if_pos hls]
    rw [hhead]
    cases hrec : assignTerm v b t with
    | some t' =>
        simp only [hrec, dnfSize_cons, List.length_cons]
        have := length_assignTerm_le v b t t' hrec
        omega
    | none =>
        simp only [hrec, dnfSize_cons, List.length_cons]
        omega
  · -- head literal falsified: whole head term dies
    have hhead : assignTerm v b (l :: t) = none := by
      simp only [assignTerm, if_pos hlv, if_neg hls]
    rw [hhead]
    simp only [dnfSize_cons, List.length_cons]
    omega

/-! ## 5. The canonical decision tree

`canonicalDT` deterministically turns a DNF into a decision tree:

* `[]` (constant false) → `leaf false`;
* a DNF whose first term is empty `[] :: _` (that term is constant true) →
  `leaf true`;
* otherwise the first term is `(l :: t)`; let `v := l.var`.  Query `v` and, in
  each child, residualize the **whole** DNF under the queried value and recurse.

Termination: each recursive call residualizes on `v`, which occurs in the head
term `(l :: t)`, so `dnfSize` strictly decreases (lemma `dnfSize_assignVar_lt`). -/

/-- The canonical decision tree of a DNF (deterministic; queries the first
literal of the first surviving term and residualizes). -/
def canonicalDT {n : Nat} : DNF n → DTree n
  | [] => DTree.leaf false
  | [] :: _ => DTree.leaf true
  | (l :: t) :: D =>
      DTree.node l.var
        (canonicalDT (assignVar l.var false ((l :: t) :: D)))
        (canonicalDT (assignVar l.var true ((l :: t) :: D)))
  termination_by D => dnfSize D
  decreasing_by
    · exact dnfSize_assignVar_lt l.var false l t D rfl
    · exact dnfSize_assignVar_lt l.var true l t D rfl

/-! ## 6. THE DELIVERABLE — eval-correctness

The canonical decision tree computes exactly the DNF's Boolean function. -/

/-- **`dtEval_canonicalDT` — the deliverable.**  For every assignment `a` and
DNF `D`, the canonical decision tree evaluates to exactly the DNF's Boolean
value: `dtEval a (canonicalDT D) = dnfEval a D`.  This is the genuine,
unweakened eval-correctness of the deterministic core object. -/
theorem dtEval_canonicalDT {n : Nat} (a : Assignment n) (D : DNF n) :
    dtEval a (canonicalDT D) = dnfEval a D := by
  match D with
  | [] => simp [canonicalDT]
  | [] :: D => simp [canonicalDT, dnfEval_cons, termEval_nil]
  | (l :: t) :: D =>
      rw [show canonicalDT ((l :: t) :: D)
            = DTree.node l.var
                (canonicalDT (assignVar l.var false ((l :: t) :: D)))
                (canonicalDT (assignVar l.var true ((l :: t) :: D))) from by
            rw [canonicalDT]]
      rw [dtEval_node]
      -- recurse into both children (well-founded on dnfSize)
      have ih0 := dtEval_canonicalDT a (assignVar l.var false ((l :: t) :: D))
      have ih1 := dtEval_canonicalDT a (assignVar l.var true ((l :: t) :: D))
      cases hv : a l.var with
      | true =>
          simp only [if_pos, hv]
          rw [ih1, dnfEval_assignVar a l.var true hv]
      | false =>
          simp only [hv, Bool.false_eq_true, if_false]
          rw [ih0, dnfEval_assignVar a l.var false hv]
  termination_by dnfSize D
  decreasing_by
    · exact dnfSize_assignVar_lt l.var false l t D rfl
    · exact dnfSize_assignVar_lt l.var true l t D rfl
