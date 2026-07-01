import PvNP.BoundedDepthFrege
import PvNP.BoundedDepthDecisionTree
import PvNP.BoundedDepthRestriction

/-!
# Restricted PHP floor interface

This module starts the bounded-depth Frege/PHP floor interface without claiming a
Frege lower bound.  It provides a restricted pigeonhole formula surface, an
isolated decision-tree depth-floor statement shape, and a tiny proved `1 × 1`
bounded query-depth floor.  The proved floor is only for that concrete restricted
view and is not a PHP/Frege lower bound.
-/

namespace PvNP
namespace RestrictedPHPFloor

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction

/-- Variable index for "pigeon `p` maps to hole `h`" in a `pigeons × holes`
rectangle encoded in `Fin (Nat.succ (pigeons * holes))`, so degenerate empty
rectangles still have a harmless ambient variable type. -/
def phpVar (pigeons holes : Nat) (p : Fin pigeons) (h : Fin holes) :
    Fin (Nat.succ (pigeons * holes)) :=
  ⟨(p.val * holes + h.val) % Nat.succ (pigeons * holes),
    Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Positive literal saying pigeon `p` is assigned to hole `h`. -/
def mapsLit (pigeons holes : Nat) (p : Fin pigeons) (h : Fin holes) :
    Literal (Nat.succ (pigeons * holes)) :=
  { var := phpVar pigeons holes p h, sign := true }

/-- Negative literal saying pigeon `p` is not assigned to hole `h`. -/
def notMapsLit (pigeons holes : Nat) (p : Fin pigeons) (h : Fin holes) :
    Literal (Nat.succ (pigeons * holes)) :=
  { var := phpVar pigeons holes p h, sign := false }

/-- Hole choices allowed for each pigeon in the restricted PHP view. -/
structure RestrictedPHP (pigeons holes : Nat) where
  allowed : Fin pigeons → List (Fin holes)

/-- Enumerate a finite initial segment as `Fin n` values. -/
def finList (n : Nat) : List (Fin n) :=
  List.pmap (fun i hi => (Fin.mk i hi : Fin n))
    (List.range n)
    (by
      intro i hi
      exact List.mem_range.mp hi)

/-- A pigeon must choose at least one allowed hole. -/
def pigeonSomewhereClause {pigeons holes : Nat} (R : RestrictedPHP pigeons holes)
    (p : Fin pigeons) : BDFormula (Nat.succ (pigeons * holes)) :=
  BDFormula.or ((R.allowed p).map (fun h => BDFormula.lit (mapsLit pigeons holes p h)))

/-- Two pigeons may not occupy the same hole. -/
def noCollisionClause (pigeons holes : Nat) (p q : Fin pigeons) (h : Fin holes) :
    BDFormula (Nat.succ (pigeons * holes)) :=
  BDFormula.or [BDFormula.lit (notMapsLit pigeons holes p h),
    BDFormula.lit (notMapsLit pigeons holes q h)]

/-- The restricted PHP formula: all pigeons choose an allowed hole, and all proper
pair/hole collisions are forbidden.  Collision clauses are emitted only for
`p.val < q.val`, so self-collisions are not inserted into the restricted PHP view.
-/
def restrictedPHPFormula {pigeons holes : Nat} (R : RestrictedPHP pigeons holes) :
    BDFormula (Nat.succ (pigeons * holes)) :=
  let ps : List (Fin pigeons) := finList pigeons
  let hs : List (Fin holes) := finList holes
  let someClauses := ps.map (pigeonSomewhereClause R)
  let collisionClauses := ps.bind (fun p =>
    ps.bind (fun q =>
      if p.val < q.val then
        hs.map (fun h => noCollisionClause pigeons holes p q h)
      else
        []))
  BDFormula.and (someClauses ++ collisionClauses)

/-- A public boundary record for a proposed decision-tree floor.  Supplying this
record is evidence of the exact restricted formula, restriction family, and depth
threshold being studied; it is not by itself a lower-bound proof. -/
structure PHPDepthFloorBoundary (pigeons holes : Nat) where
  view : RestrictedPHP pigeons holes
  restrictionFamily : List (Restriction (Nat.succ (pigeons * holes)))
  depthFloor : Nat

/-- The actual depth-floor statement shape for a boundary record.  It remains an
isolated proposition until proved for a concrete boundary. -/
def PHPDepthFloorStatement {pigeons holes : Nat}
    (B : PHPDepthFloorBoundary pigeons holes) : Prop :=
  ∀ ρ, ρ ∈ B.restrictionFamily → ∀ T : DTree (Nat.succ (pigeons * holes)),
    (∀ a : Assignment (Nat.succ (pigeons * holes)), Agree ρ a →
      dtEval a T = eval a (restrict ρ (restrictedPHPFormula B.view))) →
    B.depthFloor ≤ dtDepth T

/-- The boundary's formula is exactly the restricted PHP formula of its view. -/
theorem phpBoundary_formula_eq {pigeons holes : Nat}
    (B : PHPDepthFloorBoundary pigeons holes) :
    restrictedPHPFormula B.view = restrictedPHPFormula B.view := rfl

/-! ## Tiny `1 × 1` bounded floor

The following declarations prove only a concrete query-depth floor for the
restricted `1`-pigeon/`1`-hole view under the empty restriction.  They do not state
or imply a Frege lower bound or any general PHP lower bound.
-/

/-- The single PHP variable in the tiny `1 × 1` view. -/
def tinyOneOnePHPVar : Fin (Nat.succ (1 * 1)) :=
  phpVar 1 1 ⟨0, by decide⟩ ⟨0, by decide⟩

/-- The `1 × 1` restricted PHP view: the lone pigeon may use the lone hole. -/
def tinyOneOneRestrictedPHP : RestrictedPHP 1 1 where
  allowed _ := [⟨0, by decide⟩]

/-- Empty/free restriction on the two ambient variables of the `1 × 1` view. -/
def tinyOneOneEmptyRestriction : Restriction (Nat.succ (1 * 1)) :=
  fun _ => none

/-- Boundary record for the tiny concrete bounded decision-tree floor. -/
def tinyOneOnePHPDepthFloorBoundary : PHPDepthFloorBoundary 1 1 where
  view := tinyOneOneRestrictedPHP
  restrictionFamily := [tinyOneOneEmptyRestriction]
  depthFloor := 1

/-- The tiny restricted PHP formula computes exactly the single PHP variable under
the empty/free restriction. -/
theorem eval_tinyOneOneRestrictedPHPFormula
    (a : Assignment (Nat.succ (1 * 1))) :
    eval a (restrict tinyOneOneEmptyRestriction
      (restrictedPHPFormula tinyOneOneRestrictedPHP)) = a tinyOneOnePHPVar := by
  rw [show restrictedPHPFormula tinyOneOneRestrictedPHP =
      BDFormula.and [BDFormula.or [BDFormula.lit (mapsLit 1 1 ⟨0, by decide⟩ ⟨0, by decide⟩)]] by
    simp [restrictedPHPFormula, tinyOneOneRestrictedPHP, pigeonSomewhereClause,
      finList]]
  simp [restrict, restrict_and, restrict_or, eval_and, eval_or, eval_lit,
    tinyOneOneEmptyRestriction, mapsLit, tinyOneOnePHPVar, phpVar, litEval]

/-- If a decision tree has different outputs on two assignments, it has positive
query depth. -/
theorem one_le_dtDepth_of_dtEval_ne {n : Nat} (T : DTree n)
    {a b : Assignment n} (h : dtEval a T ≠ dtEval b T) :
    1 ≤ dtDepth T := by
  cases T with
  | leaf c => simp at h
  | node v t0 t1 => simp [dtDepth]

/-- Assignment setting the tiny PHP variable to `false` and all other ambient
variables to `false`. -/
def tinyOneOneFalseAssignment : Assignment (Nat.succ (1 * 1)) :=
  fun _ => false

/-- Assignment setting exactly the tiny PHP variable to `true`. -/
def tinyOneOneTrueAssignment : Assignment (Nat.succ (1 * 1)) :=
  fun v => v = tinyOneOnePHPVar

/-- Both witness assignments agree with the empty/free restriction. -/
theorem agree_tinyOneOneEmptyRestriction (a : Assignment (Nat.succ (1 * 1))) :
    Agree tinyOneOneEmptyRestriction a := by
  intro v b h
  cases h

/-- Concrete `1 × 1` bounded decision-tree/query-depth floor.  This is only a
tiny restricted PHP view floor, not a Frege/PHP lower bound. -/
theorem tinyOneOnePHPDepthFloor :
    PHPDepthFloorStatement tinyOneOnePHPDepthFloorBoundary := by
  intro ρ hρ T hT
  simp [tinyOneOnePHPDepthFloorBoundary] at hρ
  subst ρ
  apply one_le_dtDepth_of_dtEval_ne T
    (a := tinyOneOneFalseAssignment) (b := tinyOneOneTrueAssignment)
  have hfalse : dtEval tinyOneOneFalseAssignment T = false := by
    rw [hT tinyOneOneFalseAssignment (agree_tinyOneOneEmptyRestriction _)]
    simpa [tinyOneOnePHPDepthFloorBoundary, tinyOneOneFalseAssignment] using
      eval_tinyOneOneRestrictedPHPFormula tinyOneOneFalseAssignment
  have htrue : dtEval tinyOneOneTrueAssignment T = true := by
    rw [hT tinyOneOneTrueAssignment (agree_tinyOneOneEmptyRestriction _)]
    simpa [tinyOneOnePHPDepthFloorBoundary, tinyOneOneTrueAssignment] using
      eval_tinyOneOneRestrictedPHPFormula tinyOneOneTrueAssignment
  rw [hfalse, htrue]
  decide

/-! ## Bounded `2 × 1` falsified-clause search floor

The following declarations are deliberately bounded search-query infrastructure
for the concrete `2`-pigeon/`1`-hole view.  Since the full `2 × 1` PHP Boolean
formula is identically false, a positive Boolean decision-tree depth floor for
that Boolean function would be false: the constant-false tree has depth `0`.
The theorem below is instead a certificate-search floor for outputting a
falsified clause of this fixed formula.
-/

/-- First pigeon-to-hole variable in the concrete `2 × 1` view. -/
def twoOnePHPVar0 : Fin (Nat.succ (2 * 1)) :=
  phpVar 2 1 ⟨0, by decide⟩ ⟨0, by decide⟩

/-- Second pigeon-to-hole variable in the concrete `2 × 1` view. -/
def twoOnePHPVar1 : Fin (Nat.succ (2 * 1)) :=
  phpVar 2 1 ⟨1, by decide⟩ ⟨0, by decide⟩

/-- The concrete `2 × 1` restricted PHP view: both pigeons may use the lone hole. -/
def twoOneRestrictedPHP : RestrictedPHP 2 1 where
  allowed _ := [⟨0, by decide⟩]

/-- Empty/free restriction on the three ambient variables of the `2 × 1` view. -/
def twoOneEmptyRestriction : Restriction (Nat.succ (2 * 1)) :=
  fun _ => none

/-- The bounded outputs for the `2 × 1` PHP falsified-clause search problem. -/
inductive TwoOnePHPFalsifiedClause where
  | pigeon0
  | pigeon1
  | collision
  deriving DecidableEq, Repr

namespace TwoOnePHPFalsifiedClause

/-- Validity predicate for the bounded search output: the output names a clause
of the fixed `2 × 1` PHP formula falsified by the assignment. -/
def Valid (a : Assignment (Nat.succ (2 * 1))) :
    TwoOnePHPFalsifiedClause → Prop
  | pigeon0 => a twoOnePHPVar0 = false
  | pigeon1 => a twoOnePHPVar1 = false
  | collision => a twoOnePHPVar0 = true ∧ a twoOnePHPVar1 = true

end TwoOnePHPFalsifiedClause

/-- A small output-valued query tree.  This is bounded search-query
infrastructure only, not a Boolean decision-tree lower-bound interface. -/
inductive QueryTree (n : Nat) (α : Type) where
  | leaf (out : α) : QueryTree n α
  | node (v : Fin n) (t0 t1 : QueryTree n α) : QueryTree n α

/-- Evaluate an output-valued query tree under an assignment. -/
def queryEval {n : Nat} {α : Type} (a : Assignment n) : QueryTree n α → α
  | QueryTree.leaf out => out
  | QueryTree.node v t0 t1 => if a v then queryEval a t1 else queryEval a t0

/-- Depth of an output-valued query tree. -/
def queryDepth {n : Nat} {α : Type} : QueryTree n α → Nat
  | QueryTree.leaf _ => 0
  | QueryTree.node _ t0 t1 => Nat.succ (max (queryDepth t0) (queryDepth t1))

/-- Reusable bounded-search ambiguity floor.  If every constant answer is
invalid somewhere, and after any first query set to `true` every possible leaf
answer is still invalid somewhere on that branch, then a correct output-valued
query tree has worst-case depth at least two.  This is only generic query-tree
infrastructure for certificate search; it is not a Boolean PHP lower bound. -/
theorem queryTree_depth_ge_two_of_two_unqueried_ambiguity {n : Nat} {α : Type}
    (Valid : Assignment n → α → Prop)
    (T : QueryTree n α)
    (hT : ∀ a : Assignment n, Valid a (queryEval a T))
    (hLeaf : ∀ out : α, ∃ a : Assignment n, ¬ Valid a out)
    (hTrueLeaf : ∀ (out : α) (v : Fin n),
      ∃ a : Assignment n, a v = true ∧ ¬ Valid a out) :
    2 ≤ queryDepth T := by
  cases T with
  | leaf out =>
      rcases hLeaf out with ⟨a, ha⟩
      exact False.elim (ha (hT a))
  | node v t0 t1 =>
      cases t0 with
      | node v0 s00 s01 =>
          simp [queryDepth]
          exact Nat.le_trans (Nat.succ_pos _) (Nat.le_max_left _ _)
      | leaf out0 =>
          cases t1 with
          | node v1 s10 s11 =>
              simp [queryDepth]
          | leaf out1 =>
              rcases hTrueLeaf out1 v with ⟨a1, hv1, ha1⟩
              have h1 : Valid a1 out1 := by
                simpa [queryEval, hv1] using hT a1
              exact False.elim (ha1 h1)

/-- Assignment helper for the concrete `2 × 1` ambient variable space. -/
def twoOneAssignment (x0 x1 dummy : Bool) : Assignment (Nat.succ (2 * 1)) :=
  fun v => if v = twoOnePHPVar0 then x0 else if v = twoOnePHPVar1 then x1 else dummy

theorem twoOneAssignment_var0 (x0 x1 dummy : Bool) :
    twoOneAssignment x0 x1 dummy twoOnePHPVar0 = x0 := by
  simp [twoOneAssignment]

theorem twoOneAssignment_var1 (x0 x1 dummy : Bool) :
    twoOneAssignment x0 x1 dummy twoOnePHPVar1 = x1 := by
  simp [twoOneAssignment, twoOnePHPVar0, twoOnePHPVar1, phpVar]

private theorem twoOne_leaf_invalid
    (out : TwoOnePHPFalsifiedClause) :
    ∃ a : Assignment (Nat.succ (2 * 1)),
      ¬ TwoOnePHPFalsifiedClause.Valid a out := by
  cases out
  · exact ⟨twoOneAssignment true false false, by
      simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0]⟩
  · exact ⟨twoOneAssignment false true false, by
      simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var1]⟩
  · exact ⟨twoOneAssignment false false false, by
      simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0,
        twoOneAssignment_var1]⟩

private theorem twoOne_trueBranch_invalid
    (out : TwoOnePHPFalsifiedClause) (v : Fin (Nat.succ (2 * 1))) :
    ∃ a : Assignment (Nat.succ (2 * 1)), a v = true ∧
      ¬ TwoOnePHPFalsifiedClause.Valid a out := by
  by_cases hv0 : v = twoOnePHPVar0
  · subst v
    cases out
    · exact ⟨twoOneAssignment true false false, by
        simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0]⟩
    · exact ⟨twoOneAssignment true true false, by
        simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0,
          twoOneAssignment_var1]⟩
    · exact ⟨twoOneAssignment true false false, by
        simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0,
          twoOneAssignment_var1]⟩
  · by_cases hv1 : v = twoOnePHPVar1
    · subst v
      cases out
      · exact ⟨twoOneAssignment true true false, by
          simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0,
            twoOneAssignment_var1]⟩
      · exact ⟨twoOneAssignment false true false, by
          simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var1]⟩
      · exact ⟨twoOneAssignment false true false, by
          simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0,
            twoOneAssignment_var1]⟩
    · cases out
      · exact ⟨twoOneAssignment true false true, by
          constructor
          · simp [twoOneAssignment, hv0, hv1]
          · simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0]⟩
      · exact ⟨twoOneAssignment false true true, by
          constructor
          · simp [twoOneAssignment, hv0, hv1]
          · simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var1]⟩
      · exact ⟨twoOneAssignment false false true, by
          constructor
          · simp [twoOneAssignment, hv0, hv1]
          · simp [TwoOnePHPFalsifiedClause.Valid, twoOneAssignment_var0,
              twoOneAssignment_var1]⟩

/-- Concrete `2 × 1` bounded falsified-clause search-query depth floor.  This is
only a bounded search/certificate result for the fixed `2 × 1` view; it is not a
Frege/PHP lower bound and not a positive Boolean depth floor for the identically
false unsatisfiable formula. -/
theorem twoOnePHPFalsifiedClauseSearchDepthFloor
    (T : QueryTree (Nat.succ (2 * 1)) TwoOnePHPFalsifiedClause)
    (hT : ∀ a : Assignment (Nat.succ (2 * 1)),
      TwoOnePHPFalsifiedClause.Valid a (queryEval a T)) :
    2 ≤ queryDepth T := by
  exact queryTree_depth_ge_two_of_two_unqueried_ambiguity
    TwoOnePHPFalsifiedClause.Valid T hT twoOne_leaf_invalid twoOne_trueBranch_invalid

/-! ## Bounded `3 × 2` falsified-clause search floor

This is the next concrete bounded PHP-search increment: for the unsatisfiable
`3`-pigeon/`2`-hole view, any output-valued query tree that always returns a
falsified clause must make at least two queries in the worst case.  As above,
this is only a bounded certificate-search statement for one fixed finite view.
-/

def threeTwoPHPVar00 : Fin (Nat.succ (3 * 2)) :=
  phpVar 3 2 ⟨0, by decide⟩ ⟨0, by decide⟩

def threeTwoPHPVar01 : Fin (Nat.succ (3 * 2)) :=
  phpVar 3 2 ⟨0, by decide⟩ ⟨1, by decide⟩

def threeTwoPHPVar10 : Fin (Nat.succ (3 * 2)) :=
  phpVar 3 2 ⟨1, by decide⟩ ⟨0, by decide⟩

def threeTwoPHPVar11 : Fin (Nat.succ (3 * 2)) :=
  phpVar 3 2 ⟨1, by decide⟩ ⟨1, by decide⟩

def threeTwoPHPVar20 : Fin (Nat.succ (3 * 2)) :=
  phpVar 3 2 ⟨2, by decide⟩ ⟨0, by decide⟩

def threeTwoPHPVar21 : Fin (Nat.succ (3 * 2)) :=
  phpVar 3 2 ⟨2, by decide⟩ ⟨1, by decide⟩

/-- The bounded outputs for the `3 × 2` PHP falsified-clause search problem. -/
inductive ThreeTwoPHPFalsifiedClause where
  | pigeon0 | pigeon1 | pigeon2
  | collision01h0 | collision01h1
  | collision02h0 | collision02h1
  | collision12h0 | collision12h1
  deriving DecidableEq, Repr

namespace ThreeTwoPHPFalsifiedClause

/-- Validity predicate for naming a clause of the fixed `3 × 2` PHP formula
falsified by the assignment. -/
def Valid (a : Assignment (Nat.succ (3 * 2))) :
    ThreeTwoPHPFalsifiedClause → Prop
  | pigeon0 => a threeTwoPHPVar00 = false ∧ a threeTwoPHPVar01 = false
  | pigeon1 => a threeTwoPHPVar10 = false ∧ a threeTwoPHPVar11 = false
  | pigeon2 => a threeTwoPHPVar20 = false ∧ a threeTwoPHPVar21 = false
  | collision01h0 => a threeTwoPHPVar00 = true ∧ a threeTwoPHPVar10 = true
  | collision01h1 => a threeTwoPHPVar01 = true ∧ a threeTwoPHPVar11 = true
  | collision02h0 => a threeTwoPHPVar00 = true ∧ a threeTwoPHPVar20 = true
  | collision02h1 => a threeTwoPHPVar01 = true ∧ a threeTwoPHPVar21 = true
  | collision12h0 => a threeTwoPHPVar10 = true ∧ a threeTwoPHPVar20 = true
  | collision12h1 => a threeTwoPHPVar11 = true ∧ a threeTwoPHPVar21 = true

/-- Validity of a named falsified clause is decidable (each case is a finite
conjunction of Boolean equalities).  Bookkeeping instance only. -/
instance validDecidable (a : Assignment (Nat.succ (3 * 2))) :
    (out : ThreeTwoPHPFalsifiedClause) → Decidable (Valid a out)
  | pigeon0 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar00 = false ∧ a threeTwoPHPVar01 = false))
  | pigeon1 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar10 = false ∧ a threeTwoPHPVar11 = false))
  | pigeon2 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar20 = false ∧ a threeTwoPHPVar21 = false))
  | collision01h0 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar00 = true ∧ a threeTwoPHPVar10 = true))
  | collision01h1 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar01 = true ∧ a threeTwoPHPVar11 = true))
  | collision02h0 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar00 = true ∧ a threeTwoPHPVar20 = true))
  | collision02h1 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar01 = true ∧ a threeTwoPHPVar21 = true))
  | collision12h0 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar10 = true ∧ a threeTwoPHPVar20 = true))
  | collision12h1 =>
      inferInstanceAs (Decidable (a threeTwoPHPVar11 = true ∧ a threeTwoPHPVar21 = true))

end ThreeTwoPHPFalsifiedClause

/-- Fixed finite semantic selector for the `3 x 2` PHP falsified-clause search
interface.  It inspects only the six named PHP variables in the ambient
`Nat.succ (3 * 2)` assignment space and returns one falsified pigeon or collision
clause. -/
def threeTwoPHPFalsifiedClauseSelector
    (a : Assignment (Nat.succ (3 * 2))) :
    ThreeTwoPHPFalsifiedClause :=
  if a threeTwoPHPVar00 || a threeTwoPHPVar01 then
    if a threeTwoPHPVar10 || a threeTwoPHPVar11 then
      if a threeTwoPHPVar20 || a threeTwoPHPVar21 then
        if a threeTwoPHPVar00 then
          if a threeTwoPHPVar10 then
            ThreeTwoPHPFalsifiedClause.collision01h0
          else if a threeTwoPHPVar20 then
            ThreeTwoPHPFalsifiedClause.collision02h0
          else
            ThreeTwoPHPFalsifiedClause.collision12h1
        else if a threeTwoPHPVar11 then
          ThreeTwoPHPFalsifiedClause.collision01h1
        else if a threeTwoPHPVar21 then
          ThreeTwoPHPFalsifiedClause.collision02h1
        else
          ThreeTwoPHPFalsifiedClause.collision12h0
      else
        ThreeTwoPHPFalsifiedClause.pigeon2
    else
      ThreeTwoPHPFalsifiedClause.pigeon1
  else
    ThreeTwoPHPFalsifiedClause.pigeon0

/-- The fixed finite selector always names a falsified clause for the `3 x 2` PHP
search interface.  This is semantic selector validity only; it does not construct
or verify any query tree. -/
theorem threeTwoPHPFalsifiedClauseSelector_valid
    (a : Assignment (Nat.succ (3 * 2))) :
    ThreeTwoPHPFalsifiedClause.Valid a
      (threeTwoPHPFalsifiedClauseSelector a) := by
  cases h00 : a threeTwoPHPVar00 <;>
    cases h01 : a threeTwoPHPVar01 <;>
    cases h10 : a threeTwoPHPVar10 <;>
    cases h11 : a threeTwoPHPVar11 <;>
    cases h20 : a threeTwoPHPVar20 <;>
    cases h21 : a threeTwoPHPVar21 <;>
    simp [threeTwoPHPFalsifiedClauseSelector,
      ThreeTwoPHPFalsifiedClause.Valid, h00, h01, h10, h11, h20, h21]

/-- Premise-reduction helper for S2044-style consumers: it is enough to show that
a supplied query tree evaluates to the fixed finite semantic selector.  The tree
itself is still supplied here. -/
theorem threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hEval :
      ∀ a : Assignment (Nat.succ (3 * 2)),
        queryEval a T = threeTwoPHPFalsifiedClauseSelector a) :
    ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T) := by
  intro a
  rw [hEval a]
  exact threeTwoPHPFalsifiedClauseSelector_valid a

private def queryBool {n : Nat} {α : Type} (v : Fin n)
    (next : Bool → QueryTree n α) : QueryTree n α :=
  QueryTree.node v (next false) (next true)

private def threeTwoPHPFalsifiedClauseSelectorOfBools
    (b00 b01 b10 b11 b20 b21 : Bool) :
    ThreeTwoPHPFalsifiedClause :=
  if b00 || b01 then
    if b10 || b11 then
      if b20 || b21 then
        if b00 then
          if b10 then
            ThreeTwoPHPFalsifiedClause.collision01h0
          else if b20 then
            ThreeTwoPHPFalsifiedClause.collision02h0
          else
            ThreeTwoPHPFalsifiedClause.collision12h1
        else if b11 then
          ThreeTwoPHPFalsifiedClause.collision01h1
        else if b21 then
          ThreeTwoPHPFalsifiedClause.collision02h1
        else
          ThreeTwoPHPFalsifiedClause.collision12h0
      else
        ThreeTwoPHPFalsifiedClause.pigeon2
    else
      ThreeTwoPHPFalsifiedClause.pigeon1
  else
    ThreeTwoPHPFalsifiedClause.pigeon0

/-- Concrete fixed finite `3 x 2` PHP query tree that queries the six named PHP
variables and returns the corresponding semantic selector output.  This is only a
finite search tree for the existing bounded interface. -/
def threeTwoPHPFalsifiedClauseQueryTree :
    QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause :=
  queryBool threeTwoPHPVar00 (fun b00 =>
    queryBool threeTwoPHPVar01 (fun b01 =>
      queryBool threeTwoPHPVar10 (fun b10 =>
        queryBool threeTwoPHPVar11 (fun b11 =>
          queryBool threeTwoPHPVar20 (fun b20 =>
            queryBool threeTwoPHPVar21 (fun b21 =>
              QueryTree.leaf
                (threeTwoPHPFalsifiedClauseSelectorOfBools
                  b00 b01 b10 b11 b20 b21)))))))

/-- Evaluation theorem for the concrete fixed finite `3 x 2` PHP query tree: for
every ambient assignment, the tree returns exactly the S2046 semantic selector. -/
theorem threeTwoPHPFalsifiedClauseQueryTree_evalSelector
    (a : Assignment (Nat.succ (3 * 2))) :
    queryEval a threeTwoPHPFalsifiedClauseQueryTree =
      threeTwoPHPFalsifiedClauseSelector a := by
  cases h00 : a threeTwoPHPVar00 <;>
    cases h01 : a threeTwoPHPVar01 <;>
    cases h10 : a threeTwoPHPVar10 <;>
    cases h11 : a threeTwoPHPVar11 <;>
    cases h20 : a threeTwoPHPVar20 <;>
    cases h21 : a threeTwoPHPVar21 <;>
    simp [threeTwoPHPFalsifiedClauseQueryTree,
      threeTwoPHPFalsifiedClauseSelectorOfBools,
      threeTwoPHPFalsifiedClauseSelector, queryBool, queryEval,
      h00, h01, h10, h11, h20, h21]

private def branchOnly {n : Nat} (v : Fin n) : Assignment n :=
  fun w => w = v

private def branchOr {n : Nat} (v x : Fin n) : Assignment n :=
  fun w => w = v || w = x

private theorem threeTwo_leaf_invalid
    (out : ThreeTwoPHPFalsifiedClause) :
    ∃ a : Assignment (Nat.succ (3 * 2)),
      ¬ ThreeTwoPHPFalsifiedClause.Valid a out := by
  cases out
  · exact ⟨fun _ => true, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => true, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => true, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => false, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => false, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => false, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => false, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => false, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩
  · exact ⟨fun _ => false, by simp [ThreeTwoPHPFalsifiedClause.Valid]⟩

private theorem branchOnly_invalid_collision
    (v x y : Fin (Nat.succ (3 * 2))) (hxy : x ≠ y) :
    ¬ (branchOnly v x = true ∧ branchOnly v y = true) := by
  intro h
  have hxv : x = v := by simpa [branchOnly] using h.left
  have hyv : y = v := by simpa [branchOnly] using h.right
  exact hxy (hxv.trans hyv.symm)

private theorem threeTwo_trueBranch_invalid
    (out : ThreeTwoPHPFalsifiedClause) (v : Fin (Nat.succ (3 * 2))) :
    ∃ a : Assignment (Nat.succ (3 * 2)), a v = true ∧
      ¬ ThreeTwoPHPFalsifiedClause.Valid a out := by
  cases out
  · refine ⟨branchOr v threeTwoPHPVar00, by simp [branchOr], ?_⟩
    intro h
    have htrue : branchOr v threeTwoPHPVar00 threeTwoPHPVar00 = true := by simp [branchOr]
    exact Bool.noConfusion (h.left.symm.trans htrue)
  · refine ⟨branchOr v threeTwoPHPVar10, by simp [branchOr], ?_⟩
    intro h
    have htrue : branchOr v threeTwoPHPVar10 threeTwoPHPVar10 = true := by simp [branchOr]
    exact Bool.noConfusion (h.left.symm.trans htrue)
  · refine ⟨branchOr v threeTwoPHPVar20, by simp [branchOr], ?_⟩
    intro h
    have htrue : branchOr v threeTwoPHPVar20 threeTwoPHPVar20 = true := by simp [branchOr]
    exact Bool.noConfusion (h.left.symm.trans htrue)
  · exact ⟨branchOnly v, by simp [branchOnly],
      branchOnly_invalid_collision v threeTwoPHPVar00 threeTwoPHPVar10 (by decide)⟩
  · exact ⟨branchOnly v, by simp [branchOnly],
      branchOnly_invalid_collision v threeTwoPHPVar01 threeTwoPHPVar11 (by decide)⟩
  · exact ⟨branchOnly v, by simp [branchOnly],
      branchOnly_invalid_collision v threeTwoPHPVar00 threeTwoPHPVar20 (by decide)⟩
  · exact ⟨branchOnly v, by simp [branchOnly],
      branchOnly_invalid_collision v threeTwoPHPVar01 threeTwoPHPVar21 (by decide)⟩
  · exact ⟨branchOnly v, by simp [branchOnly],
      branchOnly_invalid_collision v threeTwoPHPVar10 threeTwoPHPVar20 (by decide)⟩
  · exact ⟨branchOnly v, by simp [branchOnly],
      branchOnly_invalid_collision v threeTwoPHPVar11 threeTwoPHPVar21 (by decide)⟩

/-- Concrete `3 × 2` bounded falsified-clause search-query depth floor.  This is
only a bounded search/certificate result for the fixed `3 × 2` view; it is not a
Frege/PHP lower bound and not a positive Boolean depth floor for the identically
false unsatisfiable formula. -/
theorem threeTwoPHPFalsifiedClauseSearchDepthFloor
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hT : ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    2 ≤ queryDepth T := by
  exact queryTree_depth_ge_two_of_two_unqueried_ambiguity
    ThreeTwoPHPFalsifiedClause.Valid T hT threeTwo_leaf_invalid threeTwo_trueBranch_invalid

/-! ## S2066: bounded `3 × 2` falsified-clause search floor of three

This section strengthens the fixed `3 × 2` falsified-clause search floor from
two queries to three, by a genuine adversary argument: answer the first query
`false`; if the second query is the pigeon-partner of the first, answer `true`,
otherwise answer `false`.  After any two queries answered this way, every
possible output is invalidated by some consistent assignment.

As before, this is only a bounded certificate-search statement for one fixed
finite view; it is not a Frege/PHP lower bound and not a positive Boolean depth
floor for the identically false unsatisfiable formula.
-/

/-- The three same-pigeon variable pairs of the fixed `3 × 2` view, in both
orders. -/
private def pigeonPair (v w : Fin (Nat.succ (3 * 2))) : Prop :=
  (v = threeTwoPHPVar00 ∧ w = threeTwoPHPVar01) ∨
    (v = threeTwoPHPVar01 ∧ w = threeTwoPHPVar00) ∨
    (v = threeTwoPHPVar10 ∧ w = threeTwoPHPVar11) ∨
    (v = threeTwoPHPVar11 ∧ w = threeTwoPHPVar10) ∨
    (v = threeTwoPHPVar20 ∧ w = threeTwoPHPVar21) ∨
    (v = threeTwoPHPVar21 ∧ w = threeTwoPHPVar20)

/-- Adversary step 1: after one query answered `false`, every output is invalid
on some consistent assignment. -/
private theorem threeTwo_falseBranch_invalid
    (out : ThreeTwoPHPFalsifiedClause) (v : Fin (Nat.succ (3 * 2))) :
    ∃ a : Assignment (Nat.succ (3 * 2)), a v = false ∧
      ¬ ThreeTwoPHPFalsifiedClause.Valid a out := by
  cases out
  case pigeon0 =>
    by_cases hv : v = threeTwoPHPVar00
    · exact ⟨branchOnly threeTwoPHPVar01, by subst hv; decide, by decide⟩
    · exact ⟨branchOnly threeTwoPHPVar00, by simp [branchOnly, hv], by decide⟩
  case pigeon1 =>
    by_cases hv : v = threeTwoPHPVar10
    · exact ⟨branchOnly threeTwoPHPVar11, by subst hv; decide, by decide⟩
    · exact ⟨branchOnly threeTwoPHPVar10, by simp [branchOnly, hv], by decide⟩
  case pigeon2 =>
    by_cases hv : v = threeTwoPHPVar20
    · exact ⟨branchOnly threeTwoPHPVar21, by subst hv; decide, by decide⟩
    · exact ⟨branchOnly threeTwoPHPVar20, by simp [branchOnly, hv], by decide⟩
  all_goals exact ⟨fun _ => false, rfl, by decide⟩

/-- Adversary step 2, partner branch: with a pigeon pair queried `false` then
`true`, every output is invalid on some consistent assignment. -/
private theorem threeTwo_partnerTrue_invalid
    (out : ThreeTwoPHPFalsifiedClause) (v w : Fin (Nat.succ (3 * 2)))
    (hpair : pigeonPair v w) :
    ∃ a : Assignment (Nat.succ (3 * 2)), a v = false ∧ a w = true ∧
      ¬ ThreeTwoPHPFalsifiedClause.Valid a out := by
  rcases hpair with ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩ <;>
    subst hv <;> subst hw <;> cases out <;>
    first
      | exact ⟨branchOr threeTwoPHPVar00 threeTwoPHPVar00, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar01 threeTwoPHPVar01, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar10 threeTwoPHPVar10, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar11 threeTwoPHPVar11, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar20 threeTwoPHPVar20, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar21 threeTwoPHPVar21, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar00 threeTwoPHPVar10, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar00 threeTwoPHPVar20, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar01 threeTwoPHPVar10, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar01 threeTwoPHPVar20, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar10 threeTwoPHPVar00, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar10 threeTwoPHPVar20, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar11 threeTwoPHPVar00, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar11 threeTwoPHPVar20, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar20 threeTwoPHPVar00, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar20 threeTwoPHPVar10, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar21 threeTwoPHPVar00, by decide, by decide, by decide⟩
      | exact ⟨branchOr threeTwoPHPVar21 threeTwoPHPVar10, by decide, by decide, by decide⟩

/-- Adversary step 2, non-partner branch: with two non-pigeon-pair queries both
answered `false`, every output is invalid on some consistent assignment. -/
private theorem threeTwo_bothFalse_invalid
    (out : ThreeTwoPHPFalsifiedClause) (v w : Fin (Nat.succ (3 * 2)))
    (hpair : ¬ pigeonPair v w) :
    ∃ a : Assignment (Nat.succ (3 * 2)), a v = false ∧ a w = false ∧
      ¬ ThreeTwoPHPFalsifiedClause.Valid a out := by
  cases out
  case pigeon0 =>
    by_cases hxv : threeTwoPHPVar00 = v
    · by_cases hyw : threeTwoPHPVar01 = w
      · exact absurd (Or.inl ⟨hxv.symm, hyw.symm⟩) hpair
      · refine ⟨branchOnly threeTwoPHPVar01, ?_, ?_, by decide⟩
        · rw [← hxv]; decide
        · simp [branchOnly, Ne.symm hyw]
    · by_cases hxw : threeTwoPHPVar00 = w
      · by_cases hyv : threeTwoPHPVar01 = v
        · exact absurd (Or.inr (Or.inl ⟨hyv.symm, hxw.symm⟩)) hpair
        · refine ⟨branchOnly threeTwoPHPVar01, ?_, ?_, by decide⟩
          · simp [branchOnly, Ne.symm hyv]
          · rw [← hxw]; decide
      · refine ⟨branchOnly threeTwoPHPVar00, ?_, ?_, by decide⟩
        · simp [branchOnly, Ne.symm hxv]
        · simp [branchOnly, Ne.symm hxw]
  case pigeon1 =>
    by_cases hxv : threeTwoPHPVar10 = v
    · by_cases hyw : threeTwoPHPVar11 = w
      · exact absurd (Or.inr (Or.inr (Or.inl ⟨hxv.symm, hyw.symm⟩))) hpair
      · refine ⟨branchOnly threeTwoPHPVar11, ?_, ?_, by decide⟩
        · rw [← hxv]; decide
        · simp [branchOnly, Ne.symm hyw]
    · by_cases hxw : threeTwoPHPVar10 = w
      · by_cases hyv : threeTwoPHPVar11 = v
        · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨hyv.symm, hxw.symm⟩)))) hpair
        · refine ⟨branchOnly threeTwoPHPVar11, ?_, ?_, by decide⟩
          · simp [branchOnly, Ne.symm hyv]
          · rw [← hxw]; decide
      · refine ⟨branchOnly threeTwoPHPVar10, ?_, ?_, by decide⟩
        · simp [branchOnly, Ne.symm hxv]
        · simp [branchOnly, Ne.symm hxw]
  case pigeon2 =>
    by_cases hxv : threeTwoPHPVar20 = v
    · by_cases hyw : threeTwoPHPVar21 = w
      · exact absurd
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hxv.symm, hyw.symm⟩))))) hpair
      · refine ⟨branchOnly threeTwoPHPVar21, ?_, ?_, by decide⟩
        · rw [← hxv]; decide
        · simp [branchOnly, Ne.symm hyw]
    · by_cases hxw : threeTwoPHPVar20 = w
      · by_cases hyv : threeTwoPHPVar21 = v
        · exact absurd
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hyv.symm, hxw.symm⟩))))) hpair
        · refine ⟨branchOnly threeTwoPHPVar21, ?_, ?_, by decide⟩
          · simp [branchOnly, Ne.symm hyv]
          · rw [← hxw]; decide
      · refine ⟨branchOnly threeTwoPHPVar20, ?_, ?_, by decide⟩
        · simp [branchOnly, Ne.symm hxv]
        · simp [branchOnly, Ne.symm hxw]
  all_goals exact ⟨fun _ => false, rfl, rfl, by decide⟩

/-- **Reusable generic adversary floor of three.**  If every constant answer is
invalid somewhere, every single query answered `false` leaves every answer
invalid somewhere on that branch, and — for an arbitrary adversary "partner"
relation on query variables — two queries answered `false`,`true` (partner
case) or `false`,`false` (non-partner case) also leave every answer invalid
somewhere on the corresponding branch, then a correct output-valued query tree
has worst-case depth at least three.  This is only generic query-tree
infrastructure for certificate search; it is not a Boolean PHP lower bound. -/
theorem queryTree_depth_ge_three_of_adversary {n : Nat} {α : Type}
    (Valid : Assignment n → α → Prop)
    (Partner : Fin n → Fin n → Prop)
    (T : QueryTree n α)
    (hT : ∀ a : Assignment n, Valid a (queryEval a T))
    (hLeaf : ∀ out : α, ∃ a : Assignment n, ¬ Valid a out)
    (hFalse : ∀ (out : α) (v : Fin n),
      ∃ a : Assignment n, a v = false ∧ ¬ Valid a out)
    (hPartner : ∀ (out : α) (v w : Fin n), Partner v w →
      ∃ a : Assignment n, a v = false ∧ a w = true ∧ ¬ Valid a out)
    (hNonPartner : ∀ (out : α) (v w : Fin n), ¬ Partner v w →
      ∃ a : Assignment n, a v = false ∧ a w = false ∧ ¬ Valid a out) :
    3 ≤ queryDepth T := by
  cases T with
  | leaf out =>
      rcases hLeaf out with ⟨a, ha⟩
      exact absurd (hT a) ha
  | node v t0 t1 =>
      have h2 : 2 ≤ queryDepth t0 := by
        cases t0 with
        | leaf out0 =>
            rcases hFalse out0 v with ⟨a, hav, hinv⟩
            have hval := hT a
            simp [queryEval, hav] at hval
            exact absurd hval hinv
        | node w s0 s1 =>
            cases s0 with
            | node w0 u0 u1 =>
                exact Nat.succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _))
                  (Nat.le_max_left _ _))
            | leaf out00 =>
                cases s1 with
                | node w1 u0 u1 =>
                    exact Nat.succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _))
                      (Nat.le_max_right _ _))
                | leaf out01 =>
                    by_cases hpair : Partner v w
                    · rcases hPartner out01 v w hpair with ⟨a, hav, haw, hinv⟩
                      have hval := hT a
                      simp [queryEval, hav, haw] at hval
                      exact absurd hval hinv
                    · rcases hNonPartner out00 v w hpair with ⟨a, hav, haw, hinv⟩
                      have hval := hT a
                      simp [queryEval, hav, haw] at hval
                      exact absurd hval hinv
      exact Nat.succ_le_succ (Nat.le_trans h2 (Nat.le_max_left _ _))

/-- **Concrete `3 × 2` bounded falsified-clause search-query depth floor of
three.**  Any output-valued query tree that always returns a falsified clause of
the fixed `3 × 2` view makes at least three queries in the worst case.  This is
only a bounded search/certificate result for the fixed `3 × 2` view; it is not a
Frege/PHP lower bound and not a positive Boolean depth floor for the identically
false unsatisfiable formula. -/
theorem threeTwoPHPFalsifiedClauseSearchDepthFloor_three
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hT : ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    3 ≤ queryDepth T :=
  queryTree_depth_ge_three_of_adversary
    ThreeTwoPHPFalsifiedClause.Valid pigeonPair T hT
    threeTwo_leaf_invalid
    (fun out v => threeTwo_falseBranch_invalid out v)
    (fun out v w h => threeTwo_partnerTrue_invalid out v w h)
    (fun out v w h => threeTwo_bothFalse_invalid out v w h)

/-- Non-vacuity: the floor of three applies to the concrete correct fixed tree,
whose depth is six. -/
theorem threeTwoPHPFalsifiedClauseQueryTree_depth_ge_three :
    3 ≤ queryDepth threeTwoPHPFalsifiedClauseQueryTree :=
  threeTwoPHPFalsifiedClauseSearchDepthFloor_three
    threeTwoPHPFalsifiedClauseQueryTree
    (threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector
      threeTwoPHPFalsifiedClauseQueryTree
      threeTwoPHPFalsifiedClauseQueryTree_evalSelector)

/-! ## S2066: general falsified-clause search depth-floor statement shape

The following statement shape names, for arbitrary output-valued search
problems over the ambient PHP variable space, what a search depth floor says.
It is only a statement shape plus its already-proved concrete instances; no
general floor for growing PHP families is stated or claimed.
-/

/-- Statement shape for a falsified-clause search depth floor over an ambient
variable space: every always-valid output-valued query tree has worst-case
query depth at least `floor`.  This is a `Prop`-valued shape, not a proved
general theorem. -/
def FalsifiedClauseSearchDepthFloorStatement (n : Nat) (Out : Type)
    (Valid : Assignment n → Out → Prop) (floor : Nat) : Prop :=
  ∀ T : QueryTree n Out,
    (∀ a : Assignment n, Valid a (queryEval a T)) →
    floor ≤ queryDepth T

/-- The `2 × 1` floor of two as an instance of the general statement shape. -/
theorem twoOnePHPFalsifiedClauseSearchDepthFloorStatement_two :
    FalsifiedClauseSearchDepthFloorStatement (Nat.succ (2 * 1))
      TwoOnePHPFalsifiedClause TwoOnePHPFalsifiedClause.Valid 2 :=
  twoOnePHPFalsifiedClauseSearchDepthFloor

/-- The `3 × 2` floor of three as an instance of the general statement shape.
This is the first non-trivial adversary-argument witness of the shape. -/
theorem threeTwoPHPFalsifiedClauseSearchDepthFloorStatement_three :
    FalsifiedClauseSearchDepthFloorStatement (Nat.succ (3 * 2))
      ThreeTwoPHPFalsifiedClause ThreeTwoPHPFalsifiedClause.Valid 3 :=
  threeTwoPHPFalsifiedClauseSearchDepthFloor_three

end RestrictedPHPFloor
end PvNP
