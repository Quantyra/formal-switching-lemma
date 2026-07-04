import PvNP.FormulaDepthDecomposition

/-!
# Recursive raw-formula depth frontiers

`FormulaDepthDecomposition` proves a one-step peel: every top child exposed by
the positive-depth raw-formula `FrozenDepthView` synthesis is strictly
shallower than the original formula.  This module packages the recursive
frontier that repeatedly expands top children and proves that each expansion
spends one unit of raw-formula depth.

## HONEST SCOPE STATEMENT (read this)

* This is recursive structural bookkeeping for raw `BDFormula` syntax.
* It does not synthesize `FrozenDepthView` values at every level, does not
  build efficient bottom-layer DNF/CNF views, and does not synthesize product
  or counting hypotheses.
* The frontier may be empty, for example at empty fan-in gates.  The theorems
  are membership theorems for formulas that actually occur in the constructed
  frontier.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveDepth

open BoundedDepthFrege
open FormulaTruthTableView
open FormulaDepthDecomposition

/-! ## Recursive top-child frontier -/

/-- Expand a list of raw formulas by `k` repeated top-child steps. -/
def depthFrontier {n : Nat} : Nat -> List (BDFormula n) -> List (BDFormula n)
  | 0, roots => roots
  | k + 1, roots => depthFrontier k (roots.bind topChildren)

/-- The depth-`k` top-child frontier of a single raw formula. -/
def formulaDepthFrontier {n : Nat} (k : Nat) (F : BDFormula n) :
    List (BDFormula n) :=
  depthFrontier k [F]

/-! ## Depth budget for recursive frontiers -/

/-- A member of a `k`-step frontier has spent at least `k` units of depth from
some original root. -/
theorem depthFrontier_depth_add_le {n : Nat} :
    forall (k : Nat) (roots : List (BDFormula n)) (child : BDFormula n),
      child ∈ depthFrontier k roots ->
        ∃ root, root ∈ roots ∧ depth child + k <= depth root
  | 0, roots, child, hchild => by
      exact ⟨child, hchild, by simp⟩
  | k + 1, roots, child, hchild => by
      have ih := depthFrontier_depth_add_le k (roots.bind topChildren) child hchild
      rcases ih with ⟨mid, hmid, hdepth⟩
      rcases List.mem_bind.mp hmid with ⟨root, hroot, hmidroot⟩
      have hlt := topChildren_depth_lt root mid hmidroot
      exact ⟨root, hroot, by omega⟩

/-- Single-root form of the recursive frontier depth budget. -/
theorem formulaDepthFrontier_depth_add_le {n : Nat} (k : Nat)
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier k F) :
    depth child + k <= depth F := by
  have h := depthFrontier_depth_add_le k [F] child hchild
  rcases h with ⟨root, hroot, hdepth⟩
  simp only [List.mem_singleton] at hroot
  subst root
  exact hdepth

/-- Subtraction form of the single-root recursive frontier budget. -/
theorem formulaDepthFrontier_depth_le_sub {n : Nat} (k : Nat)
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier k F) :
    depth child <= depth F - k := by
  have h := formulaDepthFrontier_depth_add_le k F child hchild
  omega

/-- Any nonempty `k`-step frontier witnesses that `k` is within the root depth. -/
theorem formulaDepthFrontier_member_level_le_depth {n : Nat} (k : Nat)
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier k F) :
    k <= depth F := by
  have h := formulaDepthFrontier_depth_add_le k F child hchild
  omega

/-- At the full raw-formula depth, every surviving frontier member has depth
zero.  This is still only a frontier-membership theorem, not an efficient
bottom-layer synthesis theorem. -/
theorem formulaDepthFrontier_fullDepth_zero {n : Nat}
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier (depth F) F) :
    depth child = 0 := by
  have h := formulaDepthFrontier_depth_add_le (depth F) F child hchild
  omega

/-! ## Packaged recursive frontier -/

/-- A packaged recursive frontier with its raw-depth budget proof. -/
structure RecursiveDepthFrontier {n : Nat} (F : BDFormula n) (k : Nat) where
  frontier : List (BDFormula n)
  frontier_eq : frontier = formulaDepthFrontier k F
  depthBudget : forall child, child ∈ frontier -> depth child + k <= depth F

/-- Construct the recursive frontier package from raw syntax. -/
def recursiveDepthFrontier {n : Nat} (F : BDFormula n) (k : Nat) :
    RecursiveDepthFrontier F k where
  frontier := formulaDepthFrontier k F
  frontier_eq := rfl
  depthBudget := formulaDepthFrontier_depth_add_le k F

theorem recursiveDepthFrontier_depth_add_le {n : Nat}
    (F : BDFormula n) (k : Nat) :
    forall child, child ∈ (recursiveDepthFrontier F k).frontier ->
      depth child + k <= depth F :=
  (recursiveDepthFrontier F k).depthBudget

theorem recursiveDepthFrontier_fullDepth_zero {n : Nat}
    (F child : BDFormula n)
    (hchild : child ∈ (recursiveDepthFrontier F (depth F)).frontier) :
    depth child = 0 := by
  have h := recursiveDepthFrontier_depth_add_le F (depth F) child hchild
  omega

end FormulaRecursiveDepth
end PvNP
