import PvNP.FormulaRecursiveNonempty

/-!
# Recursive frontier size bounds

The recursive frontier surface has a formula-local max-frontier tree budget:

  `t_F(d,s) = recursiveFrontierMaxGateCount F * (s - 1)`.

This module proves the next structural bound needed on the Gate B route: every
recursive frontier layer, and therefore the max frontier count, is bounded by
the raw formula size `formulaSize F`.

## HONEST SCOPE STATEMENT (read this)

* This is a structural count/budget bound only. It does not synthesize
  efficient width profiles; intermediate layers still use the truth-table
  fallback unless a separate width profile is supplied.
* Product/counting hypotheses, ratio regimes, and geometric entry-size
  inequalities remain supplied by callers.
* The resulting size-based budget is still formula-size dependent; it is not
  the final asymptotic B4 theorem with a fully discharged global `t(d,s)` for a
  formula class.
* It is not a PHP switching lemma, not a Frege/PHP lower bound, not an
  NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSizeBound

open BoundedDepthFrege
open FormulaTruthTableView
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveGlobalSchedule
open FrozenProductSchedule
open GeneratedIteratedCollapseFinal

/-! ## Size sums over formula lists -/

/-- Sum of raw formula sizes over a list of formulas. -/
def formulaSizeSum {n : Nat} (xs : List (BDFormula n)) : Nat :=
  (xs.map formulaSize).foldr (· + ·) 0

private theorem foldr_add_with_init (xs : List Nat) (init : Nat) :
    xs.foldr (· + ·) init = xs.foldr (· + ·) 0 + init := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc]

theorem formulaSize_pos {n : Nat} (F : BDFormula n) :
    1 <= formulaSize F := by
  cases F with
  | tru =>
      simp [formulaSize]
  | fls =>
      simp [formulaSize]
  | lit l =>
      simp [formulaSize]
  | and children =>
      rw [formulaSize_and]
      omega
  | or children =>
      rw [formulaSize_or]
      omega

theorem formulaSizeSum_append {n : Nat}
    (xs ys : List (BDFormula n)) :
    formulaSizeSum (xs ++ ys) = formulaSizeSum xs + formulaSizeSum ys := by
  induction xs with
  | nil =>
      simp [formulaSizeSum]
  | cons x xs ih =>
      change formulaSize x + formulaSizeSum (xs ++ ys) =
        (formulaSize x + formulaSizeSum xs) + formulaSizeSum ys
      rw [ih]
      omega

/-! ## Expanding top children never increases the size sum -/

theorem formulaSizeSum_topChildren_le {n : Nat} (F : BDFormula n) :
    formulaSizeSum (topChildren F) <= formulaSize F := by
  cases F with
  | tru =>
      simp [formulaSizeSum, topChildren, formulaSize]
  | fls =>
      simp [formulaSizeSum, topChildren, formulaSize]
  | lit l =>
      simp [formulaSizeSum, topChildren, formulaSize]
  | and children =>
      rw [formulaSize_and]
      simp [formulaSizeSum, topChildren]
  | or children =>
      rw [formulaSize_or]
      simp [formulaSizeSum, topChildren]

theorem formulaSizeSum_bind_topChildren_le {n : Nat} :
    forall roots : List (BDFormula n),
      formulaSizeSum (roots.bind topChildren) <= formulaSizeSum roots
  | [] => by
      simp [formulaSizeSum]
  | F :: rest => by
      calc
        formulaSizeSum ((F :: rest).bind topChildren)
            = formulaSizeSum (topChildren F) +
                formulaSizeSum (rest.bind topChildren) := by
              simp [formulaSizeSum_append]
        _ <= formulaSize F + formulaSizeSum rest :=
              Nat.add_le_add (formulaSizeSum_topChildren_le F)
                (formulaSizeSum_bind_topChildren_le rest)
        _ = formulaSizeSum (F :: rest) := by
              simp [formulaSizeSum]

theorem formulaSizeSum_depthFrontier_le {n : Nat} :
    forall (k : Nat) (roots : List (BDFormula n)),
      formulaSizeSum (depthFrontier k roots) <= formulaSizeSum roots
  | 0, roots => by
      simp [depthFrontier]
  | k + 1, roots => by
      have ih :
          formulaSizeSum (depthFrontier k (roots.bind topChildren)) <=
            formulaSizeSum (roots.bind topChildren) :=
        formulaSizeSum_depthFrontier_le k (roots.bind topChildren)
      exact Nat.le_trans (by simpa [depthFrontier] using ih)
        (formulaSizeSum_bind_topChildren_le roots)

/-! ## Frontier lengths and gate counts are size-bounded -/

theorem length_le_formulaSizeSum {n : Nat} :
    forall roots : List (BDFormula n),
      roots.length <= formulaSizeSum roots
  | [] => by
      simp [formulaSizeSum]
  | F :: rest => by
      have hF := formulaSize_pos F
      have hrest := length_le_formulaSizeSum rest
      have hsum : Nat.succ rest.length <= formulaSize F + formulaSizeSum rest := by
        omega
      simpa [formulaSizeSum] using hsum

theorem depthFrontier_length_le_formulaSizeSum {n : Nat}
    (k : Nat) (roots : List (BDFormula n)) :
    (depthFrontier k roots).length <= formulaSizeSum roots := by
  calc
    (depthFrontier k roots).length
        <= formulaSizeSum (depthFrontier k roots) :=
          length_le_formulaSizeSum (depthFrontier k roots)
    _ <= formulaSizeSum roots :=
          formulaSizeSum_depthFrontier_le k roots

theorem formulaDepthFrontier_length_le_formulaSize {n : Nat}
    (F : BDFormula n) (k : Nat) :
    (formulaDepthFrontier k F).length <= formulaSize F := by
  simpa [formulaDepthFrontier, formulaSizeSum] using
    depthFrontier_length_le_formulaSizeSum k [F]

theorem frontierLayerGateCount_le_formulaSize {n : Nat}
    (F : BDFormula n) (k : Nat) :
    frontierLayerGateCount F k <= formulaSize F := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  exact formulaDepthFrontier_length_le_formulaSize F k

private theorem foldr_max_le_of_all {xs : List Nat} {B : Nat}
    (h : forall x, x ∈ xs -> x <= B) :
    xs.foldr Nat.max 0 <= B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact (Nat.max_le).2 ⟨h x (List.mem_cons_self x xs),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

theorem recursiveFrontierMaxGateCount_le_formulaSize {n : Nat}
    (F : BDFormula n) :
    recursiveFrontierMaxGateCount F <= formulaSize F := by
  unfold recursiveFrontierMaxGateCount
  apply foldr_max_le_of_all
  intro count hcount
  rcases List.mem_map.mp hcount with ⟨k, _hk, rfl⟩
  exact frontierLayerGateCount_le_formulaSize F k

/-! ## Size-based tree budget -/

/-- Formula-size structural tree budget for every recursive frontier layer:
`t_F(d,s) = formulaSize F * (s - 1)`. -/
def recursiveFrontierSizeTreeBudget {n : Nat} (F : BDFormula n)
    (_depth s : Nat) : Nat :=
  formulaSize F * (s - 1)

theorem recursiveFrontierGlobalTreeBudget_le_sizeTreeBudget {n : Nat}
    (F : BDFormula n) (scheduleDepth s : Nat) :
    recursiveFrontierGlobalTreeBudget F scheduleDepth s <=
      recursiveFrontierSizeTreeBudget F scheduleDepth s := by
  simpa [recursiveFrontierGlobalTreeBudget, recursiveFrontierSizeTreeBudget]
    using Nat.mul_le_mul_right (s - 1)
      (recursiveFrontierMaxGateCount_le_formulaSize F)

private theorem treeBudgetFrom_constant_of_le {m M : Nat} (hm : m <= M) :
    forall (sched : List ScheduledAutoCollapse.ScheduleStage)
      (scheduleDepth : Nat),
      TreeBudgetFrom (fun _depth s => M * (s - 1)) m scheduleDepth sched
  | [], _ => trivial
  | st :: rest, scheduleDepth => by
      refine ⟨?_, treeBudgetFrom_constant_of_le hm rest
        (scheduleDepth - 1)⟩
      cases st with
      | mk s ell =>
          simpa [StageTreeBudget, stageS] using
            Nat.mul_le_mul_right (s - 1) hm

/-- The size-based structural tree budget satisfies every numeric schedule for
any recursive frontier layer. -/
theorem recursiveFrontierSizeTreeBudgetFrom {n : Nat}
    (F : BDFormula n) (k : Nat) :
    forall (sched : List ScheduledAutoCollapse.ScheduleStage)
      (scheduleDepth : Nat),
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F k) scheduleDepth sched := by
  intro sched scheduleDepth
  have hm := frontierLayerGateCount_le_formulaSize F k
  simpa [recursiveFrontierSizeTreeBudget] using
    treeBudgetFrom_constant_of_le
      (m := frontierLayerGateCount F k)
      (M := formulaSize F) hm sched scheduleDepth

/-- The same size-based structural tree budget also bounds the max-frontier
gate count itself. -/
theorem recursiveFrontierMaxSizeTreeBudgetFrom {n : Nat}
    (F : BDFormula n) :
    forall (sched : List ScheduledAutoCollapse.ScheduleStage)
      (scheduleDepth : Nat),
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (recursiveFrontierMaxGateCount F) scheduleDepth sched := by
  intro sched scheduleDepth
  have hm := recursiveFrontierMaxGateCount_le_formulaSize F
  simpa [recursiveFrontierSizeTreeBudget] using
    treeBudgetFrom_constant_of_le
      (m := recursiveFrontierMaxGateCount F)
      (M := formulaSize F) hm sched scheduleDepth

end FormulaRecursiveSizeBound
end PvNP
