import PvNP.FormulaRecursiveSizeBound

/-!
# Hypothesis-free recursive frontier count recurrence (S2180)

This module defines a structural count measure for raw formulas and proves that
it bounds every recursive frontier layer without a nonempty-fanin hypothesis.
OR and AND nodes use `max 1 (sum of child measures)`: the lower bound of one is
essential for empty fan-ins, whose level-zero frontier still contains the root.

This is structural count bookkeeping only. It is not full B4, a PHP switching
lemma, a Frege/PHP or circuit lower bound, Gate A, or a P-versus-NP result.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveFrontierCountRecurrence

open BoundedDepthFrege
open CNFModel
open FormulaTruthTableView
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveSizeBound
open GeneratedIteratedCollapseFinal

/-- Structural count measure for frontier budgets. Leaves contribute one.
OR/AND contribute `max 1` of the sum of their children, so empty fan-ins still
cover the root-level frontier of size one. -/
def formulaRecurrenceCount {n : Nat} : BDFormula n → Nat
  | .tru | .fls | .lit _ => 1
  | .or children | .and children =>
      Nat.max 1
        ((children.attach.map (fun f => formulaRecurrenceCount f.1)).foldr (· + ·) 0)
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

/-- The level-independent structural recurrence budget. -/
def formulaFrontierCountRecurrence {n : Nat} (F : BDFormula n)
    (_level : Nat) : Nat :=
  formulaRecurrenceCount F

/-- OR recurrence count with the `attach` erased. -/
theorem formulaRecurrenceCount_or {n : Nat} (children : List (BDFormula n)) :
    formulaRecurrenceCount (.or children) =
      Nat.max 1 ((children.map formulaRecurrenceCount).foldr (· + ·) 0) := by
  rw [show formulaRecurrenceCount (.or children) =
      Nat.max 1
        ((children.attach.map (fun f => formulaRecurrenceCount f.1)).foldr
          (· + ·) 0) from by rw [formulaRecurrenceCount]]
  rw [List.attach_map_val children formulaRecurrenceCount]

/-- AND recurrence count with the `attach` erased. -/
theorem formulaRecurrenceCount_and {n : Nat} (children : List (BDFormula n)) :
    formulaRecurrenceCount (.and children) =
      Nat.max 1 ((children.map formulaRecurrenceCount).foldr (· + ·) 0) := by
  rw [show formulaRecurrenceCount (.and children) =
      Nat.max 1
        ((children.attach.map (fun f => formulaRecurrenceCount f.1)).foldr
          (· + ·) 0) from by rw [formulaRecurrenceCount]]
  rw [List.attach_map_val children formulaRecurrenceCount]

theorem formulaRecurrenceCount_lit {n : Nat} (l : Literal n) :
    formulaRecurrenceCount (.lit l) = 1 := by
  simp only [formulaRecurrenceCount]

theorem formulaRecurrenceCount_tru {n : Nat} :
    formulaRecurrenceCount (.tru : BDFormula n) = 1 := by
  simp only [formulaRecurrenceCount]

theorem formulaRecurrenceCount_fls {n : Nat} :
    formulaRecurrenceCount (.fls : BDFormula n) = 1 := by
  simp only [formulaRecurrenceCount]

/-- Every recurrence count is positive, including empty OR/AND fan-ins. -/
theorem formulaRecurrenceCount_pos {n : Nat} (F : BDFormula n) :
    0 < formulaRecurrenceCount F := by
  cases F with
  | tru => rw [formulaRecurrenceCount]; exact Nat.zero_lt_one
  | fls => rw [formulaRecurrenceCount]; exact Nat.zero_lt_one
  | lit l => rw [formulaRecurrenceCount]; exact Nat.zero_lt_one
  | and children =>
      rw [formulaRecurrenceCount]
      exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  | or children =>
      rw [formulaRecurrenceCount]
      exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

private theorem foldr_add_map_le {α : Type _} (xs : List α) (f g : α → Nat)
    (h : ∀ x, x ∈ xs → f x ≤ g x) :
    (xs.map f).foldr (· + ·) 0 ≤ (xs.map g).foldr (· + ·) 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact Nat.add_le_add (h x (List.mem_cons_self x xs))
        (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- The structural recurrence never exceeds raw gate/leaf formula size. -/
theorem formulaRecurrenceCount_le_formulaSize {n : Nat} :
    ∀ F : BDFormula n, formulaRecurrenceCount F ≤ formulaSize F
  | .tru => by simp [formulaRecurrenceCount, formulaSize]
  | .fls => by simp [formulaRecurrenceCount, formulaSize]
  | .lit l => by simp [formulaRecurrenceCount, formulaSize]
  | .or children => by
      rw [formulaRecurrenceCount_or, formulaSize_or]
      have hsum := foldr_add_map_le children formulaRecurrenceCount formulaSize
        (fun G _ => formulaRecurrenceCount_le_formulaSize G)
      calc
        Nat.max 1 ((children.map formulaRecurrenceCount).foldr (· + ·) 0) ≤
            1 + (children.map formulaRecurrenceCount).foldr (· + ·) 0 := by
              exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
        _ ≤ 1 + (children.map formulaSize).foldr (· + ·) 0 :=
          Nat.add_le_add_left hsum 1
  | .and children => by
      rw [formulaRecurrenceCount_and, formulaSize_and]
      have hsum := foldr_add_map_le children formulaRecurrenceCount formulaSize
        (fun G _ => formulaRecurrenceCount_le_formulaSize G)
      calc
        Nat.max 1 ((children.map formulaRecurrenceCount).foldr (· + ·) 0) ≤
            1 + (children.map formulaRecurrenceCount).foldr (· + ·) 0 := by
              exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
        _ ≤ 1 + (children.map formulaSize).foldr (· + ·) 0 :=
          Nat.add_le_add_left hsum 1
  termination_by F => sizeOf F

/-- Sum of recurrence counts over a formula list. -/
def formulaRecurrenceCountSum {n : Nat} (xs : List (BDFormula n)) : Nat :=
  (xs.map formulaRecurrenceCount).foldr (· + ·) 0

private theorem formulaRecurrenceCountSum_append {n : Nat}
    (xs ys : List (BDFormula n)) :
    formulaRecurrenceCountSum (xs ++ ys) =
      formulaRecurrenceCountSum xs + formulaRecurrenceCountSum ys := by
  induction xs with
  | nil => simp [formulaRecurrenceCountSum]
  | cons x xs ih =>
      change formulaRecurrenceCount x + formulaRecurrenceCountSum (xs ++ ys) =
        (formulaRecurrenceCount x + formulaRecurrenceCountSum xs) +
          formulaRecurrenceCountSum ys
      rw [ih]
      omega

/-- Expanding one root to its top children does not increase recurrence mass. -/
theorem formulaRecurrenceCountSum_topChildren_le {n : Nat} (F : BDFormula n) :
    formulaRecurrenceCountSum (topChildren F) ≤ formulaRecurrenceCount F := by
  cases F with
  | tru => simp [formulaRecurrenceCountSum, topChildren, formulaRecurrenceCount]
  | fls => simp [formulaRecurrenceCountSum, topChildren, formulaRecurrenceCount]
  | lit l => simp [formulaRecurrenceCountSum, topChildren, formulaRecurrenceCount]
  | or children =>
      simp only [topChildren, formulaRecurrenceCountSum,
        formulaRecurrenceCount_or]
      exact Nat.le_max_right _ _
  | and children =>
      simp only [topChildren, formulaRecurrenceCountSum,
        formulaRecurrenceCount_and]
      exact Nat.le_max_right _ _

private theorem formulaRecurrenceCountSum_bind_topChildren_le {n : Nat} :
    ∀ roots : List (BDFormula n),
      formulaRecurrenceCountSum (roots.bind topChildren) ≤
        formulaRecurrenceCountSum roots
  | [] => by simp [formulaRecurrenceCountSum]
  | F :: rest => by
      calc
        formulaRecurrenceCountSum ((F :: rest).bind topChildren) =
            formulaRecurrenceCountSum (topChildren F) +
              formulaRecurrenceCountSum (rest.bind topChildren) := by
                simp [formulaRecurrenceCountSum_append]
        _ ≤ formulaRecurrenceCount F + formulaRecurrenceCountSum rest :=
          Nat.add_le_add (formulaRecurrenceCountSum_topChildren_le F)
            (formulaRecurrenceCountSum_bind_topChildren_le rest)
        _ = formulaRecurrenceCountSum (F :: rest) := by
          simp [formulaRecurrenceCountSum]

private theorem formulaRecurrenceCountSum_depthFrontier_le {n : Nat} :
    ∀ (level : Nat) (roots : List (BDFormula n)),
      formulaRecurrenceCountSum (depthFrontier level roots) ≤
        formulaRecurrenceCountSum roots
  | 0, roots => by simp [depthFrontier]
  | level + 1, roots => by
      have ih := formulaRecurrenceCountSum_depthFrontier_le level
        (roots.bind topChildren)
      exact Nat.le_trans (by simpa [depthFrontier] using ih)
        (formulaRecurrenceCountSum_bind_topChildren_le roots)

private theorem length_le_formulaRecurrenceCountSum {n : Nat} :
    ∀ roots : List (BDFormula n),
      roots.length ≤ formulaRecurrenceCountSum roots
  | [] => by simp [formulaRecurrenceCountSum]
  | F :: rest => by
      have hF := formulaRecurrenceCount_pos F
      have hrest := length_le_formulaRecurrenceCountSum rest
      have hsum : Nat.succ rest.length ≤
          formulaRecurrenceCount F + formulaRecurrenceCountSum rest := by
        omega
      simpa [formulaRecurrenceCountSum] using hsum

/-- Every raw recursive frontier count is bounded by the root recurrence,
without a nonempty-fanin or formula-class hypothesis. -/
theorem frontierLayerGateCount_le_formulaRecurrenceCount {n : Nat}
    (F : BDFormula n) (level : Nat) :
    frontierLayerGateCount F level ≤ formulaRecurrenceCount F := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  calc
    (formulaDepthFrontier level F).length ≤
        formulaRecurrenceCountSum (formulaDepthFrontier level F) :=
      length_le_formulaRecurrenceCountSum _
    _ ≤ formulaRecurrenceCountSum [F] := by
      simpa [formulaDepthFrontier] using
        formulaRecurrenceCountSum_depthFrontier_le level [F]
    _ = formulaRecurrenceCount F := by simp [formulaRecurrenceCountSum]

/-- Alias through the public level-indexed recurrence budget. -/
theorem frontierLayerGateCount_le_formulaFrontierCountRecurrence {n : Nat}
    (F : BDFormula n) (level : Nat) :
    frontierLayerGateCount F level ≤
      formulaFrontierCountRecurrence F level :=
  frontierLayerGateCount_le_formulaRecurrenceCount F level

/-- Pointwise chain from raw frontier count through recurrence to raw size. -/
theorem frontierLayerGateCount_le_formulaRecurrenceCount_le_formulaSize
    {n : Nat} (F : BDFormula n) (level : Nat) :
    frontierLayerGateCount F level ≤ formulaRecurrenceCount F ∧
      formulaRecurrenceCount F ≤ formulaSize F :=
  ⟨frontierLayerGateCount_le_formulaRecurrenceCount F level,
    formulaRecurrenceCount_le_formulaSize F⟩

/-- Pointwise chain using the level-indexed public recurrence name. -/
theorem frontierLayerGateCount_le_formulaFrontierCountRecurrence_le_formulaSize
    {n : Nat} (F : BDFormula n) (level : Nat) :
    frontierLayerGateCount F level ≤ formulaFrontierCountRecurrence F level ∧
      formulaFrontierCountRecurrence F level ≤ formulaSize F :=
  frontierLayerGateCount_le_formulaRecurrenceCount_le_formulaSize F level

end FormulaRecursiveFrontierCountRecurrence
end PvNP
