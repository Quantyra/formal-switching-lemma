import PvNP.FormulaRecursiveGateLayers

/-!
# Recursive frontier layer profiles

`FormulaRecursiveGateLayers` packages every recursive frontier as a gate layer
and records the terminal width-one bottom layer.  This module adds the narrow
structural-profile facts needed by the next Gate B bookkeeping step: level
gate counts, count transitions, honest width budgets, and per-level constant
tree-budget facts.

## HONEST SCOPE STATEMENT (read this)

* This is a structural profile over the already-defined recursive frontier
  layers. It does not build new frontier layers.
* Intermediate frontier layers still use the truth-table/path-DNF fallback, so
  their width budget is the ambient variable count `n`, not an efficient AC0
  bottom fan-in bound.
* The terminal full-depth layer keeps the existing width-one bottom witness.
* This is not full B4, does not synthesize product/counting hypotheses, and
  does not prove a global generated-collapse theorem for arbitrary formulas.
* Formula-collapse infrastructure only: NOT a Gate A/PHP switching lemma, NOT
  a Frege/PHP proof-size lower bound, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveLayerProfile

open BoundedDepthFrege
open BoundedDepthLayerView
open FormulaTruthTableView
open FormulaRecursiveDepth
open FormulaRecursiveDecomposition
open FormulaRecursiveGateLayers
open FormulaStructuralSchedule
open FrozenProductSchedule
open GeneratedGoodRestriction
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Frontier layer gate counts -/

/-- Gate count of the `k`-th recursive frontier layer. -/
def frontierLayerGateCount {n : Nat} (F : BDFormula n) (k : Nat) : Nat :=
  ((fullDepthRecursiveGateLayers F).layer k).gates.length

/-- The layer gate count agrees with the raw formula-depth frontier length. -/
theorem frontierLayerGateCount_eq_formulaDepthFrontier_length {n : Nat}
    (F : BDFormula n) (k : Nat) :
    frontierLayerGateCount F k = (formulaDepthFrontier k F).length := by
  simpa [frontierLayerGateCount] using
    ((fullDepthRecursiveGateLayers F).layer k).count_eq

/-- The zero-th frontier has the single root formula. -/
theorem frontierLayerGateCount_zero {n : Nat} (F : BDFormula n) :
    frontierLayerGateCount F 0 = 1 := by
  simp [frontierLayerGateCount_eq_formulaDepthFrontier_length,
    formulaDepthFrontier, depthFrontier]

/-- The next gate count is the length of the previous layer's top-child bind. -/
theorem frontierLayerGateCount_succ_eq_layer_bind_topChildren_length
    {n : Nat} (F : BDFormula n) (k : Nat) :
    frontierLayerGateCount F (k + 1) =
      ((((fullDepthRecursiveGateLayers F).layer k).gates.map
        GateSpec.formula).bind topChildren).length := by
  have hlen := congrArg List.length
    (fullDepthRecursiveGateLayers_transition F k)
  simpa [frontierLayerGateCount] using hlen

/-- Formula-frontier form of the next-layer count transition. -/
theorem frontierLayerGateCount_succ_eq_frontier_bind_topChildren_length
    {n : Nat} (F : BDFormula n) (k : Nat) :
    frontierLayerGateCount F (k + 1) =
      ((formulaDepthFrontier k F).bind topChildren).length := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length,
    formulaDepthFrontier_succ_eq_bind_topChildren]

/-- Length of a top-child bind as the sum of per-formula top-child counts. -/
theorem length_bind_topChildren_eq_sum_topChildCount {n : Nat}
    (frontier : List (BDFormula n)) :
    (frontier.bind topChildren).length =
      (frontier.map topChildCount).sum := by
  induction frontier with
  | nil =>
      simp
  | cons F rest ih =>
      simp [topChildCount, ih]

/-- The next gate count is the sum of top-child counts over the previous layer. -/
theorem frontierLayerGateCount_succ_eq_layer_topChildCount_sum
    {n : Nat} (F : BDFormula n) (k : Nat) :
    frontierLayerGateCount F (k + 1) =
      ((((fullDepthRecursiveGateLayers F).layer k).gates.map
        GateSpec.formula).map topChildCount).sum := by
  rw [frontierLayerGateCount_succ_eq_layer_bind_topChildren_length]
  exact length_bind_topChildren_eq_sum_topChildCount
    (((fullDepthRecursiveGateLayers F).layer k).gates.map GateSpec.formula)

/-- Raw-frontier form of the top-child-count sum transition. -/
theorem frontierLayerGateCount_succ_eq_frontier_topChildCount_sum
    {n : Nat} (F : BDFormula n) (k : Nat) :
    frontierLayerGateCount F (k + 1) =
      ((formulaDepthFrontier k F).map topChildCount).sum := by
  rw [frontierLayerGateCount_succ_eq_frontier_bind_topChildren_length]
  exact length_bind_topChildren_eq_sum_topChildCount (formulaDepthFrontier k F)

/-! ## Honest width budgets -/

/-- Honest intermediate frontier width budget: the truth-table fallback uses
the ambient variable count. -/
def frontierLayerWidthBudget {n : Nat} (_F : BDFormula n) (_k : Nat) : Nat :=
  n

/-- Honest terminal frontier width budget from the full-depth bottom layer. -/
def terminalLayerWidthBudget {n : Nat} (_F : BDFormula n) : Nat :=
  1

/-- Every gate in an intermediate recursive frontier layer satisfies the
ambient-variable width budget. -/
theorem frontierLayer_width_le_budget {n : Nat} (F : BDFormula n) (k : Nat) :
    forall g, g ∈ ((fullDepthRecursiveGateLayers F).layer k).gates ->
      widthDNF g.theDNF <= frontierLayerWidthBudget F k := by
  simpa [frontierLayerWidthBudget] using
    fullDepthRecursiveGateLayers_level_width_le_vars F k

/-- Every terminal bottom gate satisfies the width-one terminal budget. -/
theorem terminalLayer_width_le_budget {n : Nat} (F : BDFormula n) :
    forall g, g ∈ (fullDepthRecursiveGateLayers F).terminalBottom.gates ->
      widthDNF g.theDNF <= terminalLayerWidthBudget F := by
  simpa [terminalLayerWidthBudget] using
    fullDepthRecursiveGateLayers_terminal_width F

/-! ## Per-layer tree budgets -/

/-- Constant tree-budget profile for frontier layer `k`:
`t_k(depth, s) = frontierLayerGateCount F k * (s - 1)`. -/
def frontierLayerTreeBudget {n : Nat} (F : BDFormula n) (k : Nat)
    (_depth s : Nat) : Nat :=
  frontierLayerGateCount F k * (s - 1)

/-- The per-layer constant tree budget satisfies every numeric schedule. -/
theorem frontierLayer_treeBudgetFrom {n : Nat} (F : BDFormula n) (k : Nat) :
    forall (sched : List ScheduleStage) (depth : Nat),
      TreeBudgetFrom (frontierLayerTreeBudget F k)
        (frontierLayerGateCount F k) depth sched :=
  fun sched depth => by
    simpa [frontierLayerTreeBudget] using
      constantGateTreeBudget (frontierLayerGateCount F k) sched depth

end FormulaRecursiveLayerProfile
end PvNP
