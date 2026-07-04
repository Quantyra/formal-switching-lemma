import PvNP.FormulaDepthZeroBottom

/-!
# Recursive formula decomposition skeleton

`FormulaRecursiveDepth` exposes the repeated top-child frontier and proves its
raw-depth budget. `FormulaDepthZeroBottom` turns the full-depth frontier into
width-one-or-less bottom gates. This module packages those pieces into one
explicit structural skeleton: every frontier level, the transition from one
frontier to the next, the depth budget at every level, and the terminal bottom
layer.

## HONEST SCOPE STATEMENT (read this)

* This is recursive structural decomposition bookkeeping. It records the
  frontier layers and terminal bottom layer; it is not yet a generated collapse
  theorem.
* Intermediate child views are still only frontier formulas, not efficient
  `GateSpec` layers with synthesized product/counting hypotheses.
* It does not prove a full B4 theorem, does not derive a global product
  hypothesis, and does not prove a `t(d,s)` collapse theorem from arbitrary
  syntax.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveDecomposition

open BoundedDepthFrege
open BoundedDepthLayerView
open GeneratedGoodRestriction
open FormulaTruthTableView
open FormulaRecursiveDepth
open FormulaDepthZeroBottom
open SwitchingLemmaStatement

/-! ## Frontier transitions -/

/-- A `k+1` frontier is obtained from the `k` frontier by expanding every
surviving formula to its top children. -/
theorem depthFrontier_succ_eq_bind_topChildren {n : Nat} :
    forall (k : Nat) (roots : List (BDFormula n)),
      depthFrontier (k + 1) roots = (depthFrontier k roots).bind topChildren
  | 0, _roots => rfl
  | k + 1, roots => by
      simpa [depthFrontier] using
        depthFrontier_succ_eq_bind_topChildren k
          (roots.bind topChildren)

/-- Single-root form of the recursive frontier transition. -/
theorem formulaDepthFrontier_succ_eq_bind_topChildren {n : Nat}
    (k : Nat) (F : BDFormula n) :
    formulaDepthFrontier (k + 1) F =
      (formulaDepthFrontier k F).bind topChildren := by
  simpa [formulaDepthFrontier] using
    depthFrontier_succ_eq_bind_topChildren k ([F] : List (BDFormula n))

/-! ## Full-depth decomposition skeleton -/

/-- A full-depth recursive decomposition skeleton for a raw formula.

The skeleton records every frontier level and the terminal bottom layer.  It is
the structural data needed before a later B4 theorem can add efficient
intermediate views, product/counting hypotheses, and a collapse schedule. -/
structure FullDepthRecursiveDecomposition {n : Nat} (F : BDFormula n) where
  frontier : Nat -> List (BDFormula n)
  frontier_eq : forall k, frontier k = formulaDepthFrontier k F
  transition : forall k, frontier (k + 1) = (frontier k).bind topChildren
  depthBudget : forall k child, child ∈ frontier k -> depth child + k <= depth F
  terminalLayer : FullDepthFrontierBottomLayer F
  terminal_formulas_eq :
    terminalLayer.gates.map GateSpec.formula = frontier (depth F)
  terminal_width :
    forall g, g ∈ terminalLayer.gates -> widthDNF g.theDNF <= 1
  terminal_count : terminalLayer.gates.length = (frontier (depth F)).length

/-- Construct the full-depth recursive decomposition skeleton from raw syntax. -/
def fullDepthRecursiveDecomposition {n : Nat} (F : BDFormula n) :
    FullDepthRecursiveDecomposition F where
  frontier := fun k => formulaDepthFrontier k F
  frontier_eq := fun _k => rfl
  transition := fun k => formulaDepthFrontier_succ_eq_bind_topChildren k F
  depthBudget := fun k child hchild =>
    formulaDepthFrontier_depth_add_le k F child hchild
  terminalLayer := fullDepthFrontierBottomLayer F
  terminal_formulas_eq := by
    simpa [fullDepthFrontierBottomLayer] using
      fullDepthFrontierGateList_formulas F
  terminal_width := by
    simpa [fullDepthFrontierBottomLayer] using
      fullDepthFrontierGateList_width_le_one F
  terminal_count := by
    simpa [fullDepthFrontierBottomLayer] using
      fullDepthFrontierGateList_length F

theorem fullDepthRecursiveDecomposition_transition {n : Nat}
    (F : BDFormula n) (k : Nat) :
    (fullDepthRecursiveDecomposition F).frontier (k + 1) =
      ((fullDepthRecursiveDecomposition F).frontier k).bind topChildren :=
  (fullDepthRecursiveDecomposition F).transition k

theorem fullDepthRecursiveDecomposition_depthBudget {n : Nat}
    (F : BDFormula n) :
    forall k child,
      child ∈ (fullDepthRecursiveDecomposition F).frontier k ->
        depth child + k <= depth F :=
  (fullDepthRecursiveDecomposition F).depthBudget

theorem fullDepthRecursiveDecomposition_terminal_formulas {n : Nat}
    (F : BDFormula n) :
    (fullDepthRecursiveDecomposition F).terminalLayer.gates.map
        GateSpec.formula =
      (fullDepthRecursiveDecomposition F).frontier (depth F) :=
  (fullDepthRecursiveDecomposition F).terminal_formulas_eq

theorem fullDepthRecursiveDecomposition_terminal_width {n : Nat}
    (F : BDFormula n) :
    forall g, g ∈ (fullDepthRecursiveDecomposition F).terminalLayer.gates ->
      widthDNF g.theDNF <= 1 :=
  (fullDepthRecursiveDecomposition F).terminal_width

theorem fullDepthRecursiveDecomposition_terminal_count {n : Nat}
    (F : BDFormula n) :
    (fullDepthRecursiveDecomposition F).terminalLayer.gates.length =
      ((fullDepthRecursiveDecomposition F).frontier (depth F)).length :=
  (fullDepthRecursiveDecomposition F).terminal_count

end FormulaRecursiveDecomposition
end PvNP
