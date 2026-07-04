import PvNP.FormulaRecursiveDecomposition

/-!
# Recursive frontier gate layers

`FormulaRecursiveDecomposition` records every raw-formula frontier level and
the terminal bottom layer. This module reifies each intermediate frontier as a
list of `GateSpec.dnf` gates using the existing truth-table/path-DNF fallback
from `FormulaTruthTableView`.

## HONEST SCOPE STATEMENT (read this)

* Every frontier level can now be viewed as a `GateSpec` list with exact
  formula alignment and count alignment.
* Intermediate levels use `formulaGate`, hence their switching DNF width is
  only bounded by the ambient variable count `n`. This is not the efficient
  intermediate-width theorem required for full frozen-form B4.
* The terminal full-depth level is still connected to the S2086 bottom layer,
  whose gates have width at most one.
* This module does not synthesize product/counting hypotheses, does not prove a
  generated-collapse theorem, and does not prove a global `t(d,s)` theorem from
  arbitrary syntax.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveGateLayers

open BoundedDepthFrege
open BoundedDepthLayerView
open FormulaTruthTableView
open FormulaRecursiveDepth
open FormulaDepthZeroBottom
open FormulaRecursiveDecomposition
open GeneratedGoodRestriction
open SwitchingLemmaStatement

/-! ## Level-wise frontier gate lists -/

/-- Reify the `k`-step recursive frontier as `GateSpec.dnf` gates through the
truth-table/path-DNF fallback. -/
def frontierGateList {n : Nat} (F : BDFormula n) (k : Nat) :
    List (GateSpec n) :=
  (formulaDepthFrontier k F).map formulaGate

theorem frontierGateList_length {n : Nat} (F : BDFormula n) (k : Nat) :
    (frontierGateList F k).length = (formulaDepthFrontier k F).length := by
  simp [frontierGateList]

theorem frontierGateList_formulas {n : Nat} (F : BDFormula n) (k : Nat) :
    (frontierGateList F k).map GateSpec.formula =
      formulaDepthFrontier k F := by
  simpa [frontierGateList] using
    map_formulaGate_formula (formulaDepthFrontier k F)

theorem frontierGateList_width_le_vars {n : Nat} (F : BDFormula n) (k : Nat) :
    forall g, g ∈ frontierGateList F k -> widthDNF g.theDNF <= n := by
  intro g hg
  rw [frontierGateList] at hg
  rcases List.mem_map.mp hg with ⟨child, _hchild, rfl⟩
  exact formulaGate_width_le_vars child

/-! ## Packaged frontier gate layers -/

/-- A `GateSpec` reification of one recursive frontier level.

The width field records the honest truth-table fallback bound `<= n`; the
terminal full-depth layer has a sharper width-one package below. -/
structure RecursiveFrontierGateLayer {n : Nat} (F : BDFormula n) (k : Nat) where
  gates : List (GateSpec n)
  formulas_eq : gates.map GateSpec.formula = formulaDepthFrontier k F
  gate_width_vars : forall g, g ∈ gates -> widthDNF g.theDNF <= n
  count_eq : gates.length = (formulaDepthFrontier k F).length

/-- Construct the packaged `GateSpec` reification of one recursive frontier
level. -/
def recursiveFrontierGateLayer {n : Nat} (F : BDFormula n) (k : Nat) :
    RecursiveFrontierGateLayer F k where
  gates := frontierGateList F k
  formulas_eq := frontierGateList_formulas F k
  gate_width_vars := frontierGateList_width_le_vars F k
  count_eq := frontierGateList_length F k

/-- All recursive frontier levels reified as gate lists, together with the
terminal bottom layer from S2086.

This structure intentionally separates intermediate truth-table layers from
the terminal width-one layer: it records the current structural surface and the
remaining efficient-width gap. -/
structure FullDepthRecursiveGateLayers {n : Nat} (F : BDFormula n) where
  layer : (k : Nat) -> RecursiveFrontierGateLayer F k
  transition :
    forall k,
      (layer (k + 1)).gates.map GateSpec.formula =
        ((layer k).gates.map GateSpec.formula).bind topChildren
  depthBudget :
    forall k child,
      child ∈ (layer k).gates.map GateSpec.formula -> depth child + k <= depth F
  terminalBottom : FullDepthFrontierBottomLayer F
  terminal_formulas_eq :
    terminalBottom.gates.map GateSpec.formula =
      (layer (depth F)).gates.map GateSpec.formula
  terminal_width :
    forall g, g ∈ terminalBottom.gates -> widthDNF g.theDNF <= 1

/-- Construct the full-depth recursive frontier gate-layer package from raw
syntax. -/
def fullDepthRecursiveGateLayers {n : Nat} (F : BDFormula n) :
    FullDepthRecursiveGateLayers F where
  layer := fun k => recursiveFrontierGateLayer F k
  transition := by
    intro k
    show (frontierGateList F (k + 1)).map GateSpec.formula =
      ((frontierGateList F k).map GateSpec.formula).bind topChildren
    rw [frontierGateList_formulas, frontierGateList_formulas]
    exact formulaDepthFrontier_succ_eq_bind_topChildren k F
  depthBudget := by
    intro k child hchild
    have hfront := hchild
    rw [(recursiveFrontierGateLayer F k).formulas_eq] at hfront
    exact formulaDepthFrontier_depth_add_le k F child hfront
  terminalBottom := fullDepthFrontierBottomLayer F
  terminal_formulas_eq := by
    rw [(recursiveFrontierGateLayer F (depth F)).formulas_eq]
    exact (fullDepthFrontierBottomLayer F).formulas_eq
  terminal_width := (fullDepthFrontierBottomLayer F).gate_width

theorem fullDepthRecursiveGateLayers_transition {n : Nat}
    (F : BDFormula n) (k : Nat) :
    (((fullDepthRecursiveGateLayers F).layer (k + 1)).gates.map
        GateSpec.formula) =
      (((fullDepthRecursiveGateLayers F).layer k).gates.map
        GateSpec.formula).bind topChildren :=
  (fullDepthRecursiveGateLayers F).transition k

theorem fullDepthRecursiveGateLayers_depthBudget {n : Nat}
    (F : BDFormula n) :
    forall k child,
      child ∈ ((fullDepthRecursiveGateLayers F).layer k).gates.map
          GateSpec.formula ->
        depth child + k <= depth F :=
  (fullDepthRecursiveGateLayers F).depthBudget

theorem fullDepthRecursiveGateLayers_level_width_le_vars {n : Nat}
    (F : BDFormula n) (k : Nat) :
    forall g, g ∈ ((fullDepthRecursiveGateLayers F).layer k).gates ->
      widthDNF g.theDNF <= n :=
  ((fullDepthRecursiveGateLayers F).layer k).gate_width_vars

theorem fullDepthRecursiveGateLayers_terminal_formulas {n : Nat}
    (F : BDFormula n) :
    (fullDepthRecursiveGateLayers F).terminalBottom.gates.map
        GateSpec.formula =
      ((fullDepthRecursiveGateLayers F).layer (depth F)).gates.map
        GateSpec.formula :=
  (fullDepthRecursiveGateLayers F).terminal_formulas_eq

theorem fullDepthRecursiveGateLayers_terminal_width {n : Nat}
    (F : BDFormula n) :
    forall g, g ∈ (fullDepthRecursiveGateLayers F).terminalBottom.gates ->
      widthDNF g.theDNF <= 1 :=
  (fullDepthRecursiveGateLayers F).terminal_width

end FormulaRecursiveGateLayers
end PvNP
