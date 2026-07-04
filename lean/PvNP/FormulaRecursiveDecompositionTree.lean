import PvNP.FormulaRecursiveClassDefault
import PvNP.FormulaRecursiveDecomposition

/-!
# Full-depth recursive decomposition with formula-size final trees

`FormulaRecursiveDecomposition` builds the raw full-depth frontier skeleton,
including the terminal width-one bottom layer.  `FormulaRecursiveClassDefault`
now supplies formula-local truth-table fallback final-tree consumers for every
recursive frontier level under `NoEmptyFanins`.

This module packages those two surfaces together: one synthesized full-depth
recursive decomposition skeleton plus all-level generated final-tree evidence
under the formula-size truth-table fallback route.

## Honest scope

* This is a structural packaging theorem, not full frozen-form B4.
* The final-tree route still uses truth-table fallback width `n`.
* The ambient formula-size geometric bound remains a hypothesis.
* Product/counting hypotheses, efficient width synthesis, formula-class
  envelopes, arbitrary normalization, and a discharged global asymptotic
  `t(d,s)` theorem remain open.
* It is not a PHP switching lemma, not a Frege/PHP lower bound, not an
  NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveDecompositionTree

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveClassDefault
open FormulaRecursiveDecomposition
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveWidthSchedule
open FormulaTruthTableView
open FrozenDepthView
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open GeneratedRefinedIteratedCertificate
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Formula-size truth-table final trees by recursive level -/

open GeneratedRefinedIteratedCertificate in
/-- Final-tree payload for one recursive frontier level under the formula-size
truth-table fallback route. -/
def FormulaSizeTruthTableFinalTreeAt {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind) (level : Nat) : Prop :=
  level <= d /\
  exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (frontierLayerMinimalLayer F level parent).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          (truthTableRecursiveWidthProfile F).widthBudget level))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
    cert.stageBudgets = List.replicate (rounds + 1) 2 /\
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          (truthTableRecursiveWidthProfile F).widthBudget level))
        (rounds + 1)).map stageStars /\
    TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          (truthTableRecursiveWidthProfile F).widthBudget level))
        (rounds + 1)) /\
    exists T : DTree n, exists s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
      (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
      dtDepth T <= recursiveFrontierSizeTreeBudget F level s /\
      (forall a : Assignment n, Agree cert.finalComposed a ->
        dtEval a T = eval a (restrict cert.finalComposed
          (frontierLayerMinimalLayer F level parent).originalFormula))

/-! ## Full-depth structural package -/

/-- A full-depth recursive decomposition together with formula-size truth-table
final-tree evidence for every in-depth recursive frontier level. -/
structure FullDepthFormulaSizeTruthTableTreePackage {n : Nat}
    (F : BDFormula n) (d rounds : Nat) (parent : ParentKind) where
  decomposition : FullDepthRecursiveDecomposition F
  terminal_formulas :
    decomposition.terminalLayer.gates.map GateSpec.formula =
      decomposition.frontier (depth F)
  terminal_width :
    forall g, g ∈ decomposition.terminalLayer.gates -> widthDNF g.theDNF <= 1
  finalTrees :
    forall level, level <= depth F ->
      FormulaSizeTruthTableFinalTreeAt F d rounds parent level

open GeneratedRefinedIteratedCertificate in
/-- Construct the full-depth recursive decomposition and attach all-level
formula-size truth-table final-tree evidence.

This is the current structural B4-facing package from raw syntax.  It combines
the synthesized recursive frontier skeleton and terminal bottom layer with the
formula-local truth-table fallback final-tree route; it still does not
synthesize efficient widths, product/counting hypotheses, or a formula-class
global `t(d,s)` theorem. -/
def fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_finalTreePackage
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    FullDepthFormulaSizeTruthTableTreePackage F d rounds parent := by
  refine
    { decomposition := fullDepthRecursiveDecomposition F
      terminal_formulas := ?_
      terminal_width := ?_
      finalTrees := ?_ }
  · exact (fullDepthRecursiveDecomposition F).terminal_formulas_eq
  · exact (fullDepthRecursiveDecomposition F).terminal_width
  · intro level hk
    simpa [FormulaSizeTruthTableFinalTreeAt] using
      allFrontierLayers_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_finalTree
        F d rounds parent hDepth hF hvars hn level hk

open GeneratedRefinedIteratedCertificate in
/-- Existence form of the full-depth structural package with formula-size
truth-table final-tree evidence at every in-depth recursive frontier level. -/
theorem exists_fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    Nonempty (FullDepthFormulaSizeTruthTableTreePackage F d rounds parent) := by
  exact ⟨
    fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_finalTreePackage
      F d rounds parent hDepth hF hvars hn⟩

end FormulaRecursiveDecompositionTree
end PvNP
