import PvNP.FormulaRecursiveSyntacticLayer
import PvNP.FormulaRecursiveNonempty

/-!
# No-empty-fanin wrappers for syntactic recursive frontier layers

`FormulaRecursiveSyntacticLayer` routes structurally certified recursive
frontiers through syntactic-DNF child gates at width `formulaSize F`, but its
schedule consumers still require nonempty frontier gate counts.

This module composes that surface with the existing `NoEmptyFanins` machinery:
for every level `level <= depth F`, the nonempty-count hypothesis is synthesized
from raw syntax while the frontier simplicity predicate and ratio/geometric
schedule hypotheses remain supplied.

## Honest scope

* `FrontierSyntacticSimple` is still supplied for each target level.
* Ratio regimes and geometric entry-size inequalities are still supplied.
* Product/counting synthesis, arbitrary normalization, efficient depth-`d`
  decomposition, a global formula-class `t(d,s)` theorem, Gate A rung 4,
  Frege/PHP lower bounds, NP/circuit lower bounds, and P-vs-NP remain open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticNonempty

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticLayer
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open GeneratedIteratedCollapseFinal
open ScheduledAutoCollapse
open SwitchingLemmaStatement

open GeneratedRefinedIteratedCertificate in
/-- Single-level ratio-regime syntactic frontier collapse where the nonempty
gate-count hypothesis is synthesized from no-empty-fanin raw syntax. -/
theorem syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize_noEmptyFanins
    {n : Nat} (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hF : NoEmptyFanins F) (hk : level <= depth F)
    (hSimple : FrontierSyntacticSimple F level)
    (sched : List ScheduleStage)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (formulaSize F) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent hSimple).originalFormula
        sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  exact syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize
    F level parent hSimple sched
    (frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk)
    hreg

open GeneratedRefinedIteratedCertificate in
/-- Uniform ratio-regime syntactic frontier collapse where nonempty frontier
counts are synthesized from no-empty-fanin raw syntax. -/
theorem allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize_noEmptyFanins
    {n : Nat} (F : BDFormula n) (parent : ParentKind)
    (sched : List ScheduleStage)
    (hF : NoEmptyFanins F)
    (hSimple : forall level, level <= depth F ->
      FrontierSyntacticSimple F level)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (formulaSize F) (stars (freeRestriction n)) sched) :
    forall (level : Nat) (hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (hSimple level hk)).originalFormula sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  exact allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize
    F parent sched hSimple
    (fun level hk => frontierLayerGateCount_nonempty_of_noEmptyFanins
      F level hF hk)
    hreg

open GeneratedRefinedIteratedCertificate in
/-- Single-level geometric syntactic frontier collapse where the nonempty
gate-count hypothesis is synthesized from no-empty-fanin raw syntax. -/
theorem syntacticFrontierLayer_geometricCollapseWithFormulaSize_noEmptyFanins
    {n : Nat} (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (hF : NoEmptyFanins F) (hk : level <= depth F)
    (hSimple : FrontierSyntacticSimple F level)
    (hw1 : 1 <= formulaSize F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent hSimple).originalFormula
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)).length,
      cert.stageGateCounts =
        List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
      cert.stageBudgets = List.replicate (rounds + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)).map stageStars /\
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)) := by
  exact syntacticFrontierLayer_geometricCollapseWithFormulaSize
    F level rounds parent hSimple
    (frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk)
    hw1 hn

open GeneratedRefinedIteratedCertificate in
/-- Uniform geometric syntactic frontier collapse where nonempty frontier counts
are synthesized from no-empty-fanin raw syntax. -/
theorem allSyntacticFrontierLayers_geometricCollapseWithFormulaSize_noEmptyFanins
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (hF : NoEmptyFanins F)
    (hSimple : forall level, level <= depth F ->
      FrontierSyntacticSimple F level)
    (hw1 : 1 <= formulaSize F)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    forall (level : Nat) (hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (hSimple level hk)).originalFormula
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)).length,
        cert.stageGateCounts =
          List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
        cert.stageBudgets = List.replicate (rounds + 1) 2 /\
        cert.stageStarCounts =
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)).map stageStars /\
        TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)) := by
  intro level hk
  exact syntacticFrontierLayer_geometricCollapseWithFormulaSize_noEmptyFanins
    F level rounds parent hF hk (hSimple level hk) hw1 (hn level hk)

end FormulaRecursiveSyntacticNonempty
end PvNP
