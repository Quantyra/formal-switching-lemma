import PvNP.FormulaRecursiveSyntacticSimple

/-!
# Formula-size geometric bounds for syntactic recursive frontiers

`FormulaRecursiveSyntacticSimple` removes the per-frontier simplicity
hypothesis from syntactic recursive frontier consumers, and its no-empty
wrappers remove the separate nonempty-count hypothesis.  The geometric
consumers still ask for a per-level entry-size inequality involving the actual
frontier gate count.

This module proves the next small schedule-synthesis step: since every
recursive frontier count is bounded by `formulaSize F`, one root
formula-size ambient lower bound implies the geometric entry-size inequality at
every frontier level.  The resulting all-frontier wrapper consumes only the
root structural-simple predicate, `NoEmptyFanins F`, and the single
formula-size ambient bound.

## Honest scope

* The formula must still satisfy the sufficient root structural predicate
  `syntacticFormulaSimpleDNF F` and `NoEmptyFanins F`.
* The ambient lower bound is still formula-size dependent:
  `2 * (64 * formulaSize F)^rounds * (64 * formulaSize F * formulaSize F) <= n`.
* This is not arbitrary normalization, product/counting synthesis, an
  efficient formula-class `t(d,s)` theorem, full frozen-form B4, a PHP
  switching lemma, a Frege/PHP lower bound, an NP/circuit lower bound, or a
  P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticGeometric

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticLayer
open FormulaRecursiveSyntacticSimple
open FormulaSyntacticSimpleBridge
open FormulaTruthTableView
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open GeneratedIteratedCollapseFinal
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Formula-size monotonicity for geometric entry bounds -/

/-- If a frontier count `m` is bounded by `formulaSize F`, then the single
formula-size geometric entry bound implies the entry bound for that frontier. -/
theorem geometricEntryBound_of_le_formulaSize {n : Nat}
    (F : BDFormula n) (m rounds : Nat)
    (hm : m <= formulaSize F)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
      (64 * formulaSize F * formulaSize F) <= n) :
    2 * (64 * m) ^ rounds * (64 * m * formulaSize F) <= n := by
  have h64 : 64 * m <= 64 * formulaSize F :=
    Nat.mul_le_mul_left 64 hm
  have hpow : (64 * m) ^ rounds <=
      (64 * formulaSize F) ^ rounds :=
    Nat.pow_le_pow_left h64 rounds
  have hright : 64 * m * formulaSize F <=
      64 * formulaSize F * formulaSize F :=
    Nat.mul_le_mul_right (formulaSize F) h64
  have hmul : (64 * m) ^ rounds * (64 * m * formulaSize F) <=
      (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * formulaSize F) :=
    Nat.mul_le_mul hpow hright
  have hmain : 2 * ((64 * m) ^ rounds *
      (64 * m * formulaSize F)) <=
      2 * ((64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * formulaSize F)) :=
    Nat.mul_le_mul_left 2 hmul
  calc
    2 * (64 * m) ^ rounds * (64 * m * formulaSize F)
        = 2 * ((64 * m) ^ rounds * (64 * m * formulaSize F)) := by
            rw [Nat.mul_assoc]
    _ <= 2 * ((64 * formulaSize F) ^ rounds *
          (64 * formulaSize F * formulaSize F)) := hmain
    _ = 2 * (64 * formulaSize F) ^ rounds *
          (64 * formulaSize F * formulaSize F) := by
            rw [← Nat.mul_assoc]
    _ <= n := hn

/-- The formula-size bound specializes to every recursive frontier gate count. -/
theorem frontierLayer_geometricEntryBound_of_formulaSize {n : Nat}
    (F : BDFormula n) (level rounds : Nat)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
      (64 * formulaSize F * formulaSize F) <= n) :
    2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * formulaSize F) <= n :=
  geometricEntryBound_of_le_formulaSize F (frontierLayerGateCount F level)
    rounds (frontierLayerGateCount_le_formulaSize F level) hn

/-! ## Geometric consumers with a single formula-size ambient bound -/

open GeneratedRefinedIteratedCertificate in
/-- Single-level syntactic recursive frontier geometric collapse from root
structural predicates and one formula-size ambient bound. -/
theorem syntacticFrontierLayer_geometricCollapseWithFormulaSize_simpleNoEmptyFanins_of_formulaSizeBound
    {n : Nat} (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F) (hk : level <= depth F)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
      (64 * formulaSize F * formulaSize F) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent
          (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
            hSimple)).originalFormula
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
  exact
    syntacticFrontierLayer_geometricCollapseWithFormulaSize_simpleNoEmptyFanins
      F level rounds parent hSimple hNoEmpty hk (formulaSize_pos F)
      (frontierLayer_geometricEntryBound_of_formulaSize F level rounds hn)

open GeneratedRefinedIteratedCertificate in
/-- All syntactic recursive frontier levels consume the named geometric
schedule from root structural predicates and one formula-size ambient bound. -/
theorem allSyntacticFrontierLayers_geometricCollapseWithFormulaSize_simpleNoEmptyFanins_of_formulaSizeBound
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
      (64 * formulaSize F * formulaSize F) <= n) :
    forall (level : Nat) (hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
              hSimple)).originalFormula
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
  exact
    syntacticFrontierLayer_geometricCollapseWithFormulaSize_simpleNoEmptyFanins_of_formulaSizeBound
      F level rounds parent hSimple hNoEmpty hk hn

end FormulaRecursiveSyntacticGeometric
end PvNP
