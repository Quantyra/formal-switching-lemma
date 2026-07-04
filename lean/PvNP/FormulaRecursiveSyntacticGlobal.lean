import PvNP.FormulaRecursiveSyntacticGeometric

/-!
# Global-envelope bounds for syntactic recursive frontiers

`FormulaRecursiveSyntacticGeometric` reduces the geometric syntactic frontier
route to one formula-local ambient bound in `formulaSize F`.  This module adds
the next B4-facing interface: if a formula class supplies a global size
envelope `formulaSize F <= M`, then the same root-simple/no-empty geometric
route can use a global tree budget

  `t_M(d,s) = M * (s - 1)`

and a single ambient bound in `M`.

## Honest scope

* The size envelope `formulaSize F <= M` is supplied.
* The root structural predicates `syntacticFormulaSimpleDNF F` and
  `NoEmptyFanins F` are still supplied.
* This does not synthesize product/counting hypotheses, ratio regimes, a
  formula-class envelope `M`, arbitrary normalization, full frozen-form B4, a
  PHP switching lemma, a Frege/PHP lower bound, an NP/circuit lower bound, or a
  P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticGlobal

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticGeometric
open FormulaRecursiveSyntacticLayer
open FormulaRecursiveSyntacticSimple
open FormulaSyntacticSimpleBridge
open FormulaTruthTableView
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Global formula-size budgets -/

/-- A supplied global formula-size tree budget:
`t_M(d,s) = M * (s - 1)`. -/
def globalFormulaSizeTreeBudget (M : Nat) (_depth s : Nat) : Nat :=
  M * (s - 1)

private theorem treeBudgetFrom_global_of_le {m M : Nat} (hm : m <= M) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (globalFormulaSizeTreeBudget M) m scheduleDepth sched
  | [], _ => trivial
  | st :: rest, scheduleDepth => by
      refine And.intro ?_ (treeBudgetFrom_global_of_le hm rest
        (scheduleDepth - 1))
      cases st with
      | mk s ell =>
          simpa [globalFormulaSizeTreeBudget, StageTreeBudget, stageS] using
            Nat.mul_le_mul_right (s - 1) hm

/-- A supplied formula-size envelope bounds every recursive frontier count
under the global tree budget. -/
theorem globalFormulaSizeTreeBudgetFrom {n : Nat}
    (F : BDFormula n) (M level : Nat) (hM : formulaSize F <= M) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (globalFormulaSizeTreeBudget M)
        (frontierLayerGateCount F level) scheduleDepth sched := by
  intro sched scheduleDepth
  have hm : frontierLayerGateCount F level <= M :=
    Nat.le_trans (frontierLayerGateCount_le_formulaSize F level) hM
  exact treeBudgetFrom_global_of_le hm sched scheduleDepth

/-! ## Global-envelope geometric entry bounds -/

/-- A global formula-size ambient bound implies the formula-local ambient bound
whenever `formulaSize F <= M`. -/
theorem formulaSizeGeometricAmbient_of_le_global {n : Nat}
    (F : BDFormula n) (M rounds : Nat)
    (hM : formulaSize F <= M)
    (hn : 2 * (64 * M) ^ rounds * (64 * M * M) <= n) :
    2 * (64 * formulaSize F) ^ rounds *
      (64 * formulaSize F * formulaSize F) <= n := by
  have h64 : 64 * formulaSize F <= 64 * M :=
    Nat.mul_le_mul_left 64 hM
  have hpow : (64 * formulaSize F) ^ rounds <=
      (64 * M) ^ rounds :=
    Nat.pow_le_pow_left h64 rounds
  have hright : 64 * formulaSize F * formulaSize F <=
      64 * M * M :=
    Nat.mul_le_mul h64 hM
  have hmul : (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * formulaSize F) <=
      (64 * M) ^ rounds * (64 * M * M) :=
    Nat.mul_le_mul hpow hright
  have hmain : 2 * ((64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * formulaSize F)) <=
      2 * ((64 * M) ^ rounds * (64 * M * M)) :=
    Nat.mul_le_mul_left 2 hmul
  calc
    2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * formulaSize F)
        = 2 * ((64 * formulaSize F) ^ rounds *
          (64 * formulaSize F * formulaSize F)) := by
            rw [Nat.mul_assoc]
    _ <= 2 * ((64 * M) ^ rounds * (64 * M * M)) := hmain
    _ = 2 * (64 * M) ^ rounds * (64 * M * M) := by
            rw [<- Nat.mul_assoc]
    _ <= n := hn

/-- Every recursive frontier layer satisfies the geometric entry bound from a
single global formula-size envelope and ambient bound. -/
theorem frontierLayer_geometricEntryBound_of_globalFormulaSize {n : Nat}
    (F : BDFormula n) (M level rounds : Nat)
    (hM : formulaSize F <= M)
    (hn : 2 * (64 * M) ^ rounds * (64 * M * M) <= n) :
    2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * formulaSize F) <= n :=
  frontierLayer_geometricEntryBound_of_formulaSize F level rounds
    (formulaSizeGeometricAmbient_of_le_global F M rounds hM hn)

/-! ## Geometric consumers under a supplied global formula-size envelope -/

open GeneratedRefinedIteratedCertificate in
/-- Single-level root-simple/no-empty geometric collapse under a supplied
global formula-size envelope and the global budget `M * (s - 1)`. -/
theorem syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (M level rounds : Nat) (parent : ParentKind)
    (hM : formulaSize F <= M)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F) (hk : level <= depth F)
    (hn : 2 * (64 * M) ^ rounds * (64 * M * M) <= n) :
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
      TreeBudgetFrom (globalFormulaSizeTreeBudget M)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)) := by
  match
    syntacticFrontierLayer_geometricCollapseWithFormulaSize_simpleNoEmptyFanins_of_formulaSizeBound
      F level rounds parent hSimple hNoEmpty hk
      (formulaSizeGeometricAmbient_of_le_global F M rounds hM hn) with
  | Exists.intro cert hcert =>
      exact Exists.intro cert
        (And.intro hcert.1
          (And.intro hcert.2.1
            (And.intro hcert.2.2.1
              (globalFormulaSizeTreeBudgetFrom F M level hM
                (geometricSchedule (frontierLayerGateCount F level)
                  (n / (64 * frontierLayerGateCount F level * formulaSize F))
                  (rounds + 1)) (rounds + 1)))))

open GeneratedRefinedIteratedCertificate in
/-- All recursive syntactic frontier levels consume the geometric route under
one supplied global formula-size envelope and global budget. -/
theorem allSyntacticFrontierLayers_geometricCollapseWithGlobalFormulaSize_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (M rounds : Nat) (parent : ParentKind)
    (hM : formulaSize F <= M)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F)
    (hn : 2 * (64 * M) ^ rounds * (64 * M * M) <= n) :
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
        TreeBudgetFrom (globalFormulaSizeTreeBudget M)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)) := by
  intro level hk
  exact
    syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_simpleNoEmptyFanins
      F M level rounds parent hM hSimple hNoEmpty hk hn

end FormulaRecursiveSyntacticGlobal
end PvNP
