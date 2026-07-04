import PvNP.FormulaRecursiveSyntacticGlobal
import PvNP.FrozenDepthView

/-!
# Final-tree extraction for global syntactic recursive frontiers

`FormulaRecursiveSyntacticGlobal` gives generated refined certificates and a
`TreeBudgetFrom` witness under a supplied global formula-size envelope
`formulaSize F <= M`. This module exposes the actual last-stage decision tree
carried by those certificates and bounds its depth by the same global budget

  `t_M(d,s) = M * (s - 1)`.

## Honest scope

* The global formula-size envelope `formulaSize F <= M` is still supplied for
  the global-envelope wrapper; the formula-local corollaries specialize it to
  `M = formulaSize F`.
* Root `syntacticFormulaSimpleDNF F`, `NoEmptyFanins F`, and the ambient bound
  in `M` or `formulaSize F` are still supplied.
* This extracts the final generated tree for the current syntactic frontier
  route; it does not synthesize product/counting hypotheses, ratio
  regimes, arbitrary normalization, full frozen-form B4, a PHP switching
  lemma, a Frege/PHP lower bound, an NP/circuit lower bound, or a P-vs-NP
  claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticGlobalTree

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticGlobal
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
open GeneratedRefinedIteratedCertificate
open ScheduledAutoCollapse
open SwitchingLemmaStatement

open GeneratedRefinedIteratedCertificate in
/-- Single-level global-envelope syntactic frontier collapse, with the actual
last-stage decision tree exposed and bounded by `M * (s - 1)`. -/
theorem syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_finalTree_simpleNoEmptyFanins
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
          (rounds + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= globalFormulaSizeTreeBudget M level s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (syntacticFrontierMinimalLayer F level parent
              (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
                hSimple)).originalFormula)) := by
  match
    syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_simpleNoEmptyFanins
      F M level rounds parent hM hSimple hNoEmpty hk hn with
  | Exists.intro cert hcert =>
      have hgc := hcert.1
      have hb := hcert.2.1
      have hsc := hcert.2.2.1
      have ht := hcert.2.2.2
      let sched := geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level * formulaSize F))
        (rounds + 1)
      have hlen : sched.length = rounds + 1 := by
        simpa [sched] using geometricSchedule_length
          (frontierLayerGateCount F level) (rounds + 1)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
      have hpos : 0 < sched.length := by
        rw [hlen]
        exact Nat.succ_pos rounds
      have hgcLen : cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) := by
        simpa [hlen] using hgc
      have hsome := lastStage_isSome cert hpos
      cases hlast : cert.lastStage with
      | none =>
          rw [hlast] at hsome
          simp at hsome
      | some x =>
          let T : DTree n := x.1
          let m : Nat := x.2.1
          let s : Nat := x.2.2
          have hlastT : cert.lastStage = some (T, m, s) := by
            simpa [T, m, s] using hlast
          have hmLast : m = frontierLayerGateCount F level :=
            FrozenDepthView.lastStage_gateCount_of_stageGateCounts_replicate
              cert hgcLen T m s hlastT
          have hlast' :
              cert.lastStage =
                some (T, frontierLayerGateCount F level, s) := by
            simpa [hmLast] using hlastT
          have hspec := lastStage_spec cert T m s hlastT
          have heval := hspec.1
          have hdepth := hspec.2
          have hmGlobal : frontierLayerGateCount F level <= M :=
            Nat.le_trans (frontierLayerGateCount_le_formulaSize F level) hM
          have hdepthCount :
              dtDepth T <= frontierLayerGateCount F level * (s - 1) := by
            simpa [hmLast] using hdepth
          have hdepthGlobal :
              dtDepth T <= globalFormulaSizeTreeBudget M level s := by
            refine Nat.le_trans hdepthCount ?_
            simpa [globalFormulaSizeTreeBudget] using
              Nat.mul_le_mul_right (s - 1) hmGlobal
          refine Exists.intro cert ?_
          refine And.intro hgc ?_
          refine And.intro hb ?_
          refine And.intro hsc ?_
          refine And.intro ht ?_
          refine Exists.intro T ?_
          refine Exists.intro s ?_
          refine And.intro hlast' ?_
          refine And.intro heval ?_
          refine And.intro hdepthGlobal ?_
          intro a ha
          rw [heval a, finalFormula_restrict_eval cert a ha]

open GeneratedRefinedIteratedCertificate in
/-- All root-simple/no-empty recursive syntactic frontier levels expose a
last-stage decision tree bounded by the supplied global formula-size budget. -/
theorem allSyntacticFrontierLayers_geometricCollapseWithGlobalFormulaSize_finalTree_simpleNoEmptyFanins
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
            (rounds + 1)) /\
        exists T : DTree n, exists s : Nat,
          cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
          (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
          dtDepth T <= globalFormulaSizeTreeBudget M level s /\
          (forall a : Assignment n, Agree cert.finalComposed a ->
            dtEval a T = eval a (restrict cert.finalComposed
              (syntacticFrontierMinimalLayer F level parent
                (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
                  hSimple)).originalFormula)) := by
  intro level hk
  exact
    syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_finalTree_simpleNoEmptyFanins
      F M level rounds parent hM hSimple hNoEmpty hk hn

open GeneratedRefinedIteratedCertificate in
/-- Single-level formula-local syntactic frontier collapse, with the actual
last-stage decision tree exposed and bounded by `formulaSize F * (s - 1)`.

This discharges the external envelope parameter of the global wrapper by
specializing it to `M = formulaSize F`; it is still formula-local and still
requires the formula-size ambient bound. -/
theorem syntacticFrontierLayer_geometricCollapseWithFormulaSize_finalTree_simpleNoEmptyFanins_of_formulaSizeBound
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
          (rounds + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= recursiveFrontierSizeTreeBudget F level s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (syntacticFrontierMinimalLayer F level parent
              (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
                hSimple)).originalFormula)) := by
  match
    syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_finalTree_simpleNoEmptyFanins
      F (formulaSize F) level rounds parent (Nat.le_refl _)
      hSimple hNoEmpty hk hn with
  | Exists.intro cert hcert =>
      have hgc := hcert.1
      have hb := hcert.2.1
      have hsc := hcert.2.2.1
      have htGlobal := hcert.2.2.2.1
      rcases hcert.2.2.2.2 with
        ⟨T, s, hlast, heval, hdepthGlobal, hsem⟩
      have ht : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)) := by
        simpa [globalFormulaSizeTreeBudget, recursiveFrontierSizeTreeBudget]
          using htGlobal
      have hdepth : dtDepth T <= recursiveFrontierSizeTreeBudget F level s := by
        simpa [globalFormulaSizeTreeBudget, recursiveFrontierSizeTreeBudget]
          using hdepthGlobal
      exact
        ⟨cert, hgc, hb, hsc, ht, T, s, hlast, heval, hdepth, hsem⟩

open GeneratedRefinedIteratedCertificate in
/-- All root-simple/no-empty recursive syntactic frontier levels expose a
last-stage decision tree bounded by the formula-local size budget
`formulaSize F * (s - 1)`. -/
theorem allSyntacticFrontierLayers_geometricCollapseWithFormulaSize_finalTree_simpleNoEmptyFanins_of_formulaSizeBound
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
            (rounds + 1)) /\
        exists T : DTree n, exists s : Nat,
          cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
          (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
          dtDepth T <= recursiveFrontierSizeTreeBudget F level s /\
          (forall a : Assignment n, Agree cert.finalComposed a ->
            dtEval a T = eval a (restrict cert.finalComposed
              (syntacticFrontierMinimalLayer F level parent
                (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
                  hSimple)).originalFormula)) := by
  intro level hk
  exact
    syntacticFrontierLayer_geometricCollapseWithFormulaSize_finalTree_simpleNoEmptyFanins_of_formulaSizeBound
      F level rounds parent hSimple hNoEmpty hk hn

end FormulaRecursiveSyntacticGlobalTree
end PvNP
