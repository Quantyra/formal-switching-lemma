import PvNP.FormulaRecursiveSyntacticGlobalTree

/-!
# Depth-indexed class budgets for syntactic recursive frontier final trees

`FormulaRecursiveSyntacticGlobalTree` gives final-tree extraction under either
a supplied numeric envelope `M` or the formula-local envelope `formulaSize F`.
This module exposes the next B4-facing interface: a depth-indexed class-size
envelope `S(d)` and the corresponding class-budget profile

  `t(d,s) = S(d) * (s - 1)`.

The theorem still consumes a supplied size envelope `formulaSize F <= S(d)`,
root syntactic simplicity, no-empty fanins, and the same geometric ambient
bound.  It is a depth-indexed wrapper around the already proved syntactic
frontier route, not a synthesis theorem for `S`, product/counting hypotheses,
or arbitrary formula normalization.

## Honest scope

* The class-size envelope `S(d)` is supplied.
* Root `syntacticFormulaSimpleDNF F`, `NoEmptyFanins F`, `depth F <= d`, and
  the ambient bound in `S(d)` are supplied.
* The resulting `t(d,s)` is a theorem surface for this supplied envelope; this
  does not synthesize product/counting hypotheses, ratio regimes, arbitrary
  normalization, full frozen-form B4, a PHP switching lemma, a Frege/PHP lower
  bound, an NP/circuit lower bound, or a P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaSyntacticClassGlobalTree

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
open FormulaRecursiveSyntacticGlobalTree
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

/-! ## Depth-indexed class budget -/

/-- A supplied depth-indexed formula-class tree budget:
`t(d,s) = S(d) * (s - 1)`. -/
def formulaClassDepthTreeBudget (S : Nat -> Nat) (d : Nat)
    (_depth s : Nat) : Nat :=
  S d * (s - 1)

/-- A supplied class-size envelope bounds every recursive frontier count under
the depth-indexed class budget. -/
theorem formulaClassDepthTreeBudgetFrom {n : Nat}
    (F : BDFormula n) (S : Nat -> Nat) (d level : Nat)
    (hSize : formulaSize F <= S d) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (formulaClassDepthTreeBudget S d)
        (frontierLayerGateCount F level) scheduleDepth sched := by
  intro sched scheduleDepth
  simpa [formulaClassDepthTreeBudget, globalFormulaSizeTreeBudget] using
    globalFormulaSizeTreeBudgetFrom F (S d) level hSize sched scheduleDepth

/-- A recursive frontier level of a depth-`d` formula is itself no deeper than
the supplied class depth. -/
theorem frontierLevel_le_classDepth {n : Nat} (F : BDFormula n)
    {d level : Nat} (hDepth : depth F <= d) (hk : level <= depth F) :
    level <= d :=
  Nat.le_trans hk hDepth

/-! ## Final-tree consumers under a supplied depth-indexed envelope -/

open GeneratedRefinedIteratedCertificate in
/-- Single-level depth-indexed class-budget syntactic frontier collapse, with
the actual last-stage decision tree exposed and bounded by
`t(d,s)=S(d)*(s-1)`.

This is the supplied-envelope `t(d,s)` wrapper: the size envelope and ambient
bound are still hypotheses. -/
theorem syntacticFrontierLayer_geometricCollapseWithClassDepth_finalTree_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F) (hk : level <= depth F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n) :
    level <= d /\
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
      TreeBudgetFrom (formulaClassDepthTreeBudget S d)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= formulaClassDepthTreeBudget S d level s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (syntacticFrontierMinimalLayer F level parent
              (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
                hSimple)).originalFormula)) := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  match
    syntacticFrontierLayer_geometricCollapseWithGlobalFormulaSize_finalTree_simpleNoEmptyFanins
      F (S d) level rounds parent hSize hSimple hNoEmpty hk hn with
  | Exists.intro cert hcert =>
      have hgc := hcert.1
      have hb := hcert.2.1
      have hsc := hcert.2.2.1
      have htGlobal := hcert.2.2.2.1
      rcases hcert.2.2.2.2 with
        ⟨T, s, hlast, heval, hdepthGlobal, hsem⟩
      have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)) := by
        simpa [formulaClassDepthTreeBudget, globalFormulaSizeTreeBudget]
          using htGlobal
      have hdepth :
          dtDepth T <= formulaClassDepthTreeBudget S d level s := by
        simpa [formulaClassDepthTreeBudget, globalFormulaSizeTreeBudget]
          using hdepthGlobal
      exact ⟨cert, hgc, hb, hsc, ht, T, s, hlast, heval, hdepth, hsem⟩

open GeneratedRefinedIteratedCertificate in
/-- All root-simple/no-empty recursive syntactic frontier levels of a formula
with `depth F <= d` expose a final tree bounded by the supplied class budget
`t(d,s)=S(d)*(s-1)`. -/
theorem allSyntacticFrontierLayers_geometricCollapseWithClassDepth_finalTree_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n) :
    forall (level : Nat) (hk : level <= depth F),
      level <= d /\
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
        TreeBudgetFrom (formulaClassDepthTreeBudget S d)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level * formulaSize F))
            (rounds + 1)) /\
        exists T : DTree n, exists s : Nat,
          cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
          (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
          dtDepth T <= formulaClassDepthTreeBudget S d level s /\
          (forall a : Assignment n, Agree cert.finalComposed a ->
            dtEval a T = eval a (restrict cert.finalComposed
              (syntacticFrontierMinimalLayer F level parent
                (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
                  hSimple)).originalFormula)) := by
  intro level hk
  exact
    syntacticFrontierLayer_geometricCollapseWithClassDepth_finalTree_simpleNoEmptyFanins
      F S d level rounds parent hDepth hSize hSimple hNoEmpty hk hn

end FormulaSyntacticClassGlobalTree
end PvNP
