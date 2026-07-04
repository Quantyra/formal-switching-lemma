import PvNP.FormulaRecursiveClassProfile
import PvNP.FormulaRecursiveNonempty

/-!
# Default recursive frontier class-width route

`FormulaRecursiveClassProfile` gives class-envelope final-tree wrappers for
arbitrary raw recursive frontier layers, but still asks callers to supply a
recursive width profile and nonempty frontier counts.  This module instantiates
that interface with the existing truth-table recursive width profile and uses
`NoEmptyFanins` to synthesize nonempty counts from raw syntax.

The resulting width is the honest fallback `n`, not an efficient structural
width.  The class-width envelope therefore still has to dominate `n`, and the
ambient geometric bound is stated against that supplied envelope.  This is a
raw-syntax compatibility wrapper, not full frozen-form B4.

## Honest scope

* The class-size envelope `S(d)` is supplied.
* The class-width envelope `W(d)` is supplied and must satisfy `n <= W(d)`.
  The fixed-width corollaries below specialize that envelope to `W(d)=n`.
* Width is the truth-table fallback `n`; this module does not synthesize an
  efficient width profile.
* `NoEmptyFanins F` is required to remove empty frontier-count cases.
* This does not synthesize product/counting hypotheses, ratio regimes,
  arbitrary normalization, full frozen-form B4, a PHP switching lemma,
  Frege/PHP lower bounds, NP/circuit lower bounds, or P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveClassDefault

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveClassProfile
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveWidthSchedule
open FormulaSyntacticClassGlobalTree
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

/-! ## Truth-table fallback class-width consumers -/

open GeneratedRefinedIteratedCertificate in
/-- Single raw recursive frontier layer under supplied class envelopes, using
the default truth-table fallback width profile.

This removes the caller-supplied `RecursiveFrontierWidthProfile` object and
the separate nonempty count hypothesis, but the fallback width is still `n` and
the class-width envelope must dominate it. -/
theorem frontierLayer_geometricCollapseWithTruthTableClassWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hk : level <= depth F)
    (hvars : 1 <= n)
    (hWidth : n <= W d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * W d) <= n) :
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
      TreeBudgetFrom (formulaClassDepthTreeBudget S d)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            (truthTableRecursiveWidthProfile F).widthBudget level))
          (rounds + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= formulaClassDepthTreeBudget S d level s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (frontierLayerMinimalLayer F level parent).originalFormula)) := by
  have hm : 1 <= frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk
  have hwLevel : (truthTableRecursiveWidthProfile F).widthBudget level <= W d := by
    simpa [truthTableRecursiveWidthProfile_widthBudget, frontierLayerWidthBudget]
      using hWidth
  have hw1 : 1 <= (truthTableRecursiveWidthProfile F).widthBudget level := by
    simpa [truthTableRecursiveWidthProfile_widthBudget, frontierLayerWidthBudget]
      using hvars
  exact
    frontierLayer_geometricCollapseWithClassDepthWidthProfile_finalTree
      F S W d level rounds parent (truthTableRecursiveWidthProfile F)
      hDepth hSize hk hm hwLevel hw1 hn

open GeneratedRefinedIteratedCertificate in
/-- Uniform all-level form of the truth-table fallback class-width consumer for
raw recursive frontier layers under `NoEmptyFanins`. -/
theorem allFrontierLayers_geometricCollapseWithTruthTableClassWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hWidth : n <= W d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * W d) <= n) :
    forall level, level <= depth F ->
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
        TreeBudgetFrom (formulaClassDepthTreeBudget S d)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              (truthTableRecursiveWidthProfile F).widthBudget level))
            (rounds + 1)) /\
        exists T : DTree n, exists s : Nat,
          cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
          (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
          dtDepth T <= formulaClassDepthTreeBudget S d level s /\
          (forall a : Assignment n, Agree cert.finalComposed a ->
            dtEval a T = eval a (restrict cert.finalComposed
              (frontierLayerMinimalLayer F level parent).originalFormula)) := by
  intro level hk
  exact
    frontierLayer_geometricCollapseWithTruthTableClassWidth_noEmptyFanins_finalTree
      F S W d level rounds parent hDepth hSize hF hk hvars hWidth hn

/-! ## Fixed fallback-width consumers -/

open GeneratedRefinedIteratedCertificate in
/-- Single raw recursive frontier layer with the truth-table fallback width
specialized as the class-width envelope `W(d)=n`.

This removes the caller-supplied class-width envelope from the default
truth-table route, but the ambient bound is correspondingly stated with the
fallback width `n`.  This is still not efficient width synthesis. -/
theorem frontierLayer_geometricCollapseWithTruthTableFixedWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hk : level <= depth F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * n) <= n) :
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
      TreeBudgetFrom (formulaClassDepthTreeBudget S d)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            (truthTableRecursiveWidthProfile F).widthBudget level))
          (rounds + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= formulaClassDepthTreeBudget S d level s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (frontierLayerMinimalLayer F level parent).originalFormula)) := by
  exact
    frontierLayer_geometricCollapseWithTruthTableClassWidth_noEmptyFanins_finalTree
      F S (fun _ => n) d level rounds parent hDepth hSize hF hk hvars
      (Nat.le_refl n) hn

open GeneratedRefinedIteratedCertificate in
/-- Uniform all-level fixed-width form of the truth-table fallback consumer.

The theorem fixes the class-width envelope to the fallback variable count `n`;
the remaining class-size envelope `S(d)` and ambient lower bound are still
supplied. -/
theorem allFrontierLayers_geometricCollapseWithTruthTableFixedWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * n) <= n) :
    forall level, level <= depth F ->
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
        TreeBudgetFrom (formulaClassDepthTreeBudget S d)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              (truthTableRecursiveWidthProfile F).widthBudget level))
            (rounds + 1)) /\
        exists T : DTree n, exists s : Nat,
          cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
          (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
          dtDepth T <= formulaClassDepthTreeBudget S d level s /\
          (forall a : Assignment n, Agree cert.finalComposed a ->
            dtEval a T = eval a (restrict cert.finalComposed
              (frontierLayerMinimalLayer F level parent).originalFormula)) := by
  intro level hk
  exact
    frontierLayer_geometricCollapseWithTruthTableFixedWidth_noEmptyFanins_finalTree
      F S d level rounds parent hDepth hSize hF hk hvars hn

end FormulaRecursiveClassDefault
end PvNP
