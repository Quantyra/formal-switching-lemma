import PvNP.FormulaRecursiveSyntacticNonempty

/-!
# Recursive syntactic frontier simplicity from root syntax

`FormulaRecursiveSyntacticLayer` consumes `FrontierSyntacticSimple F level` as
an explicit per-frontier hypothesis.  This module proves that the existing
structural predicate `syntacticFormulaSimpleDNF F` is hereditary along
`topChildren`, and therefore automatically supplies `FrontierSyntacticSimple`
for every recursive frontier level of `F`.

The resulting wrappers remove the per-level frontier-simplicity argument from
the formula-size syntactic frontier consumers.  The no-empty wrappers also
combine this with `NoEmptyFanins F`, removing the separate nonempty
gate-count hypothesis.

## Honest scope

* The root structural predicate `syntacticFormulaSimpleDNF F` is still a
  sufficient syntactic condition, not a normalization or completeness theorem.
* Ratio regimes and geometric entry-size inequalities remain supplied.
* Product/counting synthesis, efficient depth-`d` decomposition, a global
  formula-class `t(d,s)` theorem, Gate A rung 4, Frege/PHP lower bounds,
  NP/circuit lower bounds, and P-vs-NP remain open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticSimple

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticLayer
open FormulaRecursiveSyntacticNonempty
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

/-! ## Structural simplicity is hereditary along top children -/

theorem syntacticAndListSimpleDNF_mem {n : Nat} :
    forall (children : List (BDFormula n)) (child : BDFormula n),
      List.Mem child children ->
        syntacticAndListSimpleDNF children ->
          syntacticFormulaSimpleDNF child
  | [], _child, hmem, _hsimple => by
      cases hmem
  | F :: rest, child, hmem, hsimple => by
      rcases List.mem_cons.mp hmem with hchild | hrest
      · cases hchild
        exact hsimple.1
      · exact syntacticAndListSimpleDNF_mem rest child hrest hsimple.2.1

theorem syntacticOrListSimpleDNF_mem {n : Nat} :
    forall (children : List (BDFormula n)) (child : BDFormula n),
      List.Mem child children ->
        syntacticOrListSimpleDNF children ->
          syntacticFormulaSimpleDNF child
  | [], _child, hmem, _hsimple => by
      cases hmem
  | F :: rest, child, hmem, hsimple => by
      rcases List.mem_cons.mp hmem with hchild | hrest
      · cases hchild
        exact hsimple.1
      · exact syntacticOrListSimpleDNF_mem rest child hrest hsimple.2

theorem topChild_syntacticFormulaSimpleDNF {n : Nat}
    (F child : BDFormula n)
    (hF : syntacticFormulaSimpleDNF F)
    (hchild : List.Mem child (topChildren F)) :
    syntacticFormulaSimpleDNF child := by
  cases F with
  | tru =>
      cases hchild
  | fls =>
      cases hchild
  | lit l =>
      cases hchild
  | and children =>
      exact syntacticAndListSimpleDNF_mem children child
        (by simpa [topChildren] using hchild) hF
  | or children =>
      exact syntacticOrListSimpleDNF_mem children child
        (by simpa [topChildren] using hchild) hF

theorem depthFrontier_syntacticFormulaSimpleDNF {n : Nat} :
    forall (k : Nat) (roots : List (BDFormula n)),
      (forall G, List.Mem G roots -> syntacticFormulaSimpleDNF G) ->
        forall G, List.Mem G (depthFrontier k roots) ->
          syntacticFormulaSimpleDNF G
  | 0, _roots, hroots, G, hG => hroots G hG
  | k + 1, roots, hroots, G, hG => by
      have hnext : forall H,
          List.Mem H (roots.bind topChildren) ->
            syntacticFormulaSimpleDNF H := by
        intro H hH
        rcases List.mem_bind.mp hH with ⟨root, hroot, hHroot⟩
        exact topChild_syntacticFormulaSimpleDNF root H
          (hroots root hroot) hHroot
      exact depthFrontier_syntacticFormulaSimpleDNF k
        (roots.bind topChildren) hnext G hG

theorem frontierSyntacticSimple_of_syntacticFormulaSimpleDNF {n : Nat}
    (F : BDFormula n) (k : Nat)
    (hF : syntacticFormulaSimpleDNF F) :
    FrontierSyntacticSimple F k := by
  intro G hG
  have hroots : forall H, List.Mem H [F] -> syntacticFormulaSimpleDNF H := by
    intro H hH
    rcases List.mem_cons.mp hH with hHF | hnil
    · cases hHF
      exact hF
    · cases hnil
  exact depthFrontier_syntacticFormulaSimpleDNF k [F] hroots G hG

theorem allFrontierSyntacticSimple_of_syntacticFormulaSimpleDNF {n : Nat}
    (F : BDFormula n)
    (hF : syntacticFormulaSimpleDNF F) :
    forall level, level <= depth F -> FrontierSyntacticSimple F level := by
  intro level _hk
  exact frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF

/-! ## Formula-size consumers with synthesized frontier simplicity -/

open GeneratedRefinedIteratedCertificate in
theorem syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize_of_syntacticFormulaSimpleDNF
    {n : Nat} (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hF : syntacticFormulaSimpleDNF F)
    (sched : List ScheduleStage)
    (hm : 1 <= frontierLayerGateCount F level)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (formulaSize F) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent
          (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)).originalFormula
        sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  exact syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize
    F level parent
    (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)
    sched hm hreg

open GeneratedRefinedIteratedCertificate in
theorem allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize_of_syntacticFormulaSimpleDNF
    {n : Nat} (F : BDFormula n) (parent : ParentKind)
    (sched : List ScheduleStage)
    (hF : syntacticFormulaSimpleDNF F)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (formulaSize F) (stars (freeRestriction n)) sched) :
    forall (level : Nat) (_hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)).originalFormula
          sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  exact allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize
    F parent sched
    (fun level _hk =>
      frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)
    hm hreg

open GeneratedRefinedIteratedCertificate in
theorem syntacticFrontierLayer_geometricCollapseWithFormulaSize_of_syntacticFormulaSimpleDNF
    {n : Nat} (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (hF : syntacticFormulaSimpleDNF F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hw1 : 1 <= formulaSize F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent
          (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)).originalFormula
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
    F level rounds parent
    (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)
    hm hw1 hn

open GeneratedRefinedIteratedCertificate in
theorem allSyntacticFrontierLayers_geometricCollapseWithFormulaSize_of_syntacticFormulaSimpleDNF
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (hF : syntacticFormulaSimpleDNF F)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hw1 : 1 <= formulaSize F)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    forall (level : Nat) (_hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hF)).originalFormula
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
  exact syntacticFrontierLayer_geometricCollapseWithFormulaSize_of_syntacticFormulaSimpleDNF
    F level rounds parent hF (hm level hk) hw1 (hn level hk)

/-! ## No-empty consumers with synthesized frontier simplicity -/

open GeneratedRefinedIteratedCertificate in
theorem syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F) (hk : level <= depth F)
    (sched : List ScheduleStage)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (formulaSize F) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent
          (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)).originalFormula
        sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  exact syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize_noEmptyFanins
    F level parent hNoEmpty hk
    (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)
    sched hreg

open GeneratedRefinedIteratedCertificate in
theorem allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (parent : ParentKind)
    (sched : List ScheduleStage)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (formulaSize F) (stars (freeRestriction n)) sched) :
    forall (level : Nat) (_hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)).originalFormula
          sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  exact allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize_noEmptyFanins
    F parent sched hNoEmpty
    (fun level _hk =>
      frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)
    hreg

open GeneratedRefinedIteratedCertificate in
theorem syntacticFrontierLayer_geometricCollapseWithFormulaSize_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F) (hk : level <= depth F)
    (hw1 : 1 <= formulaSize F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent
          (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)).originalFormula
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
  exact syntacticFrontierLayer_geometricCollapseWithFormulaSize_noEmptyFanins
    F level rounds parent hNoEmpty hk
    (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)
    hw1 hn

open GeneratedRefinedIteratedCertificate in
theorem allSyntacticFrontierLayers_geometricCollapseWithFormulaSize_simpleNoEmptyFanins
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (hSimple : syntacticFormulaSimpleDNF F)
    (hNoEmpty : NoEmptyFanins F)
    (hw1 : 1 <= formulaSize F)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    forall (level : Nat) (hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hSimple)).originalFormula
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
  exact syntacticFrontierLayer_geometricCollapseWithFormulaSize_simpleNoEmptyFanins
    F level rounds parent hSimple hNoEmpty hk hw1 (hn level hk)

end FormulaRecursiveSyntacticSimple
end PvNP
