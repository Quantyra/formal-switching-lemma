import PvNP.FormulaRecursiveTerminalProfile

/-!
# Terminal-aware recursive frontier schedules

`FormulaRecursiveTerminalProfile` gives one all-level terminal-aware layer
selector: the full-depth terminal level uses the width-one bottom layer, while
intermediate recursive frontier levels keep the truth-table fallback layer.
This module connects that selector back to the supplied schedule interfaces
under the formula-wide recursive frontier tree budget

  `t_F(depth, s) = recursiveFrontierMaxGateCount F * (s - 1)`.

## Honest scope

* This is a uniform schedule consumer for the already-synthesized
  terminal-aware recursive frontier layers.
* Intermediate layers still use fallback width `n`.
* Ratio regimes or geometric entry-size inequalities are still hypotheses.
* The tree budget is formula-local `t_F`, not a discharged global asymptotic
  `t(d,s)` theorem.
* It is not full B4, not a PHP switching lemma, not a Frege/PHP lower bound,
  not an NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveTerminalSchedule

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveTerminalProfile
open FrozenDepthView
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Formula-wide tree budget for terminal-aware layers -/

/-- The formula-wide recursive frontier tree budget applies to any
terminal-aware level, because the terminal-aware layer keeps the ordinary
recursive frontier gate count. -/
theorem terminalAwareFrontier_globalTreeBudgetFrom {n : Nat}
    (F : BDFormula n) {level : Nat} (hk : level <= depth F) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) scheduleDepth sched :=
  recursiveFrontierGlobalTreeBudgetFrom F hk

/-! ## Supplied ratio-regime schedules -/

open GeneratedRefinedIteratedCertificate in
/-- A terminal-aware recursive frontier layer can consume a supplied
ratio-regime schedule under the formula-local global tree budget.  At
`level = depth F` this uses the terminal width-one layer; at intermediate
levels it uses the truth-table fallback layer. -/
theorem terminalAwareFrontier_ratioRegimeCollapseWithGlobalTreeBudget
    {n : Nat} (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (sched : List ScheduleStage)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (terminalAwareFrontierLayer F level parent).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  let L := terminalAwareFrontierLayer F level parent
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using terminalAwareFrontierLayer_gateCount F level parent
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= terminalAwareFrontierWidthBudget F level := by
    simpa [L] using
      terminalAwareFrontierLayer_width_le_budget F level parent
  have hregL : RegimeFrom L.gates.length
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      (frontierLayerGateCount F level) sched.length sched :=
    terminalAwareFrontier_globalTreeBudgetFrom F hk sched sched.length
  have htL : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (recursiveFrontierGlobalTreeBudget F) sched (freeRestriction n) L
      (terminalAwareFrontierWidthBudget F level) hmL hwL hregL htL
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using htree

open GeneratedRefinedIteratedCertificate in
/-- Uniform all-level terminal-aware ratio-regime consumer. -/
theorem allFrontierLayers_ratioRegimeCollapseWithTerminalAwareGlobalTreeBudget
    {n : Nat} (F : BDFormula n) (parent : ParentKind)
    (sched : List ScheduleStage)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (terminalAwareFrontierWidthBudget F level)
        (stars (freeRestriction n)) sched) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (terminalAwareFrontierLayer F level parent).originalFormula
          sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  intro level hk
  exact terminalAwareFrontier_ratioRegimeCollapseWithGlobalTreeBudget
    F level parent sched hk (hm level hk) (hreg level hk)

/-! ## Geometric schedules -/

open GeneratedRefinedIteratedCertificate in
/-- A terminal-aware recursive frontier layer can consume the geometric ratio
schedule under an explicit terminal-aware entry-size inequality. -/
theorem terminalAwareFrontier_geometricCollapseWithGlobalTreeBudget
    {n : Nat} (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hw1 : 1 <= terminalAwareFrontierWidthBudget F level)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (terminalAwareFrontierLayer F level parent).originalFormula
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            terminalAwareFrontierWidthBudget F level)) (rounds + 1)).length,
      cert.stageGateCounts =
        List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
      cert.stageBudgets = List.replicate (rounds + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            terminalAwareFrontierWidthBudget F level)) (rounds + 1)).map
            stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            terminalAwareFrontierWidthBudget F level)) (rounds + 1)) := by
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      terminalAwareFrontierWidthBudget F level)) (rounds + 1)
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hn
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level))
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    terminalAwareFrontier_ratioRegimeCollapseWithGlobalTreeBudget
      F level parent sched hk hm hreg
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc, hlen]
  · have hbgeom :
        sched.map stageS = List.replicate (rounds + 1) 2 := by
      simpa [sched] using geometricSchedule_budgets
        (frontierLayerGateCount F level) (rounds + 1)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
    simpa [hbgeom] using hb
  · simpa [sched] using hsc
  · simpa [sched, hlen] using ht

open GeneratedRefinedIteratedCertificate in
/-- Uniform geometric form for all in-depth terminal-aware frontier layers
under per-level entry-size bounds. -/
theorem allFrontierLayers_geometricCollapseWithTerminalAwareGlobalTreeBudget
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hw1 : forall level, level <= depth F ->
      1 <= terminalAwareFrontierWidthBudget F level)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level) <= n) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (terminalAwareFrontierLayer F level parent).originalFormula
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              terminalAwareFrontierWidthBudget F level)) (rounds + 1)).length,
        cert.stageGateCounts =
          List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
        cert.stageBudgets = List.replicate (rounds + 1) 2 /\
        cert.stageStarCounts =
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              terminalAwareFrontierWidthBudget F level)) (rounds + 1)).map
              stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              terminalAwareFrontierWidthBudget F level)) (rounds + 1)) := by
  intro level hk
  exact terminalAwareFrontier_geometricCollapseWithGlobalTreeBudget
    F level rounds parent hk (hm level hk) (hw1 level hk) (hn level hk)

open GeneratedRefinedIteratedCertificate in
/-- No-empty-fanin corollary for the all-level terminal-aware geometric
consumer.  This removes only nonempty-count and positive-width bookkeeping; the
entry-size inequality is still supplied per level. -/
theorem allFrontierLayers_geometricCollapseWithTerminalAwareGlobalTreeBudget_noEmptyFanins
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level) <= n) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (terminalAwareFrontierLayer F level parent).originalFormula
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              terminalAwareFrontierWidthBudget F level)) (rounds + 1)).length,
        cert.stageGateCounts =
          List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
        cert.stageBudgets = List.replicate (rounds + 1) 2 /\
        cert.stageStarCounts =
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              terminalAwareFrontierWidthBudget F level)) (rounds + 1)).map
              stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              terminalAwareFrontierWidthBudget F level)) (rounds + 1)) := by
  exact
    allFrontierLayers_geometricCollapseWithTerminalAwareGlobalTreeBudget
      F rounds parent
      (fun level hk =>
        frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk)
      (fun level _hk =>
        terminalAwareFrontierWidthBudget_pos F level hvars)
      hn

end FormulaRecursiveTerminalSchedule
end PvNP
