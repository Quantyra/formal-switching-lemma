import PvNP.FormulaRecursiveTerminalSchedule
import PvNP.FormulaRecursiveTerminalProfile
import PvNP.FormulaRecursiveClassProfile

/-!
# Terminal-aware class-envelope recursive frontier profiles

This module combines the terminal-aware recursive frontier selector with the
supplied class-size/class-width envelope route.  The result is intentionally
bounded: the class-size envelope `S`, terminal-aware width envelope `W`,
nonempty fanin condition, and ambient geometric entry inequality are all
hypotheses.

It does not synthesize formula classes, product/counting hypotheses, arbitrary
AC0 collapse, Frege/PHP lower bounds, NP/circuit lower bounds, automatic B4, or
P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveTerminalClassProfile

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
open FormulaRecursiveTerminalProfile
open FormulaRecursiveTerminalTree
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

/-! ## Terminal-aware class-depth final-tree payloads -/

open GeneratedRefinedIteratedCertificate in
/-- Final-tree payload for one terminal-aware recursive frontier level under
supplied class-size and terminal-aware width envelopes. -/
def TerminalAwareClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S : Nat -> Nat) (d rounds : Nat) (parent : ParentKind)
    (level : Nat) : Prop :=
  level <= d /\
  exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (terminalAwareFrontierLayer F level parent).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
    cert.stageBudgets = List.replicate (rounds + 1) 2 /\
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
        (rounds + 1)).map stageStars /\
    TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
        (rounds + 1)) /\
    exists T : DTree n, exists s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
      (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
      dtDepth T <= formulaClassDepthTreeBudget S d level s /\
      (forall a : Assignment n, Agree cert.finalComposed a ->
        dtEval a T = eval a (restrict cert.finalComposed
          (terminalAwareFrontierLayer F level parent).originalFormula))

open GeneratedRefinedIteratedCertificate in
/-- One terminal-aware frontier level exposes a final decision tree under
supplied class-size and terminal-aware width envelopes.

The supplied ambient inequality is consumed only through the concrete frontier
gate count and terminal-aware width budget; no class or width synthesis is
claimed. -/
theorem frontierLayer_geometricCollapseWithTerminalAwareClassDepthWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hk : level <= depth F)
    (hvars : 1 <= n)
    (hwLevel : terminalAwareFrontierWidthBudget F level <= W d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * W d) <= n) :
    TerminalAwareClassDepthFinalTreeAt F S d rounds parent level := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      terminalAwareFrontierWidthBudget F level)) (rounds + 1)
  let L := terminalAwareFrontierLayer F level parent
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using terminalAwareFrontierLayer_gateCount F level parent
  have hm : 1 <= frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= terminalAwareFrontierWidthBudget F level := by
    simpa [L] using
      terminalAwareFrontierLayer_width_le_budget F level parent
  have hw1 : 1 <= terminalAwareFrontierWidthBudget F level :=
    terminalAwareFrontierWidthBudget_pos F level hvars
  have hmClass : frontierLayerGateCount F level <= S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level) <= n :=
    geometricEntryBound_of_class_envelopes hmClass hwLevel hn
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hnLayer
  have hregL : RegimeFrom L.gates.length
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) sched.length sched :=
    formulaClassDepthTreeBudgetFrom F S d level hSize sched sched.length
  have htL : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (formulaClassDepthTreeBudget S d) sched (freeRestriction n) L
      (terminalAwareFrontierWidthBudget F level) hmL hwL hregL htL
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level))
  have htree' : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1) sched := by
    simpa [hcount, hlen] using htree
  have hbgeom :
      sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched] using geometricSchedule_budgets
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level))
  have hposSched : 0 < sched.length := by
    rw [hlen]
    exact Nat.succ_pos rounds
  have hsome := lastStage_isSome cert hposSched
  cases hlast : cert.lastStage with
  | none =>
      rw [hlast] at hsome
      simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLastLayer : m = L.gates.length :=
        lastStage_gateCount_of_stageGateCounts_replicate cert
          hgc T m s hlast
      have hmLast : m = frontierLayerGateCount F level := by
        rw [hcount] at hmLastLayer
        exact hmLastLayer
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      have hlastCount :
          cert.lastStage =
            some (T, frontierLayerGateCount F level, s) := by
        simpa [hcount] using hlast
      have hgcRounds :
          cert.stageGateCounts =
            List.replicate (rounds + 1) (frontierLayerGateCount F level) := by
        rw [hgc, hcount, hlen]
      have hdepthClass :
          dtDepth T <= formulaClassDepthTreeBudget S d level s := by
        exact Nat.le_trans hdepth
          (by
            simpa [formulaClassDepthTreeBudget, hcount] using
              Nat.mul_le_mul_right (s - 1) hmClass)
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, hlastCount, heval, hdepthClass, ?_⟩
      · exact hgcRounds
      · rw [hb, hbgeom]
      · simpa [sched, hlen] using hsc
      · simpa [sched] using htree'
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

open GeneratedRefinedIteratedCertificate in
/-- Uniform all-level terminal-aware class-envelope final-tree route under
supplied `S`, `W`, `NoEmptyFanins`, and ambient geometric entry inequality. -/
theorem allFrontierLayers_geometricCollapseWithTerminalAwareClassDepthWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hwLevel : forall level, level <= depth F ->
      terminalAwareFrontierWidthBudget F level <= W d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * W d) <= n) :
    forall level, level <= depth F ->
      TerminalAwareClassDepthFinalTreeAt F S d rounds parent level := by
  intro level hk
  exact
    frontierLayer_geometricCollapseWithTerminalAwareClassDepthWidth_noEmptyFanins_finalTree
      F S W d level rounds parent hDepth hSize hF hk hvars
      (hwLevel level hk) hn

open GeneratedRefinedIteratedCertificate in
/-- Truth-table-width fallback for all terminal-aware recursive frontier layers:
the supplied class-size envelope `S` is retained, while the width envelope is
instantiated by the ambient variable count `n`. -/
theorem allFrontierLayers_geometricCollapseWithTerminalAwareClassFixedWidth_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * n) <= n) :
    forall level, level <= depth F ->
      TerminalAwareClassDepthFinalTreeAt F S d rounds parent level := by
  exact
    allFrontierLayers_geometricCollapseWithTerminalAwareClassDepthWidth_noEmptyFanins_finalTree
      F S (fun _ => n) d rounds parent hDepth hSize hF hvars
      (by
        intro level _hk
        exact terminalAwareFrontierWidthBudget_le_vars F level hvars)
      hn

end FormulaRecursiveTerminalClassProfile
end PvNP
