import PvNP.FormulaRecursiveGlobalSchedule
import PvNP.FrozenProductScheduleRatio

/-!
# Recursive frontier layers with ratio-regime schedules

`FormulaRecursiveGlobalSchedule` routes recursive frontier and terminal layers
through the frozen-product schedule interface when product beats are supplied.
`FrozenProductScheduleRatio` proves those per-stage arithmetic beats from a
space-aware ratio-regime schedule.

This module connects the two surfaces for recursive frontier layers.

## HONEST SCOPE STATEMENT (read this)

* The ratio-regime schedule is still supplied, or generated only under an
  explicit numeric entry bound.
* Intermediate frontier layers still use the truth-table/path-DNF fallback
  width budget `n`.  The terminal layer uses width budget `1`.
* Nonempty gate counts are explicit hypotheses; recursive frontiers can be
  empty at empty fan-in gates.
* This is not full frozen-form B4, not an efficient asymptotic `t(d,s)`
  theorem, not a Gate A/PHP switching lemma, not a Frege/PHP lower bound, not
  an NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveRatioSchedule

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveGateLayers
open FormulaRecursiveLayerProfile
open FormulaRecursiveGlobalSchedule
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Ratio-regime consumers for recursive layers -/

open GeneratedRefinedIteratedCertificate in
/-- A recursive frontier layer can consume a supplied ratio-regime schedule
under the formula-local global tree budget.  The per-stage `BeatArith`
obligations are proved by `FrozenProductScheduleRatio`; the ratio regime
itself remains supplied. -/
theorem frontierLayer_ratioRegimeCollapseWithGlobalTreeBudget {n : Nat}
    (F : BDFormula n) (level : Nat) (p : ParentKind)
    (sched : List ScheduleStage)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (frontierLayerWidthBudget F level) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (frontierLayerMinimalLayer F level p).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  let L := frontierLayerMinimalLayer F level p
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using frontierLayerMinimalLayer_gateCount F level p
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, g ∈ L.gates ->
      widthDNF g.theDNF <= frontierLayerWidthBudget F level := by
    simpa [L] using frontierLayerMinimalLayer_width_le_budget F level p
  have hregL : RegimeFrom L.gates.length
      (frontierLayerWidthBudget F level) (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      (frontierLayerGateCount F level) sched.length sched :=
    recursiveFrontierGlobalTreeBudgetFrom F hk sched sched.length
  have htL : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (recursiveFrontierGlobalTreeBudget F) sched (freeRestriction n) L
      (frontierLayerWidthBudget F level) hmL hwL hregL htL
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using htree

open GeneratedRefinedIteratedCertificate in
/-- Terminal full-depth bottom-layer consumer for a supplied ratio-regime
schedule under the same formula-local global tree budget. -/
theorem terminalLayer_ratioRegimeCollapseWithGlobalTreeBudget {n : Nat}
    (F : BDFormula n) (p : ParentKind)
    (sched : List ScheduleStage)
    (hm : 1 <= frontierLayerGateCount F (depth F))
    (hreg : RegimeFrom (frontierLayerGateCount F (depth F))
      (terminalLayerWidthBudget F) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (terminalLayerMinimalLayer F p).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F (depth F)) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F (depth F)) sched.length sched := by
  let L := terminalLayerMinimalLayer F p
  have hcount : L.gates.length = frontierLayerGateCount F (depth F) := by
    simpa [L] using terminalLayerMinimalLayer_gateCount F p
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, g ∈ L.gates ->
      widthDNF g.theDNF <= terminalLayerWidthBudget F := by
    simpa [L] using terminalLayerMinimalLayer_width_le_budget F p
  have hregL : RegimeFrom L.gates.length
      (terminalLayerWidthBudget F) (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      (frontierLayerGateCount F (depth F)) sched.length sched :=
    terminalLayer_globalTreeBudgetFrom F sched sched.length
  have htL : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (recursiveFrontierGlobalTreeBudget F) sched (freeRestriction n) L
      (terminalLayerWidthBudget F) hmL hwL hregL htL
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using htree

open GeneratedRefinedIteratedCertificate in
/-- Uniform frontier form: every in-depth nonempty recursive frontier layer can
consume its supplied ratio-regime schedule. -/
theorem allFrontierLayers_ratioRegimeCollapseWithGlobalTreeBudget {n : Nat}
    (F : BDFormula n) (p : ParentKind)
    (sched : List ScheduleStage)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (frontierLayerWidthBudget F level) (stars (freeRestriction n)) sched) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (frontierLayerMinimalLayer F level p).originalFormula sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  intro level hk
  exact frontierLayer_ratioRegimeCollapseWithGlobalTreeBudget
    F level p sched hk (hm level hk) (hreg level hk)

/-! ## Geometric ratio schedules for recursive layers -/

open GeneratedRefinedIteratedCertificate in
/-- A recursive frontier layer can use the geometric ratio schedule under an
explicit entry-size inequality.  For intermediate layers this still uses the
truth-table fallback width budget, so the numeric hypothesis may be strong. -/
  theorem frontierLayer_geometricCollapseWithGlobalTreeBudget {n : Nat}
    (F : BDFormula n) (level rounds : Nat) (p : ParentKind)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hw1 : 1 <= frontierLayerWidthBudget F level)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        frontierLayerWidthBudget F level) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (frontierLayerMinimalLayer F level p).originalFormula
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            frontierLayerWidthBudget F level)) (rounds + 1)).length,
      cert.stageGateCounts =
        List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
      cert.stageBudgets = List.replicate (rounds + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            frontierLayerWidthBudget F level)) (rounds + 1)).map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            frontierLayerWidthBudget F level)) (rounds + 1)) := by
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      frontierLayerWidthBudget F level)) (rounds + 1)
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (frontierLayerWidthBudget F level) (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hn
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        frontierLayerWidthBudget F level))
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    frontierLayer_ratioRegimeCollapseWithGlobalTreeBudget
      F level p sched hk hm hreg
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc, hlen]
  · have hbgeom :
        sched.map stageS = List.replicate (rounds + 1) 2 := by
      simpa [sched] using geometricSchedule_budgets
        (frontierLayerGateCount F level) (rounds + 1)
        (n / (64 * frontierLayerGateCount F level *
          frontierLayerWidthBudget F level))
    simpa [hbgeom] using hb
  · simpa [sched] using hsc
  · simpa [sched, hlen] using ht

open GeneratedRefinedIteratedCertificate in
/-- Terminal full-depth bottom-layer geometric ratio schedule under an explicit
entry-size inequality.  Unlike intermediate layers, the terminal width budget
is the width-one bottom-layer budget. -/
  theorem terminalLayer_geometricCollapseWithGlobalTreeBudget {n : Nat}
    (F : BDFormula n) (rounds : Nat) (p : ParentKind)
    (hm : 1 <= frontierLayerGateCount F (depth F))
    (hn : 2 * (64 * frontierLayerGateCount F (depth F)) ^ rounds *
      (64 * frontierLayerGateCount F (depth F) *
        terminalLayerWidthBudget F) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (terminalLayerMinimalLayer F p).originalFormula
        (geometricSchedule (frontierLayerGateCount F (depth F))
          (n / (64 * frontierLayerGateCount F (depth F) *
            terminalLayerWidthBudget F)) (rounds + 1)).length,
      cert.stageGateCounts =
        List.replicate (rounds + 1)
          (frontierLayerGateCount F (depth F)) /\
      cert.stageBudgets = List.replicate (rounds + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (frontierLayerGateCount F (depth F))
          (n / (64 * frontierLayerGateCount F (depth F) *
            terminalLayerWidthBudget F)) (rounds + 1)).map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F (depth F)) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F (depth F))
          (n / (64 * frontierLayerGateCount F (depth F) *
            terminalLayerWidthBudget F)) (rounds + 1)) := by
  let sched := geometricSchedule (frontierLayerGateCount F (depth F))
    (n / (64 * frontierLayerGateCount F (depth F) *
      terminalLayerWidthBudget F)) (rounds + 1)
  have hw1 : 1 <= terminalLayerWidthBudget F := by
    simp [terminalLayerWidthBudget]
  have hreg : RegimeFrom (frontierLayerGateCount F (depth F))
      (terminalLayerWidthBudget F) (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hn
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F (depth F)) (rounds + 1)
      (n / (64 * frontierLayerGateCount F (depth F) *
        terminalLayerWidthBudget F))
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    terminalLayer_ratioRegimeCollapseWithGlobalTreeBudget
      F p sched hm hreg
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc, hlen]
  · have hbgeom :
        sched.map stageS = List.replicate (rounds + 1) 2 := by
      simpa [sched] using geometricSchedule_budgets
        (frontierLayerGateCount F (depth F)) (rounds + 1)
        (n / (64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F))
    simpa [hbgeom] using hb
  · simpa [sched] using hsc
  · simpa [sched, hlen] using ht

end FormulaRecursiveRatioSchedule
end PvNP
