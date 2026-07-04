import PvNP.FormulaRecursiveRatioSchedule

/-!
# Recursive frontier layers with supplied width profiles

`FormulaRecursiveRatioSchedule` routes recursive frontier layers through
ratio-regime schedules under the formula-local max-frontier tree budget, but
uses the truth-table fallback width budget `n` for intermediate layers.

This module isolates the next structural interface: callers may supply a
per-level width profile for the already-synthesized recursive frontier layers,
and the ratio/geometric schedule consumers use those supplied widths instead
of the fallback `n`.

## HONEST SCOPE STATEMENT (read this)

* The width profile is supplied.  This module does not synthesize efficient
  width bounds from arbitrary formulas.
* The recursive frontier layers, gate counts, and formula-local tree budget are
  the existing ones from `FormulaRecursiveGlobalSchedule`.
* Nonempty gate counts and ratio-regime or geometric entry-size hypotheses
  remain explicit.
* This is not full frozen-form B4, not an efficient asymptotic `t(d,s)`
  theorem, not a Gate A/PHP switching lemma, not a Frege/PHP lower bound, not
  an NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveWidthSchedule

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveGateLayers
open FormulaRecursiveLayerProfile
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveRatioSchedule
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Supplied recursive frontier width profiles -/

/-- A caller-supplied width budget for every recursive frontier layer.

The profile records only a width bound for the already-packaged frontier
layers.  It deliberately does not assert that the budget is efficient or that
it was synthesized from raw syntax. -/
structure RecursiveFrontierWidthProfile {n : Nat} (F : BDFormula n) where
  widthBudget : Nat -> Nat
  gate_width :
    forall k parent g,
      List.Mem g (frontierLayerMinimalLayer F k parent).gates ->
        widthDNF g.theDNF <= widthBudget k

/-- The existing truth-table fallback width profile, used as a baseline and a
compatibility witness for the older recursive ratio-schedule surface. -/
def truthTableRecursiveWidthProfile {n : Nat} (F : BDFormula n) :
    RecursiveFrontierWidthProfile F where
  widthBudget := frontierLayerWidthBudget F
  gate_width := by
    intro k parent g hg
    exact frontierLayerMinimalLayer_width_le_budget F k parent g hg

theorem truthTableRecursiveWidthProfile_widthBudget {n : Nat}
    (F : BDFormula n) (k : Nat) :
    (truthTableRecursiveWidthProfile F).widthBudget k =
      frontierLayerWidthBudget F k := rfl

/-! ## Ratio-regime consumers with supplied widths -/

open GeneratedRefinedIteratedCertificate in
/-- A recursive frontier layer can consume a supplied ratio-regime schedule
using a supplied width profile under the formula-local global tree budget. -/
theorem frontierLayer_ratioRegimeCollapseWithWidthProfile {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (sched : List ScheduleStage)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (profile.widthBudget level) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (frontierLayerMinimalLayer F level parent).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  let L := frontierLayerMinimalLayer F level parent
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using frontierLayerMinimalLayer_gateCount F level parent
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= profile.widthBudget level := by
    simpa [L] using profile.gate_width level parent
  have hregL : RegimeFrom L.gates.length
      (profile.widthBudget level) (stars (freeRestriction n)) sched := by
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
      (profile.widthBudget level) hmL hwL hregL htL
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using htree

open GeneratedRefinedIteratedCertificate in
/-- Uniform frontier form: every in-depth nonempty recursive frontier layer
can consume its supplied ratio-regime schedule at the supplied profile width. -/
theorem allFrontierLayers_ratioRegimeCollapseWithWidthProfile {n : Nat}
    (F : BDFormula n) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (sched : List ScheduleStage)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (profile.widthBudget level) (stars (freeRestriction n)) sched) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (frontierLayerMinimalLayer F level parent).originalFormula sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  intro level hk
  exact frontierLayer_ratioRegimeCollapseWithWidthProfile
    F level parent profile sched hk (hm level hk) (hreg level hk)

/-! ## Geometric ratio schedules with supplied widths -/

open GeneratedRefinedIteratedCertificate in
/-- A recursive frontier layer can use the named geometric ratio schedule at a
supplied profile width under the corresponding explicit entry-size bound. -/
theorem frontierLayer_geometricCollapseWithWidthProfile {n : Nat}
    (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hw1 : 1 <= profile.widthBudget level)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        profile.widthBudget level) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (frontierLayerMinimalLayer F level parent).originalFormula
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            profile.widthBudget level)) (rounds + 1)).length,
      cert.stageGateCounts =
        List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
      cert.stageBudgets = List.replicate (rounds + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            profile.widthBudget level)) (rounds + 1)).map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            profile.widthBudget level)) (rounds + 1)) := by
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      profile.widthBudget level)) (rounds + 1)
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (profile.widthBudget level) (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hn
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        profile.widthBudget level))
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    frontierLayer_ratioRegimeCollapseWithWidthProfile
      F level parent profile sched hk hm hreg
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc, hlen]
  · have hbgeom :
        sched.map stageS = List.replicate (rounds + 1) 2 := by
      simpa [sched] using geometricSchedule_budgets
        (frontierLayerGateCount F level) (rounds + 1)
        (n / (64 * frontierLayerGateCount F level *
          profile.widthBudget level))
    simpa [hbgeom] using hb
  · simpa [sched] using hsc
  · simpa [sched, hlen] using ht

open GeneratedRefinedIteratedCertificate in
/-- Uniform geometric form for all in-depth recursive frontier layers under a
supplied width profile and per-level entry-size bounds. -/
theorem allFrontierLayers_geometricCollapseWithWidthProfile {n : Nat}
    (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hw1 : forall level, level <= depth F ->
      1 <= profile.widthBudget level)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          profile.widthBudget level) <= n) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (frontierLayerMinimalLayer F level parent).originalFormula
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)).length,
        cert.stageGateCounts =
          List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
        cert.stageBudgets = List.replicate (rounds + 1) 2 /\
        cert.stageStarCounts =
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)).map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)) := by
  intro level hk
  exact frontierLayer_geometricCollapseWithWidthProfile
    F level rounds parent profile hk (hm level hk) (hw1 level hk) (hn level hk)

end FormulaRecursiveWidthSchedule
end PvNP
