import PvNP.FormulaTruthTableView

/-!
# Structural raw-formula schedules with global tree budgets

`FormulaTruthTableView` synthesizes a `FrozenDepthView` for every positive-depth
raw `BDFormula` by exposing its top `and`/`or` constructor and giving each child
the broad truth-table/path-DNF view.  `FrozenDepthView` then consumed only the
fixed geometric schedule.

This module connects that structural view surface to the ratio-regime schedule
machinery: any supplied `FrozenDepthView` whose bottom layer satisfies a width
bound and a ratio-regime schedule now yields a generated refined certificate
with an actual last-stage decision tree bounded by the global tree budget

  `t(d,s) = gateCount * (s - 1)`.

The positive-depth corollary removes the supplied start-layer obligation for
raw formulas whose top constructor is non-leaf.

## HONEST SCOPE STATEMENT (read this)

* This is still not full frozen-form B4.  The positive-depth raw formula route
  uses the truth-table/path-DNF child fallback; its generic width bound is only
  `<= n`, and the ratio-regime schedule hypotheses are still supplied.
* Leaves and constants still do not have an exact identity parent in
  `MinimalLayeredFormula`.
* This module proves a broader structural consumer with a global `t(d,s)` tree
  budget, not an efficient arbitrary AC0/`BDFormula` depth-`d` decomposition and
  not a synthesized product hypothesis.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower bound,
  NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a statement
  about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaStructuralSchedule

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open FrozenProductSchedule
open FrozenProductScheduleRatio
open FrozenDepthView
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open FormulaTruthTableView

/-- The constant gate-count tree budget `m * (s - 1)` satisfies every
numeric schedule. -/
theorem constantGateTreeBudget (m : Nat) :
    forall (sched : List ScheduleStage) (depth : Nat),
      TreeBudgetFrom (fun _depth s => m * (s - 1)) m depth sched
  | [], _ => trivial
  | st :: rest, depth => by
      refine ⟨?_, constantGateTreeBudget m rest (depth - 1)⟩
      cases st
      simp [StageTreeBudget, stageS]

/-- The frozen global tree budget `gateCount * (s - 1)` satisfies every
ratio-regime or numeric schedule, not just the geometric schedule used by the
earlier consumer theorem. -/
theorem schedule_frozenGlobalTreeBudget {n d : Nat} {F : BDFormula n}
    (V : FrozenDepthView n F d) :
    forall (sched : List ScheduleStage) (depth : Nat),
      TreeBudgetFrom (frozenGlobalTreeBudget V) V.gateCount depth sched
  | sched, depth => by
      simpa [frozenGlobalTreeBudget] using
        constantGateTreeBudget V.gateCount sched depth

open GeneratedRefinedIteratedCertificate in
/-- **Supplied frozen-view ratio-regime collapse with a global last-tree budget.**
For any nonempty ratio-regime schedule, a supplied frozen view yields a
generated refined certificate whose last-stage decision tree is bounded by the
global budget `t(d,s) = gateCount * (s - 1)`.

Compared with `FrozenDepthView.frozenDepthView_geometricCollapseWithGlobalTreeBudget`,
this theorem is no longer tied to the fixed geometric schedule; compared with
full B4, the view, width bound, and ratio-regime hypotheses are still supplied. -/
theorem frozenDepthView_ratioRegimeCollapseWithGlobalTreeBudget
    (sched : List ScheduleStage) (w : Nat) {n d : Nat} {F : BDFormula n}
    (V : FrozenDepthView n F d)
    (hm : 1 <= V.gateCount)
    (hw : forall g, g ∈ V.layer.gates -> widthDNF g.theDNF <= w)
    (hreg : RegimeFrom V.gateCount w (stars (freeRestriction n)) sched)
    (hd : 0 < sched.length) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        F sched.length,
      cert.stageGateCounts = List.replicate sched.length V.gateCount /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (frozenGlobalTreeBudget V) V.gateCount sched.length sched /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, V.gateCount, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= frozenGlobalTreeBudget V d s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed F)) := by
  have ht : TreeBudgetFrom (frozenGlobalTreeBudget V) V.gateCount
      sched.length sched :=
    schedule_frozenGlobalTreeBudget V sched sched.length
  obtain ⟨cert0, hgc0, hb0, hsc0, _ht0⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (frozenGlobalTreeBudget V) sched (freeRestriction n) V.layer w
      hm hw hreg ht
  let cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      F sched.length :=
    castFormula V.originalFormula_eq cert0
  have hgc : cert.stageGateCounts = List.replicate sched.length V.gateCount := by
    change (castFormula V.originalFormula_eq cert0).stageGateCounts =
      List.replicate sched.length V.gateCount
    rw [castFormula_stageGateCounts, hgc0]
    simp [FrozenDepthView.gateCount]
  have hb : cert.stageBudgets = sched.map stageS := by
    change (castFormula V.originalFormula_eq cert0).stageBudgets =
      sched.map stageS
    rw [castFormula_stageBudgets, hb0]
  have hsc : cert.stageStarCounts = sched.map stageStars := by
    change (castFormula V.originalFormula_eq cert0).stageStarCounts =
      sched.map stageStars
    rw [castFormula_stageStarCounts, hsc0]
  have hsome := lastStage_isSome cert hd
  cases hlast : cert.lastStage with
  | none =>
      rw [hlast] at hsome
      simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = V.gateCount :=
        FrozenDepthView.lastStage_gateCount_of_stageGateCounts_replicate
          cert hgc T m s hlast
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      refine ⟨cert, hgc, hb, hsc, ht, T, s, hlast, heval, ?_, ?_⟩
      · simpa [frozenGlobalTreeBudget] using hdepth
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

/-- A caller-supplied width bound over the immediate children of a
positive-depth formula transfers to the gates of the synthesized frozen view. -/
theorem positiveDepthFrozenDepthView_width_of_children {n : Nat}
    (F : BDFormula n) (hpos : 0 < depth F) (w : Nat)
    (hw : forall child, child ∈ topChildren F ->
      widthDNF (formulaDNFView child).D <= w) :
    forall g, g ∈ (positiveDepthFrozenDepthView F hpos).layer.gates ->
      widthDNF g.theDNF <= w := by
  cases F with
  | tru =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | fls =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | lit l =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | and children =>
      intro g hg
      change g ∈ children.map formulaGate at hg
      rcases List.mem_map.mp hg with ⟨child, hchild, rfl⟩
      exact hw child (by simpa [topChildren] using hchild)
  | or children =>
      intro g hg
      change g ∈ children.map formulaGate at hg
      rcases List.mem_map.mp hg with ⟨child, hchild, rfl⟩
      exact hw child (by simpa [topChildren] using hchild)

open GeneratedRefinedIteratedCertificate in
/-- **Positive-depth raw formula ratio-regime collapse with a global tree
budget.**  Any positive-depth raw formula is first structurally exposed at its
top `and`/`or` constructor, then routed through a ratio-regime schedule.  The
last-stage tree is bounded by

  `topChildCount F * (s - 1)`.

This removes the supplied `MinimalLayeredFormula` obligation for non-leaf raw
syntax while preserving the honest truth-table width and supplied-schedule
boundaries. -/
theorem positiveDepthFormula_ratioRegimeCollapseWithGlobalTreeBudget
    (sched : List ScheduleStage) (w : Nat) {n : Nat} (F : BDFormula n)
    (hpos : 0 < depth F)
    (hm : 1 <= topChildCount F)
    (hw : forall child, child ∈ topChildren F ->
      widthDNF (formulaDNFView child).D <= w)
    (hreg : RegimeFrom (topChildCount F) w (stars (freeRestriction n)) sched)
    (hd : 0 < sched.length) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        F sched.length,
      cert.stageGateCounts = List.replicate sched.length (topChildCount F) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom
        (fun _depth s => topChildCount F * (s - 1))
        (topChildCount F) sched.length sched /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, topChildCount F, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= topChildCount F * (s - 1) /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed F)) := by
  let V := positiveDepthFrozenDepthView F hpos
  have hlen : V.gateCount = topChildCount F :=
    positiveDepthFrozenDepthView_gateCount F hpos
  have hmV : 1 <= V.gateCount := by
    rw [hlen]
    exact hm
  have hwV : forall g, g ∈ V.layer.gates -> widthDNF g.theDNF <= w := by
    simpa [V] using positiveDepthFrozenDepthView_width_of_children F hpos w hw
  have hregV : RegimeFrom V.gateCount w (stars (freeRestriction n)) sched := by
    rw [hlen]
    exact hreg
  obtain ⟨cert, hgc, hb, hsc, _ht, T, s, hlast, heval, hdepth, hsem⟩ :=
    frozenDepthView_ratioRegimeCollapseWithGlobalTreeBudget
      sched w V hmV hwV hregV hd
  refine ⟨cert, ?_, hb, ?_, ?_, T, s, ?_, heval, ?_, hsem⟩
  · rw [hgc, hlen]
  · exact hsc
  · exact constantGateTreeBudget (topChildCount F) sched sched.length
  · rw [hlen] at hlast
    exact hlast
  · simpa [V, hlen, frozenGlobalTreeBudget] using hdepth

end FormulaStructuralSchedule
end PvNP
