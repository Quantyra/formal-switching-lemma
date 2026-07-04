import PvNP.ScheduledAutoCollapse

/-!
# Frozen-form product schedule synthesis

This module closes the next narrow Gate B bottleneck between the scheduled
route and the frozen-form B4 interface.  `ScheduledAutoCollapse.autoIteratedCollapse`
already consumes `ValidFrom`, a per-stage conjunction of closed-form arithmetic
beats.  Here we prove that those `ValidFrom` obligations follow from one
reusable product-style bound function `B` plus a companion tree-budget function
`t`.

The result is an interface theorem, not full frozen-form B4 closure:

* `B m w s d` is a single bad-restriction bound family, used for both the
  current refinement-space size `p` and the ambient space `n` at each stage.  If
  the raw closed-form bad count is bounded by `B` and `B` is smaller than the
  corresponding star-space size, the existing `BeatArith` inequality follows.
* `t d s` is carried as a per-stage tree-budget upper bound for the generated
  stage tree budget `m * (s - 1)`.  This module records and preserves that
  schedule fact; it does not prove a final global depth theorem for arbitrary
  AC0 formulas.
* The start layer remains supplied as a width-bounded `MinimalLayeredFormula`.
  No arbitrary layered decomposition, Frege/PHP lower bound, NP/circuit lower
  bound, arbitrary AC0 collapse, PHP switching lemma, or P-vs-NP claim is made.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FrozenProductSchedule

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open RestrictionComposition
open RefinedSubspace
open GeneratedOneStepDepthReduction
open GeneratedIteratedCollapseFinal
open GeneratedRefinedCollapse
open ScheduledAutoCollapse

/-! ## Stage arithmetic packaged through one product-bound family -/

/-- ASCII projection for the scheduled stage budget. -/
def stageS : ScheduleStage -> Nat
  | ScheduleStage.mk s _ => s

/-- ASCII projection for the scheduled stage star count. -/
def stageStars : ScheduleStage -> Nat
  | ScheduleStage.mk _ ell => ell

/-- The raw closed-form bad-count side of `BeatArith`, before comparison with
the target star space. -/
def rawBadCount (m p w : Nat) (st : ScheduleStage) : Nat :=
  match st with
  | ScheduleStage.mk s ell =>
      m * (Nat.choose p (ell - s) * 2 ^ (p - (ell - s)) * (8 * w) ^ s)

/-- The closed-form size of the target `ell`-star space. -/
def starSpace (p : Nat) (st : ScheduleStage) : Nat :=
  match st with
  | ScheduleStage.mk _ ell => Nat.choose p ell * 2 ^ (p - ell)

/-- A product-style beat certificate for one stage.  The single bound family
`B` first upper-bounds the raw bad count, then beats the target star space. -/
def ProductBeat
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (m p w depth : Nat) (st : ScheduleStage) : Prop :=
  rawBadCount m p w st <= B m w (stageS st) depth /\
    B m w (stageS st) depth < starSpace p st

/-- A product-style stage beat implies the existing closed-form `BeatArith`
obligation consumed by `ValidFrom`. -/
theorem productBeat_to_beatArith
    {B : Nat -> Nat -> Nat -> Nat -> Nat}
    {m p w depth : Nat} {st : ScheduleStage}
    (h : ProductBeat B m p w depth st) :
    BeatArith m p (stageS st) (stageStars st) w := by
  cases st with
  | mk s ell =>
      simpa [ProductBeat, rawBadCount, starSpace, stageS, stageStars, BeatArith]
        using Nat.lt_of_le_of_lt h.1 h.2

/-- Product-style validity of a numeric schedule.  It is a single recursive
schedule hypothesis in terms of the product-bound family `B`; the theorem below
turns it into the existing `ValidFrom` conjunction. -/
def ProductValidFrom
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (m n : Nat) : Nat -> Nat -> Nat -> List ScheduleStage -> Prop
  | _, _, _, [] => True
  | depth, w, p, st :: rest =>
      ProductBeat B m p w depth st /\
        ProductBeat B m n w depth st /\
          ProductValidFrom B m n (depth - 1) (stageS st - 1) (stageStars st) rest

/-- A per-stage `t(d,s)` tree-budget schedule fact.  This records the usual
stage tree budget `m * (s - 1)` against a supplied bound family `t`. -/
def StageTreeBudget (t : Nat -> Nat -> Nat)
    (m depth : Nat) (st : ScheduleStage) : Prop :=
  m * (stageS st - 1) <= t depth (stageS st)

/-- Tree-budget validity threaded over the same schedule depths as
`ProductValidFrom`. -/
def TreeBudgetFrom (t : Nat -> Nat -> Nat)
    (m : Nat) : Nat -> List ScheduleStage -> Prop
  | _, [] => True
  | depth, st :: rest =>
      StageTreeBudget t m depth st /\
        TreeBudgetFrom t m (depth - 1) rest

/-- The bounded frozen-product schedule hypothesis: product beats plus the
companion `t(d,s)` tree-budget facts. -/
structure FrozenProductHypothesis
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (t : Nat -> Nat -> Nat)
    (m n depth w p : Nat) (sched : List ScheduleStage) where
  productBeats : ProductValidFrom B m n depth w p sched
  treeBudget : TreeBudgetFrom t m depth sched

/-- Main product-to-schedule synthesis: a product-style schedule hypothesis
derives the exact `ValidFrom` side condition consumed by `autoIteratedCollapse`. -/
theorem productValidFrom_validFrom
    {B : Nat -> Nat -> Nat -> Nat -> Nat}
    {m n depth w p : Nat} {sched : List ScheduleStage}
    (h : ProductValidFrom B m n depth w p sched) :
    ValidFrom m n w p sched := by
  induction sched generalizing depth w p with
  | nil =>
      exact trivial
  | cons st rest ih =>
      cases st with
      | mk s ell =>
          rcases h with ⟨hbase, hambient, hrest⟩
          exact ⟨productBeat_to_beatArith hbase,
            productBeat_to_beatArith hambient, ih hrest⟩

/-- Projection form for the full frozen-product hypothesis. -/
theorem frozenProductHypothesis_validFrom
    {B : Nat -> Nat -> Nat -> Nat -> Nat}
    {t : Nat -> Nat -> Nat}
    {m n depth w p : Nat} {sched : List ScheduleStage}
    (h : FrozenProductHypothesis B t m n depth w p sched) :
    ValidFrom m n w p sched :=
  productValidFrom_validFrom h.productBeats

/-! ## Collapse theorem consuming the synthesized schedule -/

open GeneratedRefinedIteratedCertificate in
/-- **Frozen-product schedule synthesis theorem.**  A width-bounded start layer
plus one product-style schedule hypothesis (`B`) and one tree-budget schedule
hypothesis (`t`) is enough to invoke the existing schedule-driven automatic
collapse theorem.  The returned certificate has the same bookkeeping guarantees
as `autoIteratedCollapse`, and the `t(d,s)` schedule facts are preserved.

This is deliberately narrower than full frozen-form B4: the start layer and
numeric schedule are supplied, and this theorem proves only the
product-hypothesis-to-`ValidFrom` bridge plus certificate construction. -/
theorem autoIteratedCollapse_of_frozenProduct {n : Nat}
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (t : Nat -> Nat -> Nat)
    (sched : List ScheduleStage) (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat)
    (hw : forall g, g ∈ L.gates -> widthDNF g.theDNF <= w)
    (h : FrozenProductHypothesis B t L.gates.length n sched.length w
      (stars base) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n base
        L.originalFormula sched.length,
      cert.stageGateCounts = List.replicate sched.length L.gates.length /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom t L.gates.length sched.length sched := by
  obtain ⟨cert, hgc, hb, hsc⟩ :=
    ScheduledAutoCollapse.autoIteratedCollapse sched base L w hw
      (frozenProductHypothesis_validFrom h)
  refine ⟨cert, hgc, ?_, ?_, h.treeBudget⟩
  · simpa [stageS] using hb
  · simpa [stageStars] using hsc

/-! ## A small non-vacuity witness for the interface -/

/-- The smallest product-bound family used by the one-stage witness. -/
def oneStageB : Nat -> Nat -> Nat -> Nat -> Nat :=
  fun _ _ _ _ => 0

/-- The smallest tree-budget family used by the one-stage witness. -/
def oneStageT : Nat -> Nat -> Nat :=
  fun _ _ => 0

/-- One degenerate-but-nonempty schedule: budget `1`, star count `1`. -/
def oneStageSchedule : List ScheduleStage :=
  [ScheduleStage.mk 1 1]

/-- The product hypothesis is inhabited for one stage with `m = 1`, ambient
space `n = 1`, entering width `0`, and `B = t = 0`.  The witness is intentionally
tiny and degenerate; it proves the interface is nonempty, not an asymptotic
collapse result. -/
def oneStageProductHypothesis_nonvacuous :
    FrozenProductHypothesis oneStageB oneStageT 1 1 1 0 1 oneStageSchedule := by
  refine ⟨?_, ?_⟩
  · unfold oneStageSchedule ProductValidFrom
    refine ⟨?_, ?_, trivial⟩
    · unfold ProductBeat rawBadCount starSpace stageS oneStageB
      exact ⟨by decide, by decide⟩
    · unfold ProductBeat rawBadCount starSpace stageS oneStageB
      exact ⟨by decide, by decide⟩
  · unfold oneStageSchedule TreeBudgetFrom
    refine ⟨?_, trivial⟩
    unfold StageTreeBudget stageS oneStageT
    decide

/-- A constant-true width-0 gate for the one-stage witness. -/
def oneStageTrueGate : GateSpec 1 :=
  GateSpec.dnf BDFormula.tru
    { D := ([[]] : DNF 1)
      sem_eq := by
        intro a
        simp [BoundedDepthFrege.eval, dnfEval, termEval]
      simple := by
        intro term hterm
        simp only [List.mem_singleton] at hterm
        subst hterm
        simp [SimpleTerm] }

/-- A nonempty start layer with one width-0 true gate. -/
def oneStageLayer : MinimalLayeredFormula 1 :=
  { parent := ParentKind.and
    gates := [oneStageTrueGate] }

theorem oneStageLayer_width :
    forall g, g ∈ oneStageLayer.gates -> widthDNF g.theDNF <= 0 := by
  intro g hg
  have hg' : g = oneStageTrueGate := by
    simpa [oneStageLayer] using hg
  subst hg'
  show widthDNF ([[]] : DNF 1) <= 0
  simp [widthDNF, termWidth]

open GeneratedRefinedIteratedCertificate in
/-- The frozen-product synthesis theorem has an actual one-stage certificate
instance.  This is a degenerate width-0 sanity witness only; it is not an
asymptotic family and not full frozen-form B4 closure. -/
theorem frozenProductSchedule_oneStage_nonvacuous :
    exists cert : GeneratedRefinedIteratedCertificate 1 (freeRestriction 1)
        oneStageLayer.originalFormula 1,
      cert.stageGateCounts = [1] /\
      cert.stageBudgets = [1] /\
      cert.stageStarCounts = [1] /\
      TreeBudgetFrom oneStageT 1 1 oneStageSchedule := by
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    autoIteratedCollapse_of_frozenProduct oneStageB oneStageT oneStageSchedule
      (freeRestriction 1) oneStageLayer 0 oneStageLayer_width
      oneStageProductHypothesis_nonvacuous
  refine ⟨cert, ?_, ?_, ?_, ht⟩
  · rw [hgc]
    rfl
  · rw [hb]
    rfl
  · rw [hsc]
    rfl

end FrozenProductSchedule
end PvNP
