import PvNP.FrozenProductSchedule

/-!
# A concrete frozen-product schedule instantiation

This module instantiates `FrozenProductSchedule` with an explicit finite
product-bound family `B(m,w,s,d)` and tree-budget family `t(d,s)`.

The named regime is deliberately small and exact:

* `n = 17`;
* one width-1 single-literal start gate;
* schedule `[(1,1), (1,1)]`;
* `B(1,1,1,2) = 2^20`, `B(1,0,1,1) = 0`, and `B = 0` elsewhere;
* `t(d,s) = 0`.

This is a genuine multi-stage frozen-product instantiation beyond the earlier
one-stage width-0 witness, but it is not a strong B4 theorem: the first stage
uses `s = 1`, so the second stage enters with width budget `0` and has a
near-free beat.  No arbitrary layered decomposition, asymptotic family, final
global `t(d,s)` theorem, Frege/PHP lower bound, NP/circuit lower bound,
arbitrary AC0 collapse, PHP switching lemma, or P-vs-NP claim is made.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FrozenProductScheduleDemo

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
open FrozenProductSchedule

/-! ## The named width-1 start layer -/

def seventeenLit : Literal 17 := ⟨⟨0, by omega⟩, true⟩

/-- The start gate: one single-literal DNF, so the realized start width is 1. -/
def seventeenGate : GateSpec 17 :=
  GateSpec.dnf (BDFormula.lit seventeenLit)
    { D := [[seventeenLit]]
      sem_eq := by
        intro a
        simp [dnfEval, termEval, eval_lit]
      simple := by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm] }

/-- The named start layer: one width-1 gate under an `or` parent. -/
def seventeenLayer : MinimalLayeredFormula 17 :=
  { parent := ParentKind.or, gates := [seventeenGate] }

theorem seventeenLayer_width :
    forall g, g ∈ seventeenLayer.gates -> widthDNF g.theDNF <= 1 := by
  intro g hg
  have hg' : g = seventeenGate := by
    simpa [seventeenLayer] using hg
  subst hg'
  show widthDNF [[seventeenLit]] <= 1
  simp [widthDNF, termWidth]

theorem seventeenLayer_length : seventeenLayer.gates.length = 1 := rfl

/-! ## Explicit `B(m,w,s,d)` and `t(d,s)` for the two-stage schedule -/

/-- The concrete two-stage schedule `[(1,1), (1,1)]`. -/
def seventeenSchedule : List ScheduleStage :=
  [ScheduleStage.mk 1 1, ScheduleStage.mk 1 1]

/-- Explicit product-bound family for the named regime.

Only the two schedule points are nontrivial:
`B(1,1,1,2) = 2^20` for the first width-1 stage, and
`B(1,0,1,1) = 0` for the second width-0 stage. -/
def seventeenB : Nat -> Nat -> Nat -> Nat -> Nat
  | 1, 1, 1, 2 => 2 ^ 20
  | 1, 0, 1, 1 => 0
  | _, _, _, _ => 0

/-- The explicit tree-budget family for the named schedule. -/
def seventeenT : Nat -> Nat -> Nat :=
  fun _ _ => 0

/-- The supplied frozen-product hypothesis is fully discharged for the named
width-1/two-stage regime. -/
def seventeenProductHypothesis :
    FrozenProductHypothesis seventeenB seventeenT 1 17 2 1 17
      seventeenSchedule := by
  refine ⟨?_, ?_⟩
  · unfold seventeenSchedule ProductValidFrom
    refine ⟨?_, ?_, ?_⟩
    · unfold ProductBeat rawBadCount starSpace stageS seventeenB
      exact ⟨by decide, by decide⟩
    · unfold ProductBeat rawBadCount starSpace stageS seventeenB
      exact ⟨by decide, by decide⟩
    · refine ⟨?_, ?_, trivial⟩
      · unfold ProductBeat rawBadCount starSpace stageS seventeenB
        exact ⟨by decide, by decide⟩
      · unfold ProductBeat rawBadCount starSpace stageS seventeenB
        exact ⟨by decide, by decide⟩
  · unfold seventeenSchedule TreeBudgetFrom
    refine ⟨?_, ?_⟩
    · unfold StageTreeBudget stageS seventeenT
      decide
    · refine ⟨?_, trivial⟩
      unfold StageTreeBudget stageS seventeenT
      decide

/-- The explicit product family derives the schedule's `ValidFrom` obligations. -/
theorem seventeenProduct_validFrom :
    ValidFrom 1 17 1 17 seventeenSchedule :=
  productValidFrom_validFrom seventeenProductHypothesis.productBeats

/-! ## Concrete multi-stage certificate from the frozen-product interface -/

open GeneratedRefinedIteratedCertificate in
/-- **Concrete frozen-product schedule instantiation.**  From the named width-1
start layer and explicit `B(m,w,s,d)`/`t(d,s)` families above, the
frozen-product theorem produces a two-stage generated refined certificate.

This is non-vacuous relative to the previous width-0 one-stage witness because
the start layer has one realized width-1 gate and the schedule has two stages.
It remains a small finite instance: after the first `s = 1` stage, the second
stage enters with width budget `0`, so this must not be cited as full
frozen-form B4 closure or as an asymptotic product-bound theorem. -/
theorem frozenProductSchedule_seventeenTwoStage_nonvacuous :
    exists cert : GeneratedRefinedIteratedCertificate 17 (freeRestriction 17)
        (BDFormula.or [BDFormula.lit seventeenLit]) 2,
      cert.stageGateCounts = [1, 1] /\
      cert.stageBudgets = [1, 1] /\
      cert.stageStarCounts = [1, 1] /\
      TreeBudgetFrom seventeenT 1 2 seventeenSchedule := by
  have hhyp : FrozenProductHypothesis seventeenB seventeenT
      seventeenLayer.gates.length 17 seventeenSchedule.length 1
      (stars (freeRestriction 17)) seventeenSchedule := by
    simpa [seventeenLayer_length, seventeenSchedule, stars_freeRestriction]
      using seventeenProductHypothesis
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    autoIteratedCollapse_of_frozenProduct seventeenB seventeenT
      seventeenSchedule (freeRestriction 17) seventeenLayer 1
      seventeenLayer_width hhyp
  refine ⟨cert, ?_, ?_, ?_, ht⟩
  · rw [hgc]
    rfl
  · rw [hb]
    rfl
  · rw [hsc]
    rfl

end FrozenProductScheduleDemo
end PvNP
