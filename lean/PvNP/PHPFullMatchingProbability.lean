import PvNP.PHPFullMatchingDistribution

/-!
# Finite probability interface for the full PHP matching space

`PHPFullMatchingDistribution` proves exact cardinalities over the square
matching space

  `fullMatchingSpace h s = subsetSpace h s x Equiv.Perm (Fin h)`.

This module adds the next Gate A interface layer: events, bad events, and
probability statements in exact finite-counting form.  It deliberately avoids
measure theory; an event has probability `num / den` when the cross-multiplied
counting identity

  `den * eventCount = num * totalCount`

holds, and has probability at most `num / den` when the corresponding
inequality holds.

## HONEST SCOPE STATEMENT (read this)

* This is finite event/probability bookkeeping over the already-formalized full
  square matching space.  It does NOT prove a PHP switching lemma and does NOT
  prove any collapse-probability upper bound.
* The module records the star event as an exact probability statement and
  packages the PHP depth-floor obstruction as a probability-one bad-collapse
  event.  Probability one for a lower-bound event is the opposite direction
  from the desired switching lemma upper bound.
* The matching space is still square `h x h`; rectangular `p > h` injection
  spaces remain outside this module.
* Formula/proof-complexity infrastructure only: NOT a Frege/PHP proof-size
  lower bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingProbability

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPBooleanDepthFloor
open PHPFullMatchingDistribution

/-! ## Generic finite event bookkeeping -/

/-- Count the points of a finite space satisfying an event. -/
def eventCount {alpha : Type _} (space : Finset alpha) (event : alpha -> Prop)
    [DecidablePred event] : Nat :=
  (space.filter event).card

/-- Exact finite-probability equality in cross-multiplied counting form:
`event` has probability `num / den` inside `space`. -/
def EventProbEq {alpha : Type _} (space : Finset alpha) (event : alpha -> Prop)
    [DecidablePred event] (num den : Nat) : Prop :=
  den * eventCount space event = num * space.card

/-- Finite-probability upper bound in cross-multiplied counting form:
`event` has probability at most `num / den` inside `space`. -/
def EventProbLe {alpha : Type _} (space : Finset alpha) (event : alpha -> Prop)
    [DecidablePred event] (num den : Nat) : Prop :=
  den * eventCount space event <= num * space.card

theorem eventCount_le_card {alpha : Type _} (space : Finset alpha)
    (event : alpha -> Prop) [DecidablePred event] :
    eventCount space event <= space.card := by
  exact Finset.card_filter_le _ _

theorem eventProbLe_of_eventProbEq {alpha : Type _} (space : Finset alpha)
    (event : alpha -> Prop) [DecidablePred event] {num den : Nat}
    (h : EventProbEq space event num den) :
    EventProbLe space event num den := by
  rw [EventProbLe, EventProbEq] at *
  exact Nat.le_of_eq h

theorem eventCount_eq_card_of_forall_mem {alpha : Type _} (space : Finset alpha)
    (event : alpha -> Prop) [DecidablePred event]
    (h : forall x, x ∈ space -> event x) :
    eventCount space event = space.card := by
  unfold eventCount
  rw [Finset.filter_true_of_mem]
  intro x hx
  exact h x hx

theorem eventProbEq_one_of_eventCount_eq_card {alpha : Type _}
    (space : Finset alpha) (event : alpha -> Prop) [DecidablePred event]
    (h : eventCount space event = space.card) :
    EventProbEq space event 1 1 := by
  unfold EventProbEq
  rw [h]

/-! ## Star events over the full matching space -/

/-- The event that a PHP variable is left free by a full matching restriction. -/
def fullStarEvent {h : Nat} (i j : Fin h)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) : Prop :=
  fullRestrictionOf P (phpVar h h i j) = none

instance instDecidablePredFullStarEvent {h : Nat} (i j : Fin h) :
    DecidablePred (fullStarEvent i j) :=
  fun P => inferInstanceAs
    (Decidable (fullRestrictionOf P (phpVar h h i j) = none))

theorem fullStarEvent_count {h s : Nat} (i j : Fin h) :
    eventCount (fullMatchingSpace h s) (fullStarEvent i j) =
      Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)) := by
  unfold eventCount fullStarEvent
  exact phpVar_freeCount_full i j

/-- The exact star probability over the full square matching space:
every PHP variable is free with probability `(h - s) / h`, stated in exact
cross-multiplied finite-counting form. -/
theorem fullStarEvent_probability_eq {h s : Nat} (i j : Fin h) :
    EventProbEq (fullMatchingSpace h s) (fullStarEvent i j) (h - s) h := by
  unfold EventProbEq eventCount fullStarEvent
  exact phpVar_star_ratio_full i j

theorem fullStarEvent_probability_le {h s : Nat} (i j : Fin h) :
    EventProbLe (fullMatchingSpace h s) (fullStarEvent i j) (h - s) h :=
  eventProbLe_of_eventProbEq _ _ (fullStarEvent_probability_eq i j)

/-! ## PHP collapse-bad events -/

/-- A point of the full matching space is bad for collapse below `t` when every
tree computing the restricted square-PHP formula has depth at least `t`. -/
def fullPHPCollapseBad {h : Nat} (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) : Prop :=
  forall T : DTree (Nat.succ (h * h)),
    (forall a : Assignment (Nat.succ (h * h)),
      Agree (fullRestrictionOf P) a ->
      dtEval a T =
        eval a (restrict (fullRestrictionOf P)
          (restrictedPHPFormula (fullPHPView h)))) ->
    t <= dtDepth T

/-- The S2072/S2080 floor says every point of the full matching space is bad
for collapse below `(h - s) * h`. -/
theorem fullPHPCollapseBad_depthFloor_holds {h s : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hP : P ∈ fullMatchingSpace h s) :
    fullPHPCollapseBad ((h - s) * h) P := by
  intro T hT
  exact fullMatchingSpace_depthFloor P hP T hT

open Classical in
/-- The collapse-bad depth-floor event has full count over the full matching
space.  This is probability-one lower-bound bookkeeping, not a switching-lemma
upper bound. -/
theorem fullPHPCollapseBad_depthFloor_count (h s : Nat) :
    eventCount (fullMatchingSpace h s)
        (fullPHPCollapseBad ((h - s) * h)) =
      (fullMatchingSpace h s).card := by
  apply eventCount_eq_card_of_forall_mem
  intro P hP
  exact fullPHPCollapseBad_depthFloor_holds P hP

open Classical in
/-- Probability-one form of the square-PHP depth-floor obstruction over the full
matching space.  This packages the lower-bound event in the same finite
probability interface that a future PHP switching lemma can use for upper-bound
bad events. -/
theorem fullPHPCollapseBad_depthFloor_probability_one (h s : Nat) :
    EventProbEq (fullMatchingSpace h s)
      (fullPHPCollapseBad ((h - s) * h)) 1 1 :=
  eventProbEq_one_of_eventCount_eq_card _
    (fullPHPCollapseBad ((h - s) * h))
    (fullPHPCollapseBad_depthFloor_count h s)

end PHPFullMatchingProbability
end PvNP
