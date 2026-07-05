import PvNP.PHPFullMatchingCollapseBound

/-!
# Exact single-literal collapse probability over the full matching space

`PHPFullMatchingCollapseBound` proved that the depth-1 single-literal
collapse-bad event is CONTAINED in the star event of its variable
(`fullStarEvent_of_matchingCollapseBad_lit`), giving the upper bound
`(h - s) / h` (`matchingCollapseBad_lit_probability_le`).  The converse
containment was not formalized there, so realizability of the bad event was
not certified and the bound was only an inequality.  This module closes that
gap for the single-literal event:

* `matchingCollapseBad_lit_of_fullStarEvent`: the CONVERSE containment — if
  the literal's variable is left free, the restricted formula is still the
  bare literal, and no depth-`0` leaf computes it on all agreeing
  assignments (two explicit agreeing assignments flip the free variable), so
  every correct tree has depth at least `1`;
* `matchingCollapseBad_lit_iff_fullStarEvent`: the bad event is pointwise
  EQUAL to the star event;
* `matchingCollapseBad_lit_probability_eq`: the exact probability
  `(h - s) / h` in cross-multiplied counting form (an `EventProbEq`,
  upgrading the previous `EventProbLe`);
* `matchingCollapseBad_lit_three_two_count_pos`: at `h = 3`, `s = 2` the bad
  event has POSITIVE count (`choose 2 2 * |Perm (Fin 3)|` points), so the
  event is realized by actual points of the space and the exact probability
  `1 / 3` is not vacuous.

## HONEST SCOPE STATEMENT (read this)

* Exactness covers ONLY the depth-1 SINGLE-LITERAL collapse event.  The
  single-conjunctive-term bound of `PHPFullMatchingCollapseBound` remains an
  inequality, and its union bound is genuinely loose: a term containing a
  literal fixed to `false` by the restriction is computed by a depth-`0`
  leaf even when its other variables are left free, so the term bad event is
  in general strictly smaller than the union of its star events.  NO term
  exactness is claimed here.
* Still NOT a PHP switching lemma: no multi-term DNF bad-set bound, no
  depth-`t` canonical decision-tree argument, and no geometric
  `(8w)^s`-style bound over matchings; Gate A rung 4 as a whole remains
  open.
* Trivial parameter corners of the exact statement are disclosed, not
  excluded: at `s = 0` the probability is genuinely one (no variable fixed);
  at `s = h` it is genuinely zero over a nonempty space; at `s > h` the
  space is empty and the cross-multiplied equality degenerates to `0 = 0`.
  The non-vacuous content is certified at `h = 3`, `s = 2` by the
  realizability corollary; parametric realizability for all `s < h` is NOT
  claimed.
* The matching space is still square `h x h`; rectangular `p > h` injection
  spaces remain outside this module.
* Formula/proof-complexity infrastructure only: NOT a Frege/PHP proof-size
  lower bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingCollapseExact

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPBooleanDepthFloor
open PHPMatchingDistribution
open PHPFullMatchingDistribution
open PHPFullMatchingProbability
open PHPFullMatchingCollapseBound

/-! ## Generic finite event machinery -/

/-- `eventCount` respects pointwise equivalence of events on the space. -/
theorem eventCount_congr_iff {alpha : Type _} (space : Finset alpha)
    (eventA eventB : alpha -> Prop) [DecidablePred eventA]
    [DecidablePred eventB]
    (hiff : forall x, x ∈ space -> (eventA x ↔ eventB x)) :
    eventCount space eventA = eventCount space eventB :=
  Nat.le_antisymm
    (eventCount_mono_of_imp space eventA eventB
      (fun x hx hA => (hiff x hx).mp hA))
    (eventCount_mono_of_imp space eventB eventA
      (fun x hx hB => (hiff x hx).mpr hB))

/-! ## The restricted literal on a free variable -/

/-- If the restriction leaves the variable free, the restricted literal is
still the bare literal. -/
theorem restrict_phpLitFormula_of_none {h : Nat} {i j : Fin h} {sign : Bool}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    (hfree : fullRestrictionOf P (phpVar h h i j) = none) :
    restrict (fullRestrictionOf P) (phpLitFormula h i j sign) =
      phpLitFormula h i j sign := by
  unfold phpLitFormula
  simp only [restrict, hfree]

/-- Evaluation of the single-literal formula, for either polarity: the
variable's value compared against the polarity. -/
theorem eval_phpLitFormula {h : Nat} (i j : Fin h) (sign : Bool)
    (a : Assignment (Nat.succ (h * h))) :
    eval a (phpLitFormula h i j sign) = (a (phpVar h h i j) == sign) := by
  cases sign <;> cases hval : a (phpVar h h i j) <;>
    simp [phpLitFormula, eval_lit, litEval, hval]

/-! ## Two explicit agreeing assignments flipping a free variable -/

/-- The witness assignment that copies every value fixed by the restriction,
sets the distinguished variable `x` to `c`, and sets every other free
variable to `false`. -/
def starWitness {h : Nat} (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (x : Fin (Nat.succ (h * h))) (c : Bool) :
    Assignment (Nat.succ (h * h)) :=
  fun v => if v = x then c else (fullRestrictionOf P v).getD false

/-- The witness assignment takes value `c` at the distinguished variable. -/
theorem starWitness_self {h : Nat} (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (x : Fin (Nat.succ (h * h))) (c : Bool) :
    starWitness P x c x = c := by
  unfold starWitness
  exact if_pos rfl

/-- Whenever the distinguished variable is free, the witness assignment
agrees with the restriction: `Agree` only constrains variables fixed to
`some` value, and the override sits on a `none` variable. -/
theorem starWitness_agree {h : Nat} {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {x : Fin (Nat.succ (h * h))}
    (hfree : fullRestrictionOf P x = none) (c : Bool) :
    Agree (fullRestrictionOf P) (starWitness P x c) := by
  intro v b hv
  unfold starWitness
  by_cases hvx : v = x
  · subst hvx
    rw [hv] at hfree
    exact Option.noConfusion hfree
  · rw [if_neg hvx, hv]
    rfl

/-! ## The converse containment and the exact event identity -/

/-- **Converse containment (realizability direction):** if the literal's
variable is left free, the point IS collapse-bad at depth `1`.  The
restricted formula is still the bare literal, a node tree already has depth
at least `1`, and a depth-`0` leaf is constant while the two agreeing
witness assignments flip the free variable and hence the literal's value. -/
theorem matchingCollapseBad_lit_of_fullStarEvent {h : Nat} {i j : Fin h}
    {sign : Bool} {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    (hstar : fullStarEvent i j P) :
    matchingCollapseBad (phpLitFormula h i j sign) 1 P := by
  have hfree : fullRestrictionOf P (phpVar h h i j) = none := hstar
  unfold matchingCollapseBad
  intro T hT
  cases T with
  | node v t0 t1 =>
      rw [dtDepth_node]
      exact Nat.le_add_right 1 _
  | leaf b =>
      exfalso
      have hTrue := hT (starWitness P (phpVar h h i j) true)
        (starWitness_agree hfree true)
      have hFalse := hT (starWitness P (phpVar h h i j) false)
        (starWitness_agree hfree false)
      rw [restrict_phpLitFormula_of_none hfree, dtEval_leaf,
        eval_phpLitFormula, starWitness_self] at hTrue
      rw [restrict_phpLitFormula_of_none hfree, dtEval_leaf,
        eval_phpLitFormula, starWitness_self] at hFalse
      rw [hTrue] at hFalse
      cases sign <;> exact absurd hFalse (by decide)

/-- **Exact event identity:** the depth-1 single-literal collapse-bad event
is pointwise EQUAL to the star event of its variable, combining the two
containments. -/
theorem matchingCollapseBad_lit_iff_fullStarEvent {h : Nat} (i j : Fin h)
    (sign : Bool) (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    matchingCollapseBad (phpLitFormula h i j sign) 1 P ↔
      fullStarEvent i j P :=
  ⟨fullStarEvent_of_matchingCollapseBad_lit,
    matchingCollapseBad_lit_of_fullStarEvent⟩

/-! ## The exact probability and realizability -/

open Classical in
/-- **Exact single-literal collapse probability:** over the full square
matching space, a single PHP literal fails to collapse to depth `0` with
probability EXACTLY `(h - s) / h`, in exact cross-multiplied counting form,
upgrading the `EventProbLe` of `PHPFullMatchingCollapseBound` to an
`EventProbEq`. -/
theorem matchingCollapseBad_lit_probability_eq {h s : Nat} (i j : Fin h)
    (sign : Bool) :
    EventProbEq (fullMatchingSpace h s)
      (matchingCollapseBad (phpLitFormula h i j sign) 1) (h - s) h := by
  have hcount : eventCount (fullMatchingSpace h s)
      (matchingCollapseBad (phpLitFormula h i j sign) 1) =
      eventCount (fullMatchingSpace h s) (fullStarEvent i j) :=
    Eq.trans
      (eventCount_congr_iff (fullMatchingSpace h s) _ _
        (fun P _ => matchingCollapseBad_lit_iff_fullStarEvent i j sign P))
      (eventCount_inst_irrel (fullMatchingSpace h s) (fullStarEvent i j) _ _)
  have hstar := fullStarEvent_probability_eq (h := h) (s := s) i j
  unfold EventProbEq at hstar ⊢
  rw [hcount]
  exact hstar

open Classical in
/-- **Realizability at `h = 3`, `s = 2`:** the depth-1 single-literal
collapse-bad event has POSITIVE count over the full matching space — by the
exact event identity its count equals the star-event count
`choose 2 2 * |Perm (Fin 3)|`, which is positive — so the exact probability
`1 / 3` certifies a genuinely inhabited event, not a vacuous bound. -/
theorem matchingCollapseBad_lit_three_two_count_pos (i j : Fin 3)
    (sign : Bool) :
    0 < eventCount (fullMatchingSpace 3 2)
      (matchingCollapseBad (phpLitFormula 3 i j sign) 1) := by
  have hcount : eventCount (fullMatchingSpace 3 2)
      (matchingCollapseBad (phpLitFormula 3 i j sign) 1) =
      eventCount (fullMatchingSpace 3 2) (fullStarEvent i j) :=
    Eq.trans
      (eventCount_congr_iff (fullMatchingSpace 3 2) _ _
        (fun P _ => matchingCollapseBad_lit_iff_fullStarEvent i j sign P))
      (eventCount_inst_irrel (fullMatchingSpace 3 2) (fullStarEvent i j) _ _)
  rw [hcount, fullStarEvent_count]
  have hchoose : Nat.choose (3 - 1) 2 = 1 := by decide
  rw [hchoose, Nat.one_mul]
  exact Fintype.card_pos

end PHPFullMatchingCollapseExact
end PvNP
