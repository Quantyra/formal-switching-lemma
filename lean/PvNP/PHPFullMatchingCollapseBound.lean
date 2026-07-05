import PvNP.PHPFullMatchingProbability

/-!
# First collapse-probability upper bounds over the full matching space

`PHPFullMatchingProbability` packages events over the full square matching
space `fullMatchingSpace h s = subsetSpace h s x Equiv.Perm (Fin h)` in exact
cross-multiplied counting form, but everything proved there in the bad-event
direction is a probability-one LOWER-bound statement.  This module opens the
upper-bound direction of Gate A rung 4: it proves the first collapse-probability
upper bounds over this space for the easiest honest formula shapes, with
strictly-below-one nonvacuous instances at `h = 3`, `s = 2`.

Concretely, it introduces the formula-parameterized collapse-bad event
`matchingCollapseBad F t P` (every tree computing the restricted `F` has depth
at least `t`), and proves:

* a single PHP literal is collapse-bad at depth `1` only when its variable is
  left free, so its bad event has probability at most `(h - s) / h`
  (`matchingCollapseBad_lit_probability_le`);
* a single conjunctive term over PHP variables is collapse-bad at depth `1`
  only when one of its variables is left free, so by a finite list union bound
  its bad event has probability at most `|vars| * (h - s) / h`
  (`matchingCollapseBad_term_probability_le`), including the degenerate empty
  term, whose bad event is exactly empty
  (`matchingCollapseBad_nil_term_count`).

At `h = 3`, `s = 2` the single-literal bound instantiates to `1/3 < 1` over a
nonempty space (`matchingCollapseBad_lit_three_two_strict`): this is the first
strictly-below-one collapse-probability upper bound over the matching space in
this artifact.  A two-variable term instance gives `2/3 < 1`
(`matchingCollapseBad_term_three_two_strict`), so both headline bounds have
strictly-below-one instantiations.

## HONEST SCOPE STATEMENT (read this)

* This covers ONLY depth-1 collapse events for single literals and single
  conjunctive terms over PHP variables.  It is NOT a PHP switching lemma:
  there is no multi-term DNF bad-set bound, no depth-`t` canonical
  decision-tree argument, and no `(8w)^s`-style geometric bound over
  matchings.
* The union bound is the trivial finite containment-plus-sum inequality; the
  per-term bound `|vars| * (h - s) / h` is weak and is NOT the switching-lemma
  ratio regime, and it is trivially true (bound `>= 1`) once
  `|vars| * (h - s) >= h`.
* Trivial parameter corners are not excluded, only disclosed: at `s = 0` the
  literal bound is `h / h`; at `s > h` the matching space is empty; at `h = 0`
  the denominator is `0`; and `|vars|` counts list length, so duplicate
  variables inflate the term bound.  The strictly-below-one content lives in
  the `h = 3`, `s = 2` witnesses.
* The matching space is still square `h x h`; rectangular `p > h` injection
  spaces remain outside this module.
* Formula/proof-complexity infrastructure only: NOT a Frege/PHP proof-size
  lower bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingCollapseBound

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPBooleanDepthFloor
open PHPMatchingDistribution
open PHPFullMatchingDistribution
open PHPFullMatchingProbability

/-! ## Generic finite event machinery -/

/-- `eventCount` does not depend on the decidability instance. -/
theorem eventCount_inst_irrel {alpha : Type _} (space : Finset alpha)
    (event : alpha -> Prop) (inst1 inst2 : DecidablePred event) :
    @eventCount alpha space event inst1 = @eventCount alpha space event inst2 := by
  have heq : inst1 = inst2 :=
    funext (fun x => Subsingleton.elim (inst1 x) (inst2 x))
  rw [heq]

/-- Instance-transfer form of an `eventCount` upper bound. -/
theorem eventCount_le_trans_inst {alpha : Type _} {space : Finset alpha}
    {event : alpha -> Prop} {inst1 inst2 : DecidablePred event} {n : Nat}
    (h : @eventCount alpha space event inst1 <= n) :
    @eventCount alpha space event inst2 <= n :=
  Nat.le_trans (Nat.le_of_eq (eventCount_inst_irrel space event inst2 inst1)) h

/-- Pointwise containment on the space is monotone for `eventCount`. -/
theorem eventCount_mono_of_imp {alpha : Type _} (space : Finset alpha)
    (eventA eventB : alpha -> Prop) [DecidablePred eventA]
    [DecidablePred eventB]
    (himp : forall x, x ∈ space -> eventA x -> eventB x) :
    eventCount space eventA <= eventCount space eventB := by
  unfold eventCount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, himp x hx.1 hx.2⟩

/-- Containment transfer for `EventProbLe`: if `eventA` implies `eventB` on
the space and `eventB` has probability at most `num / den`, so does
`eventA`. -/
theorem eventProbLe_of_imp {alpha : Type _} (space : Finset alpha)
    (eventA eventB : alpha -> Prop) [DecidablePred eventA]
    [DecidablePred eventB] {num den : Nat}
    (himp : forall x, x ∈ space -> eventA x -> eventB x)
    (hB : EventProbLe space eventB num den) :
    EventProbLe space eventA num den := by
  unfold EventProbLe at hB ⊢
  exact Nat.le_trans
    (Nat.mul_le_mul (Nat.le_refl den)
      (eventCount_mono_of_imp space eventA eventB himp)) hB

open Classical in
/-- Two-event union bound for `eventCount`. -/
theorem eventCount_or_le {alpha : Type _} [DecidableEq alpha]
    (space : Finset alpha) (eventA eventB : alpha -> Prop) :
    eventCount space (fun x => eventA x ∨ eventB x) <=
      eventCount space eventA + eventCount space eventB := by
  unfold eventCount
  refine Nat.le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  rw [Finset.mem_filter] at hx
  rcases hx.2 with hA | hB
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx.1, hA⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx.1, hB⟩)

/-- Sum of a list map whose values are constant on members. -/
theorem list_sum_map_eq_length_mul {iota : Type _} (L : List iota)
    (f : iota -> Nat) (c : Nat) (h : forall x, x ∈ L -> f x = c) :
    (L.map f).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons,
        h x (List.mem_cons_self x xs),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy)),
        Nat.succ_mul, Nat.add_comm]

open Classical in
/-- **Finite list union bound.**  The count of the union of a list-indexed
family of events is at most the sum of the individual event counts. -/
theorem eventCount_exists_mem_le_sum {alpha iota : Type _} [DecidableEq alpha]
    (space : Finset alpha) (E : iota -> alpha -> Prop) (L : List iota) :
    eventCount space (fun x => ∃ v ∈ L, E v x) <=
      (L.map (fun v => eventCount space (E v))).sum := by
  induction L with
  | nil =>
      rw [List.map_nil, List.sum_nil, Nat.le_zero]
      unfold eventCount
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ hex
      obtain ⟨v, hv, _⟩ := hex
      exact absurd hv (List.not_mem_nil v)
  | cons v L ih =>
      rw [List.map_cons, List.sum_cons]
      have himp : forall x, x ∈ space ->
          (∃ w ∈ v :: L, E w x) -> (E v x ∨ ∃ w ∈ L, E w x) := by
        intro x _ hex
        obtain ⟨w, hw, hE⟩ := hex
        rcases List.mem_cons.mp hw with heq | hmem
        · exact Or.inl (heq ▸ hE)
        · exact Or.inr ⟨w, hmem, hE⟩
      have hstep : eventCount space (fun x => E v x ∨ ∃ w ∈ L, E w x) <=
          eventCount space (E v) +
            (L.map (fun w => eventCount space (E w))).sum := by
        refine Nat.le_trans (Nat.le_of_eq (eventCount_inst_irrel _ _ _ _))
          (Nat.le_trans
            (eventCount_or_le space (E v) (fun x => ∃ w ∈ L, E w x)) ?_)
        exact Nat.add_le_add (Nat.le_of_eq (eventCount_inst_irrel _ _ _ _))
          (eventCount_le_trans_inst ih)
      exact eventCount_le_trans_inst (Nat.le_trans
        (eventCount_mono_of_imp space _ _ himp) hstep)

/-! ## Formula-parameterized collapse-bad events -/

/-- A point of the full matching space is collapse-bad for the formula `F`
below depth `t` when every tree computing the restricted `F` has depth at
least `t`.  This generalizes `fullPHPCollapseBad` from the fixed PHP formula
to an arbitrary formula. -/
def matchingCollapseBad {h : Nat} (F : BDFormula (Nat.succ (h * h))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) : Prop :=
  forall T : DTree (Nat.succ (h * h)),
    (forall a : Assignment (Nat.succ (h * h)),
      Agree (fullRestrictionOf P) a ->
      dtEval a T = eval a (restrict (fullRestrictionOf P) F)) ->
    t <= dtDepth T

/-- On the square PHP formula, the generalized bad event is definitionally the
existing `fullPHPCollapseBad`. -/
theorem matchingCollapseBad_phpFormula_iff {h : Nat} (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    matchingCollapseBad (restrictedPHPFormula (fullPHPView h)) t P ↔
      fullPHPCollapseBad t P :=
  Iff.rfl

/-! ## Single-literal upper bound -/

/-- The single-literal formula on PHP variable `x_{i,j}` with polarity
`sign`. -/
def phpLitFormula (h : Nat) (i j : Fin h) (sign : Bool) :
    BDFormula (Nat.succ (h * h)) :=
  BDFormula.lit ⟨phpVar h h i j, sign⟩

/-- If the restriction fixes the variable, the restricted literal is the
matching constant formula. -/
theorem restrict_phpLitFormula_of_some {h : Nat} {i j : Fin h} {sign b : Bool}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    (hset : fullRestrictionOf P (phpVar h h i j) = some b) :
    restrict (fullRestrictionOf P) (phpLitFormula h i j sign) =
      (if b == sign then BDFormula.tru else BDFormula.fls) := by
  unfold phpLitFormula
  simp only [restrict, hset]

/-- If the restriction fixes the literal's variable, a depth-`0` leaf computes
the restricted literal, so the point is not collapse-bad at depth `1`. -/
theorem not_matchingCollapseBad_lit_of_set {h : Nat} {i j : Fin h}
    {sign : Bool} {P : Finset (Fin h) × Equiv.Perm (Fin h)} {b : Bool}
    (hset : fullRestrictionOf P (phpVar h h i j) = some b) :
    ¬ matchingCollapseBad (phpLitFormula h i j sign) 1 P := by
  intro hbad
  have hleaf : forall a : Assignment (Nat.succ (h * h)),
      Agree (fullRestrictionOf P) a ->
      dtEval a (DTree.leaf (b == sign)) =
        eval a (restrict (fullRestrictionOf P) (phpLitFormula h i j sign)) := by
    intro a _
    rw [restrict_phpLitFormula_of_some hset, dtEval_leaf]
    cases hbs : b == sign <;> simp [hbs, eval_tru, eval_fls]
  have hdepth := hbad (DTree.leaf (b == sign)) hleaf
  rw [dtDepth_leaf] at hdepth
  exact Nat.not_succ_le_zero 0 hdepth

/-- **Containment:** a literal collapse-bad point must leave the literal's
variable free — the bad event is contained in the star event. -/
theorem fullStarEvent_of_matchingCollapseBad_lit {h : Nat} {i j : Fin h}
    {sign : Bool} {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    (hbad : matchingCollapseBad (phpLitFormula h i j sign) 1 P) :
    fullStarEvent i j P := by
  show fullRestrictionOf P (phpVar h h i j) = none
  cases hval : fullRestrictionOf P (phpVar h h i j) with
  | none => rfl
  | some b => exact absurd hbad (not_matchingCollapseBad_lit_of_set hval)

open Classical in
/-- **Single-literal collapse-probability upper bound:** over the full square
matching space, a single PHP literal fails to collapse to depth `0` with
probability at most `(h - s) / h`, in exact cross-multiplied counting form. -/
theorem matchingCollapseBad_lit_probability_le {h s : Nat} (i j : Fin h)
    (sign : Bool) :
    EventProbLe (fullMatchingSpace h s)
      (matchingCollapseBad (phpLitFormula h i j sign) 1) (h - s) h := by
  have hmono : eventCount (fullMatchingSpace h s)
      (matchingCollapseBad (phpLitFormula h i j sign) 1) <=
      eventCount (fullMatchingSpace h s) (fullStarEvent i j) :=
    eventCount_mono_of_imp _ _ _
      (fun P _ hbad => fullStarEvent_of_matchingCollapseBad_lit hbad)
  unfold EventProbLe
  refine Nat.le_trans
    (Nat.mul_le_mul (Nat.le_refl h) (eventCount_le_trans_inst hmono)) ?_
  exact Nat.le_of_eq (fullStarEvent_probability_eq i j)

/-! ## Single-term (conjunction) upper bound via the union bound -/

/-- The literal of a term datum `(pigeon, hole, polarity)`. -/
def phpTermLit (h : Nat) (e : Fin h × Fin h × Bool) :
    BDFormula (Nat.succ (h * h)) :=
  BDFormula.lit ⟨phpVar h h e.1 e.2.1, e.2.2⟩

/-- The conjunctive term formula of a list of `(pigeon, hole, polarity)`
data.  The empty list gives the empty conjunction `.and []`, which evaluates
to `true`; it is handled honestly below, not excluded. -/
def phpTermFormula (h : Nat) (tv : List (Fin h × Fin h × Bool)) :
    BDFormula (Nat.succ (h * h)) :=
  BDFormula.and (tv.map (phpTermLit h))

/-- A restricted term literal whose variable is fixed evaluates to a constant,
independent of the assignment. -/
theorem eval_restrict_phpTermLit_of_some {h : Nat}
    {e : Fin h × Fin h × Bool} {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {b : Bool}
    (hset : fullRestrictionOf P (phpVar h h e.1 e.2.1) = some b)
    (a : Assignment (Nat.succ (h * h))) :
    eval a (restrict (fullRestrictionOf P) (phpTermLit h e)) = (b == e.2.2) := by
  unfold phpTermLit
  simp only [restrict, hset]
  cases hbs : b == e.2.2 <;> simp [hbs, eval_tru, eval_fls]

/-- If every variable of the term is fixed by the restriction, the restricted
term formula is semantically constant: it evaluates identically under any two
assignments. -/
theorem eval_restrict_phpTermFormula_const {h : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {tv : List (Fin h × Fin h × Bool)}
    (hset : forall e, e ∈ tv ->
      fullRestrictionOf P (phpVar h h e.1 e.2.1) ≠ none)
    (a a' : Assignment (Nat.succ (h * h))) :
    eval a (restrict (fullRestrictionOf P) (phpTermFormula h tv)) =
      eval a' (restrict (fullRestrictionOf P) (phpTermFormula h tv)) := by
  unfold phpTermFormula
  rw [restrict_and, eval_and, eval_and]
  apply all_congr_mem
  intro g hg
  obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf0
  cases hval : fullRestrictionOf P (phpVar h h e.1 e.2.1) with
  | none => exact absurd hval (hset e he)
  | some b =>
      rw [eval_restrict_phpTermLit_of_some hval a,
        eval_restrict_phpTermLit_of_some hval a']

/-- If every variable of the term is fixed, a depth-`0` leaf computes the
restricted term formula, so the point is not collapse-bad at depth `1`.  This
includes the empty term (`tv = []`) vacuously. -/
theorem not_matchingCollapseBad_term_of_allSet {h : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {tv : List (Fin h × Fin h × Bool)}
    (hset : forall e, e ∈ tv ->
      fullRestrictionOf P (phpVar h h e.1 e.2.1) ≠ none) :
    ¬ matchingCollapseBad (phpTermFormula h tv) 1 P := by
  intro hbad
  have hdepth := hbad
    (DTree.leaf (eval (fun _ => false)
      (restrict (fullRestrictionOf P) (phpTermFormula h tv))))
    (fun a _ => by
      rw [dtEval_leaf]
      exact eval_restrict_phpTermFormula_const hset (fun _ => false) a)
  rw [dtDepth_leaf] at hdepth
  exact Nat.not_succ_le_zero 0 hdepth

/-- **Containment:** a term collapse-bad point must leave some variable of the
term free — the bad event is contained in the union of the star events. -/
theorem exists_fullStarEvent_of_matchingCollapseBad_term {h : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {tv : List (Fin h × Fin h × Bool)}
    (hbad : matchingCollapseBad (phpTermFormula h tv) 1 P) :
    ∃ e ∈ tv, fullStarEvent e.1 e.2.1 P := by
  by_contra hnostar
  refine not_matchingCollapseBad_term_of_allSet ?_ hbad
  intro e he hnone
  exact hnostar ⟨e, he, hnone⟩

open Classical in
/-- The empty term is never collapse-bad: its bad event has count zero.  The
degenerate case is recorded honestly rather than excluded. -/
theorem matchingCollapseBad_nil_term_count (h s : Nat) :
    eventCount (fullMatchingSpace h s)
      (matchingCollapseBad
        (phpTermFormula h ([] : List (Fin h × Fin h × Bool))) 1) = 0 := by
  unfold eventCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro P _
  exact not_matchingCollapseBad_term_of_allSet
    (fun e he _ => absurd he (List.not_mem_nil e))

open Classical in
/-- **Width-`w` term collapse-probability upper bound via the union bound:**
over the full square matching space, a conjunctive term on `tv.length` PHP
variables fails to collapse to depth `0` with probability at most
`tv.length * (h - s) / h`, in exact cross-multiplied counting form.  The
empty term (`tv = []`) is included: its bad event is empty and the bound is
`0 / h`. -/
theorem matchingCollapseBad_term_probability_le {h s : Nat}
    (tv : List (Fin h × Fin h × Bool)) :
    EventProbLe (fullMatchingSpace h s)
      (matchingCollapseBad (phpTermFormula h tv) 1)
      (tv.length * (h - s)) h := by
  have hK : eventCount (fullMatchingSpace h s)
      (matchingCollapseBad (phpTermFormula h tv) 1) <=
      tv.length *
        (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))) := by
    have hunion : eventCount (fullMatchingSpace h s)
        (fun P => ∃ e ∈ tv, fullStarEvent e.1 e.2.1 P) <=
        tv.length *
          (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))) := by
      have hb := eventCount_exists_mem_le_sum (fullMatchingSpace h s)
        (fun (e : Fin h × Fin h × Bool) P => fullStarEvent e.1 e.2.1 P) tv
      refine Nat.le_trans (Nat.le_of_eq (eventCount_inst_irrel _ _ _ _))
        (Nat.le_trans hb ?_)
      refine Nat.le_of_eq (list_sum_map_eq_length_mul tv _ _ ?_)
      intro e _
      exact (eventCount_inst_irrel _ _ _ _).trans
        (fullStarEvent_count e.1 e.2.1)
    refine Nat.le_trans (eventCount_mono_of_imp (fullMatchingSpace h s) _ _
      (fun P _ hbad =>
        exists_fullStarEvent_of_matchingCollapseBad_term hbad)) ?_
    exact eventCount_le_trans_inst hunion
  unfold EventProbLe
  refine Nat.le_trans
    (Nat.mul_le_mul (Nat.le_refl h) (eventCount_le_trans_inst hK))
    (Nat.le_of_eq ?_)
  rw [card_fullMatchingSpace]
  calc h * (tv.length *
        (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))))
      = tv.length * (h *
          (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)))) := by
        rw [Nat.mul_left_comm]
    _ = tv.length * ((h - s) *
          (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h)))) := by
        rw [star_ratio_full]
    _ = (tv.length * (h - s)) *
          (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h))) := by
        rw [Nat.mul_assoc]

/-! ## Non-vacuity at `h = 3`, `s = 2` -/

/-- The full matching space at `h = 3`, `s = 2` is nonempty. -/
theorem fullMatchingSpace_three_two_nonempty :
    (fullMatchingSpace 3 2).Nonempty := by
  refine ⟨⟨{0, 1}, Equiv.refl (Fin 3)⟩, ?_⟩
  unfold fullMatchingSpace
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · unfold subsetSpace
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by decide⟩
  · unfold permSpace
    exact Finset.mem_univ _

open Classical in
/-- **First strictly-below-one collapse bound in this artifact:** at `h = 3`,
`s = 2` the single-literal bad event has probability at most `1 / 3`, the
bound `1 / 3` is strictly below one (`1 < 3`), and the space is nonempty, so
this is a genuine non-vacuous upper bound strictly below probability one. -/
theorem matchingCollapseBad_lit_three_two_strict (i j : Fin 3) (sign : Bool) :
    EventProbLe (fullMatchingSpace 3 2)
      (matchingCollapseBad (phpLitFormula 3 i j sign) 1) 1 3 ∧
      1 < 3 ∧ (fullMatchingSpace 3 2).Nonempty :=
  ⟨matchingCollapseBad_lit_probability_le i j sign, by decide,
    fullMatchingSpace_three_two_nonempty⟩

open Classical in
/-- **Strictly-below-one term instance:** at `h = 3`, `s = 2` the width-`2`
term on the distinct variables `x_{0,0}` and `x_{1,1}` has bad-event
probability at most `2 / 3`, the bound is strictly below one (`2 < 3`), and
the space is nonempty, so the term union-bound theorem also has a genuine
non-vacuous strictly-below-one instantiation. -/
theorem matchingCollapseBad_term_three_two_strict :
    EventProbLe (fullMatchingSpace 3 2)
      (matchingCollapseBad
        (phpTermFormula 3 [(0, 0, true), (1, 1, true)]) 1) 2 3 ∧
      2 < 3 ∧ (fullMatchingSpace 3 2).Nonempty :=
  ⟨matchingCollapseBad_term_probability_le [(0, 0, true), (1, 1, true)],
    by decide, fullMatchingSpace_three_two_nonempty⟩

end PHPFullMatchingCollapseBound
end PvNP
