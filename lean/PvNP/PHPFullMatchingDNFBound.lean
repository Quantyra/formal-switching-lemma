import PvNP.PHPFullMatchingCollapseExact

/-!
# First multi-term DNF depth-1 bad-set bound over the full matching space

`PHPFullMatchingCollapseBound` bounded the depth-1 collapse-bad event for a
single PHP literal and a single conjunctive term.  This module takes the next
honest step: a simple multi-term DNF over PHP variables, represented as a
list of terms `tvs : List (List (Fin h × Fin h × Bool))` with
`phpDNFFormula h tvs = BDFormula.or (tvs.map (phpTermFormula h))`, and the
first multi-term DNF depth-1 bad-set bound over the matching space in this
artifact:

* `eval_restrict_phpDNFFormula_const`: if every variable of every term is
  fixed by the restriction, the restricted DNF is semantically constant (an
  `or` of constants is constant);
* `not_matchingCollapseBad_dnf_of_allSet`: all variables set ⇒ a depth-`0`
  leaf computes the restricted DNF ⇒ not collapse-bad at depth `1`;
* `exists_fullStarEvent_of_matchingCollapseBad_dnf`: a DNF collapse-bad point
  must leave some literal occurrence's variable free — containment in the
  union of the star events of `tvs.join`;
* `matchingCollapseBad_dnf_probability_le`: the headline union bound — the
  DNF collapse-bad event has probability at most
  `tvs.join.length * (h - s) / h` in exact cross-multiplied counting form,
  where `tvs.join.length` is the TOTAL literal-occurrence count `Σᵢ wᵢ`;
* degenerate cases as theorems: the empty DNF (`.or []` evaluates to `false`)
  has empty bad event (`matchingCollapseBad_nil_dnf_count`), and a DNF
  containing an empty term (`.and []` evaluates to `true`, so the whole DNF
  is constantly true on every assignment regardless of the restriction) also
  has empty bad event (`matchingCollapseBad_dnf_count_zero_of_mem_nil`);
* `matchingCollapseBad_dnf_three_two_strict`: at `h = 3`, `s = 2` the
  two-term single-literal-per-term DNF on `x_{0,0}` and `x_{1,1}` has bad
  probability at most `2/3 < 1` over a nonempty space.

## HONEST SCOPE STATEMENT (read this)

* This is the first multi-term DNF bad-set bound over the matching space IN
  THIS ARTIFACT, but it is ONLY the depth-1 (constant-collapse) event bounded
  by the TRIVIAL union bound over ALL literal occurrences: the bound is
  linear in the total DNF size `tvs.join.length`, NOT the switching-lemma
  regime.  A real PHP switching lemma needs depth-`t` canonical decision
  trees, a bad-set ENCODING argument, and a geometric bound independent of
  the term COUNT; none of that is here.  Gate A rung 4 as a whole remains
  open.
* "Collapse-bad at depth 1" means only "the restricted DNF fails to be
  computed by a depth-`0` tree", i.e. fails to be constant — NOT the
  depth-`t` collapse events (failure of a shallow canonical decision tree) a
  switching lemma bounds.
* The bound is trivially true (numerator `>= den * count/card` regime lost)
  once `tvs.join.length * (h - s) >= h`; duplicate literal occurrences are
  counted with multiplicity and inflate the bound; the strictly-below-one
  content lives in the `h = 3`, `s = 2` witness.
* Degenerate shapes are disclosed, not excluded: the empty DNF is constantly
  `false` and a DNF containing an empty term is constantly `true`; both bad
  events are exactly empty.
* The matching space is still square `h x h`; rectangular `p > h` injection
  spaces remain outside this module.
* Formula/proof-complexity infrastructure only: NOT a Frege/PHP proof-size
  lower bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingDNFBound

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

/-! ## The simple DNF formula of a list of terms -/

/-- The DNF formula of a list of terms, each a list of
`(pigeon, hole, polarity)` literal data.  The empty list gives the empty
disjunction `.or []`, which evaluates to `false`; a member empty term gives
the empty conjunction `.and []`, which evaluates to `true`.  Both degenerate
shapes are handled honestly below, not excluded. -/
def phpDNFFormula (h : Nat) (tvs : List (List (Fin h × Fin h × Bool))) :
    BDFormula (Nat.succ (h * h)) :=
  BDFormula.or (tvs.map (phpTermFormula h))

/-- If every variable of every term is fixed by the restriction, the
restricted DNF formula is semantically constant: it evaluates identically
under any two assignments.  Each restricted term is constant by
`eval_restrict_phpTermFormula_const`, and an `or` of constants is
constant. -/
theorem eval_restrict_phpDNFFormula_const {h : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hset : forall tv, tv ∈ tvs -> forall e, e ∈ tv ->
      fullRestrictionOf P (phpVar h h e.1 e.2.1) ≠ none)
    (a a' : Assignment (Nat.succ (h * h))) :
    eval a (restrict (fullRestrictionOf P) (phpDNFFormula h tvs)) =
      eval a' (restrict (fullRestrictionOf P) (phpDNFFormula h tvs)) := by
  unfold phpDNFFormula
  rw [restrict_or, eval_or, eval_or]
  apply any_congr_mem
  intro g hg
  obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hf0
  exact eval_restrict_phpTermFormula_const (hset tv htv) a a'

/-- If every variable of every term is fixed, a depth-`0` leaf computes the
restricted DNF formula, so the point is not collapse-bad at depth `1`.  This
includes the empty DNF (`tvs = []`) vacuously. -/
theorem not_matchingCollapseBad_dnf_of_allSet {h : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hset : forall tv, tv ∈ tvs -> forall e, e ∈ tv ->
      fullRestrictionOf P (phpVar h h e.1 e.2.1) ≠ none) :
    ¬ matchingCollapseBad (phpDNFFormula h tvs) 1 P := by
  intro hbad
  have hdepth := hbad
    (DTree.leaf (eval (fun _ => false)
      (restrict (fullRestrictionOf P) (phpDNFFormula h tvs))))
    (fun a _ => by
      rw [dtEval_leaf]
      exact eval_restrict_phpDNFFormula_const hset (fun _ => false) a)
  rw [dtDepth_leaf] at hdepth
  exact Nat.not_succ_le_zero 0 hdepth

/-- **Containment:** a DNF collapse-bad point must leave the variable of some
literal occurrence of some term free — the bad event is contained in the
union of the star events of the flattened literal list `tvs.join`. -/
theorem exists_fullStarEvent_of_matchingCollapseBad_dnf {h : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hbad : matchingCollapseBad (phpDNFFormula h tvs) 1 P) :
    ∃ e ∈ tvs.join, fullStarEvent e.1 e.2.1 P := by
  by_contra hnostar
  refine not_matchingCollapseBad_dnf_of_allSet ?_ hbad
  intro tv htv e he hnone
  exact hnostar ⟨e, List.mem_join.mpr ⟨tv, htv, he⟩, hnone⟩

/-! ## Degenerate shapes, recorded honestly -/

open Classical in
/-- The empty DNF (`.or []`, constantly `false`) is never collapse-bad: its
bad event has count zero. -/
theorem matchingCollapseBad_nil_dnf_count (h s : Nat) :
    eventCount (fullMatchingSpace h s)
      (matchingCollapseBad
        (phpDNFFormula h ([] : List (List (Fin h × Fin h × Bool)))) 1) = 0 := by
  unfold eventCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro P _
  exact not_matchingCollapseBad_dnf_of_allSet
    (fun tv htv _ _ _ => absurd htv (List.not_mem_nil tv))

open Classical in
/-- A DNF containing an empty term is never collapse-bad: the empty term is
the empty conjunction `.and []`, which evaluates to `true`, so the whole
restricted DNF is constantly `true` on every assignment — regardless of the
restriction — and a depth-`0` `true` leaf computes it.  Its bad event has
count zero, with no all-set hypothesis needed. -/
theorem matchingCollapseBad_dnf_count_zero_of_mem_nil {h : Nat} (s : Nat)
    {tvs : List (List (Fin h × Fin h × Bool))} (hnil : [] ∈ tvs) :
    eventCount (fullMatchingSpace h s)
      (matchingCollapseBad (phpDNFFormula h tvs) 1) = 0 := by
  unfold eventCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro P _ hbad
  have htrue : forall a : Assignment (Nat.succ (h * h)),
      eval a (restrict (fullRestrictionOf P) (phpDNFFormula h tvs)) = true := by
    intro a
    unfold phpDNFFormula
    rw [restrict_or, eval_or]
    apply List.any_eq_true.mpr
    refine ⟨restrict (fullRestrictionOf P) (phpTermFormula h []), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨phpTermFormula h [],
        List.mem_map.mpr ⟨[], hnil, rfl⟩, rfl⟩
    · unfold phpTermFormula
      rw [List.map_nil, restrict_and, List.map_nil, eval_and, List.all_nil]
  have hdepth := hbad (DTree.leaf true)
    (fun a _ => by rw [dtEval_leaf, htrue a])
  rw [dtDepth_leaf] at hdepth
  exact Nat.not_succ_le_zero 0 hdepth

/-! ## The headline union bound -/

open Classical in
/-- **Multi-term DNF depth-1 collapse-probability upper bound via the union
bound:** over the full square matching space, a simple DNF with total
literal-occurrence count `tvs.join.length` fails to collapse to depth `0`
with probability at most `tvs.join.length * (h - s) / h`, in exact
cross-multiplied counting form.  The bound is linear in the TOTAL DNF size
(duplicates counted), NOT the switching-lemma regime, and is trivially true
once `tvs.join.length * (h - s) >= h`. -/
theorem matchingCollapseBad_dnf_probability_le {h s : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    EventProbLe (fullMatchingSpace h s)
      (matchingCollapseBad (phpDNFFormula h tvs) 1)
      (tvs.join.length * (h - s)) h := by
  have hK : eventCount (fullMatchingSpace h s)
      (matchingCollapseBad (phpDNFFormula h tvs) 1) <=
      tvs.join.length *
        (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))) := by
    have hunion : eventCount (fullMatchingSpace h s)
        (fun P => ∃ e ∈ tvs.join, fullStarEvent e.1 e.2.1 P) <=
        tvs.join.length *
          (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))) := by
      have hb := eventCount_exists_mem_le_sum (fullMatchingSpace h s)
        (fun (e : Fin h × Fin h × Bool) P => fullStarEvent e.1 e.2.1 P)
        tvs.join
      refine Nat.le_trans (Nat.le_of_eq (eventCount_inst_irrel _ _ _ _))
        (Nat.le_trans hb ?_)
      refine Nat.le_of_eq (list_sum_map_eq_length_mul tvs.join _ _ ?_)
      intro e _
      exact (eventCount_inst_irrel _ _ _ _).trans
        (fullStarEvent_count e.1 e.2.1)
    refine Nat.le_trans (eventCount_mono_of_imp (fullMatchingSpace h s) _ _
      (fun P _ hbad =>
        exists_fullStarEvent_of_matchingCollapseBad_dnf hbad)) ?_
    exact eventCount_le_trans_inst hunion
  unfold EventProbLe
  refine Nat.le_trans
    (Nat.mul_le_mul (Nat.le_refl h) (eventCount_le_trans_inst hK))
    (Nat.le_of_eq ?_)
  rw [card_fullMatchingSpace]
  calc h * (tvs.join.length *
        (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))))
      = tvs.join.length * (h *
          (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)))) := by
        rw [Nat.mul_left_comm]
    _ = tvs.join.length * ((h - s) *
          (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h)))) := by
        rw [star_ratio_full]
    _ = (tvs.join.length * (h - s)) *
          (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h))) := by
        rw [Nat.mul_assoc]

/-! ## Non-vacuity at `h = 3`, `s = 2` -/

open Classical in
/-- **Strictly-below-one multi-term DNF instance:** at `h = 3`, `s = 2` the
two-term DNF with one literal per term on the distinct variables `x_{0,0}`
and `x_{1,1}` (total literal count `2`) has bad-event probability at most
`2 / 3`, the bound is strictly below one (`2 < 3`), and the space is
nonempty, so the headline DNF union-bound theorem has a genuine non-vacuous
strictly-below-one instantiation. -/
theorem matchingCollapseBad_dnf_three_two_strict :
    EventProbLe (fullMatchingSpace 3 2)
      (matchingCollapseBad
        (phpDNFFormula 3 [[(0, 0, true)], [(1, 1, true)]]) 1) 2 3 ∧
      2 < 3 ∧ (fullMatchingSpace 3 2).Nonempty :=
  ⟨matchingCollapseBad_dnf_probability_le [[(0, 0, true)], [(1, 1, true)]],
    by decide, fullMatchingSpace_three_two_nonempty⟩

end PHPFullMatchingDNFBound
end PvNP
