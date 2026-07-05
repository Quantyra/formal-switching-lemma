import PvNP.PHPFullMatchingCompressedBadPathCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Shared path-code fiber bound over the full matching space

This module proves the first compressed bad-set count in this artifact over
the full square PHP matching space whose encoder does NOT retain the original
matching point.  The only shared data is the path code from
`PHPFullMatchingBadPathEncoding`, drawn from a `P`-independent code space:
bad matching points are grouped by their canonical deepest-path code, and
each code fiber is bounded by the row-free multiplicity count of
`PHPFullMatchingCompressedBadPathCount`.

Concretely:

* `codeRows c` is the set of pigeon rows touched by a path code's variables,
  and it is nonempty as soon as the code has positive length
  (`codeRows_nonempty`).
* Every bad point mapped to code `c` leaves all rows of `codeRows c` free, so
  each code fiber has at most `choose (h - |codeRows c|) s * h!` points
  (`canonicalDepthBad_fiber_count_le`).
* Summing over codes gives the headline compressed count (for `1 <= t`)
  (`canonicalDepthBad_count_le_pathCode_mul_rowFree`): the depth-`t` bad event
  has at most `card (BadPathCode) * (choose (h-1) s * h!)` points — the first
  factor no longer contains the matching space itself.
* Cross-multiplying with `star_ratio_full` gives the ratio form
  (`canonicalDepthBad_ratio_le`).
* At `h = 3`, `s = 2`, `t = 1` with the single-literal demo DNF the bound
  `2 * (choose 2 2 * 3!) = 12` is strictly below the space size `18`
  (`demo_bound_lt_space`) and the bad event is nonempty
  (`demo_bad_count_pos`), so the compressed count is non-vacuous and
  genuinely below the trivial full-space bound.

The code map is many-to-one and the counting is fiberwise
(multiplicity-bounded), not an injectivity-based Razborov-style encoding.

HONEST SCOPE STATEMENT: this is the first fiber-bounded compressed count in
this artifact over the full matching space — the encoder forgets the original
matching point, and fibers are bounded by row-free multiplicity.  But the
path-code space is still the coarse support-based code space (of
`|support|^t * 2^t` shape), and the coarse corollary exploits only ONE
guaranteed free row (`choose (h-1) s`).  In relative form the headline bound
is `(2 * |support|)^t * (h - s) / h` times the space size, so it improves on
the trivial full-space bound only when the star fraction is below
`(2 * |support|)^(-t)`; it weakens as `t` grows, whereas a switching lemma
must strengthen geometrically in `t`.  This is NOT a geometric
`(8w)^s`-style bound, NOT a
depth-`t` canonical decision-tree encoding argument with per-stage
information recovery, and NOT a PHP switching lemma.  The space is the square
`h x h` permutation-matching space only; rectangular `p > h` injection spaces
remain unformalized.  No Frege/PHP proof-size lower bound, NP/circuit lower
bound, or P-vs-NP claim is stated or proved.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingPathCodeFiberBound

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open RestrictedPHPFloor
open PHPSearchFloor
open PHPMatchingDistribution
open PHPFullMatchingDistribution
open PHPFullMatchingCanonicalDT
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCompressedBadPathCount
open PHPFullMatchingProbability
open SwitchingCardLemma

/-! ## Rows touched by a path code -/

open Classical in
/-- The set of pigeon rows touched by a path code's queried variables.  This
depends only on the code, never on a matching point. -/
noncomputable def codeRows {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) : Finset (Fin h) :=
  Finset.univ.filter (fun i => ∃ k : Fin t, ∃ j : Fin h,
    ((c k).1 : Fin (Nat.succ (h * h))) = phpVar h h i j)

theorem mem_codeRows {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (i : Fin h) :
    i ∈ codeRows c ↔ ∃ k : Fin t, ∃ j : Fin h,
      ((c k).1 : Fin (Nat.succ (h * h))) = phpVar h h i j := by
  unfold codeRows
  rw [Finset.mem_filter]
  exact ⟨fun hp => hp.2, fun hp => ⟨Finset.mem_univ i, hp⟩⟩

/-- A positive-length path code touches at least one pigeon row, because its
first queried variable is certified to lie in the PHP DNF support, whose
members are all of the form `phpVar h h i j`. -/
theorem codeRows_nonempty {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (ht : 1 <= t) (c : BadPathCode h tvs t) :
    (codeRows c).Nonempty := by
  have hk : 0 < t := ht
  have hv : ((c ⟨0, hk⟩).1 : Fin (Nat.succ (h * h))) ∈ phpDNFVarSet h tvs :=
    (c ⟨0, hk⟩).1.2
  unfold phpDNFVarSet at hv
  rw [List.mem_toFinset] at hv
  obtain ⟨e, _he, heq⟩ := List.mem_map.mp hv
  exact ⟨e.1, (mem_codeRows c e.1).mpr ⟨⟨0, hk⟩, e.2.1, heq.symm⟩⟩

/-! ## Code fibers leave their code rows free -/

/-- Every variable recorded by the canonical bad-path code is free under the
full matching restriction of the bad point it was extracted from. -/
theorem canonicalDepthBadCode_fst_free {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P) (k : Fin t) :
    fullRestrictionOf P
      ((canonicalDepthBadCode tvs t P hbad k).1 : Fin (Nat.succ (h * h))) =
      none := by
  have hlen : k.1 < (deepestPath (canonicalRestrictedDNFTree h tvs P)).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le k.2 hbad
  have hvdmem : (deepestPath (canonicalRestrictedDNFTree h tvs P)).get ⟨k.1, hlen⟩
      ∈ deepestPath (canonicalRestrictedDNFTree h tvs P) :=
    List.get_mem (deepestPath (canonicalRestrictedDNFTree h tvs P)) k.1 hlen
  exact deepestPath_canonicalRestrictedDNFTree_free P tvs _ hvdmem

/-- Any bad matching point whose encoding carries the path code `c` leaves
every row of `codeRows c` free.  This is the shared-fiber containment: the
constraint depends only on `c`, not on the point. -/
theorem fullRowsFree_codeRows_of_encoding_eq_some {h t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P)
    (henc : (canonicalDepthBadEncoding h tvs t P).2 = some c) :
    fullRowsFree (codeRows c) P := by
  have hc : canonicalDepthBadCode tvs t P hbad = c := by
    unfold canonicalDepthBadEncoding at henc
    rw [dif_pos hbad] at henc
    have h2 : some (canonicalDepthBadCode tvs t P hbad) = some c := henc
    exact Option.some.inj h2
  intro i hi hiP
  obtain ⟨k, j, hkj⟩ := (mem_codeRows c i).mp hi
  have hfree : fullRestrictionOf P
      ((c k).1 : Fin (Nat.succ (h * h))) = none := by
    rw [← hc]
    exact canonicalDepthBadCode_fst_free tvs t P hbad k
  rw [hkj, fullRestrictionOf_phpVar_eq_none_iff] at hfree
  exact hfree hiP

/-! ## Per-code fiber bound -/

/-- **Shared path-code fiber bound.**  For every fixed path code `c`, the set
of bad matching points encoded to `c` has at most
`choose (h - |codeRows c|) s * h!` elements: the fiber injects into the
row-free multiplicity set of `codeRows c`, whose exact count is
`fullRowsFree_count`.  The original matching point is nowhere retained. -/
theorem canonicalDepthBad_fiber_count_le {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) :
    ((fullMatchingSpace h s).filter (fun P => canonicalDepthBad h tvs t P ∧
        (canonicalDepthBadEncoding h tvs t P).2 = some c)).card <=
      Nat.choose (h - (codeRows c).card) s *
        Fintype.card (Equiv.Perm (Fin h)) := by
  classical
  have hsubset : (fullMatchingSpace h s).filter
      (fun P => canonicalDepthBad h tvs t P ∧
        (canonicalDepthBadEncoding h tvs t P).2 = some c) ⊆
      (fullMatchingSpace h s).filter (fullRowsFree (codeRows c)) := by
    intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨hP.1,
      fullRowsFree_codeRows_of_encoding_eq_some tvs c P hP.2.1 hP.2.2⟩
  have hcount := fullRowsFree_count h s (codeRows c)
  unfold eventCount at hcount
  exact Nat.le_trans (Finset.card_le_card hsubset) (Nat.le_of_eq hcount)

/-! ## The compressed headline count -/

/-- **Compressed bad-path count over the full matching space.**  The depth-`t`
bad event is bounded by the size of the `P`-independent code space times the
single-free-row multiplicity `choose (h-1) s * h!`.  Unlike the S2119
conservative count, the first factor no longer contains the matching space:
the decomposition is fiberwise over the shared code space, the `none` fiber is
empty on the bad set, and each `some c` fiber is bounded by its row-free count
coarsened through the at-least-one-free-row estimate from
`codeRows_nonempty`. -/
theorem canonicalDepthBad_count_le_pathCode_mul_rowFree {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (ht : 1 <= t) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))) := by
  classical
  unfold eventCount
  have hmap : forall P, P ∈
      (fullMatchingSpace h s).filter (canonicalDepthBad h tvs t) ->
      (canonicalDepthBadEncoding h tvs t P).2 ∈
        (Finset.univ : Finset (Option (BadPathCode h tvs t))) :=
    fun P _ => Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  rw [Fintype.sum_option]
  have hnone : forall P, P ∈
      (fullMatchingSpace h s).filter (canonicalDepthBad h tvs t) ->
      ¬ ((canonicalDepthBadEncoding h tvs t P).2 = none) := by
    intro P hP hcontra
    have hbad : canonicalDepthBad h tvs t P := (Finset.mem_filter.mp hP).2
    unfold canonicalDepthBadEncoding at hcontra
    rw [dif_pos hbad] at hcontra
    have h2 : some (canonicalDepthBadCode tvs t P hbad) =
        (none : Option (BadPathCode h tvs t)) := hcontra
    exact Option.noConfusion h2
  rw [Finset.filter_false_of_mem hnone, Finset.card_empty, Nat.zero_add]
  have hfiber : forall c : BadPathCode h tvs t,
      (((fullMatchingSpace h s).filter (canonicalDepthBad h tvs t)).filter
        (fun P => (canonicalDepthBadEncoding h tvs t P).2 = some c)).card <=
        Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)) := by
    intro c
    rw [Finset.filter_filter]
    refine Nat.le_trans (canonicalDepthBad_fiber_count_le tvs c) ?_
    refine Nat.mul_le_mul ?_ (Nat.le_refl _)
    have hpos : 0 < (codeRows c).card :=
      Finset.card_pos.mpr (codeRows_nonempty ht c)
    exact Nat.choose_le_choose s (by omega)
  refine Nat.le_trans (Finset.sum_le_sum (fun c _ => hfiber c)) ?_
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

/-! ## Ratio corollary -/

/-- Cross-multiplied probability form of the compressed count: the bad-event
probability is at most `card (BadPathCode) * (h - s) / h`.  Pure `Nat`
algebra over the headline count via `star_ratio_full`. -/
theorem canonicalDepthBad_ratio_le {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (ht : 1 <= t) :
    h * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        ((h - s) * (fullMatchingSpace h s).card) := by
  calc
    h * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
        <= h * (Fintype.card (BadPathCode h tvs t) *
            (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)))) :=
          Nat.mul_le_mul (Nat.le_refl h)
            (canonicalDepthBad_count_le_pathCode_mul_rowFree tvs ht)
    _ = Fintype.card (BadPathCode h tvs t) *
          (h * (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)))) := by
        rw [Nat.mul_left_comm]
    _ = Fintype.card (BadPathCode h tvs t) *
          ((h - s) * (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h)))) := by
        rw [star_ratio_full]
    _ = Fintype.card (BadPathCode h tvs t) *
          ((h - s) * (fullMatchingSpace h s).card) := by
        rw [← card_fullMatchingSpace]

/-! ## Non-vacuity at `h = 3`, `s = 2`, `t = 1` -/

/-- Demo DNF data: one term with one positive literal on `x_{0,0}`. -/
def demoTvs : List (List (Fin 3 × Fin 3 × Bool)) := [[(0, 0, true)]]

/-- The demo path-code space has exactly `2` elements: one variable choice
times two directions, to the first power. -/
theorem card_badPathCode_demo : Fintype.card (BadPathCode 3 demoTvs 1) = 2 := by
  have hcongr : Fintype.card (BadPathCode 3 demoTvs 1) =
      Fintype.card (Fin 1 ->
        {v : Fin (Nat.succ (3 * 3)) // v ∈ phpDNFVarSet 3 demoTvs} × Bool) :=
    Fintype.card_congr (Equiv.refl _)
  have hsub : Fintype.card
      {v : Fin (Nat.succ (3 * 3)) // v ∈ phpDNFVarSet 3 demoTvs} = 1 := by
    decide
  rw [hcongr, Fintype.card_fun, Fintype.card_fin, pow_one, Fintype.card_prod,
    Fintype.card_bool, hsub]

/-- The compressed demo bound `2 * (choose 2 2 * 3!) = 12` is strictly below
the full space size `choose 3 2 * 3! = 18`: the compressed count genuinely
beats the trivial full-space bound at this instance. -/
theorem demo_bound_lt_space :
    Fintype.card (BadPathCode 3 demoTvs 1) *
        (Nat.choose 2 2 * Fintype.card (Equiv.Perm (Fin 3))) <
      (fullMatchingSpace 3 2).card := by
  rw [card_badPathCode_demo, card_fullMatchingSpace, Fintype.card_perm,
    Fintype.card_fin]
  decide

/-- Demo matching point: pigeons `{1, 2}` fixed along the identity. -/
def demoP : Finset (Fin 3) × Equiv.Perm (Fin 3) :=
  ({1, 2}, Equiv.refl (Fin 3))

theorem demoP_mem : demoP ∈ fullMatchingSpace 3 2 := by
  unfold fullMatchingSpace demoP
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · unfold subsetSpace
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by decide⟩
  · unfold permSpace
    exact Finset.mem_univ _

theorem demoP_free : fullRestrictionOf demoP (phpVar 3 3 0 0) = none := by
  rw [fullRestrictionOf_phpVar_eq_none_iff]
  decide

theorem demo_dnfRestrict :
    dnfRestrict (fullRestrictionOf demoP) (phpDNFAsDNF 3 demoTvs) =
      [[phpLit 3 ((0 : Fin 3), (0 : Fin 3), true)]] := by
  have hfree : fullRestrictionOf demoP (phpVar 3 3 0 0) = none := demoP_free
  simp [dnfRestrict, termRestrict, phpDNFAsDNF, demoTvs, phpTermAsTerm,
    phpLit, hfree]

/-- The demo point is depth-`1` bad: its restricted canonical tree keeps the
surviving literal as a decision node. -/
theorem demoP_bad : canonicalDepthBad 3 demoTvs 1 demoP := by
  show 1 <= dtDepth (canonicalRestrictedDNFTree 3 demoTvs demoP)
  unfold canonicalRestrictedDNFTree
  rw [demo_dnfRestrict, termCanonicalDT_cons_cons, dtDepth_node]
  exact Nat.le_add_right 1 _

/-- Non-vacuity: the depth-`1` bad event of the demo DNF is nonempty, so the
strict inequality `demo_bound_lt_space` bounds a genuinely nonempty event. -/
theorem demo_bad_count_pos :
    0 < eventCount (fullMatchingSpace 3 2) (canonicalDepthBad 3 demoTvs 1) := by
  unfold eventCount
  rw [Finset.card_pos]
  exact ⟨demoP, Finset.mem_filter.mpr ⟨demoP_mem, demoP_bad⟩⟩

end PHPFullMatchingPathCodeFiberBound
end PvNP
