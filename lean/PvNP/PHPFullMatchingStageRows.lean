import PvNP.PHPFullMatchingPathCodeFiberBound
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stage-indexed rows for full-matching bad-path codes

This module refines the S2121 path-code row set by keeping the row recovered at
each depth stage of a bad-path code.  The results remain finite full-matching
space counting infrastructure only: they preserve per-stage recovered row
information in the row-free fiber bound, and expose only a conditional
coarsening by a separately supplied lower bound on the number of recovered rows.

No distinct-row theorem is proved here, and no geometric-in-`t` consequence is
claimed.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingStageRows

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
open PHPFullMatchingPathCodeFiberBound
open PHPFullMatchingProbability
open SwitchingCardLemma

/-! ## Stage-indexed row accessors -/

open Classical in
private theorem codeStageEntry_exists {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) :
    ∃ e : Fin h × Fin h × Bool,
      e ∈ tvs.join ∧ phpVar h h e.1 e.2.1 =
        ((c k).1 : Fin (Nat.succ (h * h))) := by
  have hv : ((c k).1 : Fin (Nat.succ (h * h))) ∈ phpDNFVarSet h tvs :=
    (c k).1.2
  unfold phpDNFVarSet at hv
  rw [List.mem_toFinset] at hv
  exact List.mem_map.mp hv

open Classical in
/-- Decode the PHP literal occurrence whose variable is stored at stage `k` of a
bad-path code.  The boolean sign is retained only as occurrence metadata; the
stored code variable determines the row/column. -/
noncomputable def codeStageEntry {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) : Fin h × Fin h × Bool :=
  Classical.choose (codeStageEntry_exists c k)

/-- The decoded row at stage `k`. -/
noncomputable def codeStageRow {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) : Fin h :=
  (codeStageEntry c k).1

/-- The finite image of rows recovered stage-by-stage by the bad-path code;
duplicates are removed by `Finset.image`. -/
noncomputable def codeStageRows {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) : Finset (Fin h) :=
  Finset.univ.image (codeStageRow c)

/-- Each decoded stage entry has the PHP variable stored in the code. -/
theorem codeStageEntry_var_eq {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) :
    phpVar h h (codeStageRow c k) (codeStageEntry c k).2.1 =
      ((c k).1 : Fin (Nat.succ (h * h))) := by
  unfold codeStageRow codeStageEntry
  exact (Classical.choose_spec (codeStageEntry_exists c k)).2

theorem mem_codeStageRows {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (i : Fin h) :
    i ∈ codeStageRows c ↔ ∃ k : Fin t, codeStageRow c k = i := by
  unfold codeStageRows
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, _hk, hkrow⟩
    exact ⟨k, hkrow⟩
  · rintro ⟨k, hkrow⟩
    exact ⟨k, Finset.mem_univ k, hkrow⟩

/-! ## Stage rows are free in every matching point in the corresponding fiber -/

/-- Every recovered row at a fixed stage is outside the selected row set for any
bad point whose bad-path encoding is the code `c`. -/
theorem codeStageRow_free_of_encoding_eq_some {h t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P)
    (henc : (canonicalDepthBadEncoding h tvs t P).2 = some c)
    (k : Fin t) :
    codeStageRow c k ∉ P.1 := by
  have hc : canonicalDepthBadCode tvs t P hbad = c := by
    unfold canonicalDepthBadEncoding at henc
    rw [dif_pos hbad] at henc
    exact Option.some.inj henc
  have hfree : fullRestrictionOf P
      ((c k).1 : Fin (Nat.succ (h * h))) = none := by
    rw [← hc]
    exact canonicalDepthBadCode_fst_free tvs t P hbad k
  have hvar := codeStageEntry_var_eq c k
  rw [← hvar, fullRestrictionOf_phpVar_eq_none_iff] at hfree
  exact hfree

/-- All rows recovered by the stage-indexed code are free in any matching point
belonging to that code fiber. -/
theorem fullRowsFree_codeStageRows_of_encoding_eq_some {h t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P)
    (henc : (canonicalDepthBadEncoding h tvs t P).2 = some c) :
    fullRowsFree (codeStageRows c) P := by
  intro i hi
  obtain ⟨k, hkrow⟩ := (mem_codeStageRows c i).mp hi
  rw [← hkrow]
  exact codeStageRow_free_of_encoding_eq_some tvs c P hbad henc k

/-! ## Counting with recovered stage rows preserved -/

/-- The realized canonical bad-path fiber for a fixed code, inside the finite
full matching space. -/
noncomputable def canonicalDepthBadCodeFiber {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) : Finset (Finset (Fin h) × Equiv.Perm (Fin h)) :=
  (fullMatchingSpace h s).filter (fun P => canonicalDepthBad h tvs t P ∧
    (canonicalDepthBadEncoding h tvs t P).2 = some c)

/-- A code is realized when its canonical bad-path fiber is nonempty. -/
def canonicalDepthBadCodeFiberNonempty {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) : Prop :=
  (canonicalDepthBadCodeFiber (h := h) (s := s) (t := t) tvs c).Nonempty

/-- Fiber bound preserving all rows recovered by the stage-indexed code. -/
theorem canonicalDepthBad_fiber_count_le_stageRows {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) :
    ((fullMatchingSpace h s).filter (fun P => canonicalDepthBad h tvs t P ∧
        (canonicalDepthBadEncoding h tvs t P).2 = some c)).card <=
      Nat.choose (h - (codeStageRows c).card) s *
        Fintype.card (Equiv.Perm (Fin h)) := by
  classical
  have hsubset : (fullMatchingSpace h s).filter
      (fun P => canonicalDepthBad h tvs t P ∧
        (canonicalDepthBadEncoding h tvs t P).2 = some c) ⊆
      (fullMatchingSpace h s).filter (fullRowsFree (codeStageRows c)) := by
    intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨hP.1,
      fullRowsFree_codeStageRows_of_encoding_eq_some tvs c P hP.2.1 hP.2.2⟩
  have hcount := fullRowsFree_count h s (codeStageRows c)
  unfold eventCount at hcount
  exact Nat.le_trans (Finset.card_le_card hsubset) (Nat.le_of_eq hcount)

/-- Realized-code-only coarsening for one fiber: the `q`-row hypothesis is
needed only if this code's canonical bad-path fiber is nonempty; empty fibers
contribute zero. -/
theorem canonicalDepthBadCodeFiber_count_le_rowFree_of_realized_codeStageRows_card_ge
    {h s t q : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t)
    (hrows : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c ->
      q <= (codeStageRows c).card) :
    (canonicalDepthBadCodeFiber (h := h) (s := s) (t := t) tvs c).card <=
      Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h)) := by
  classical
  by_cases hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c
  · calc
      (canonicalDepthBadCodeFiber (h := h) (s := s) (t := t) tvs c).card
          <= Nat.choose (h - (codeStageRows c).card) s *
              Fintype.card (Equiv.Perm (Fin h)) := by
          simpa [canonicalDepthBadCodeFiber] using
            (canonicalDepthBad_fiber_count_le_stageRows (h := h) (s := s) (t := t) tvs c)
      _ <= Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h)) := by
          refine Nat.mul_le_mul ?_ (Nat.le_refl _)
          exact Nat.choose_le_choose s (Nat.sub_le_sub_left (hrows hreal) h)
  · have hzero :
        (canonicalDepthBadCodeFiber (h := h) (s := s) (t := t) tvs c).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_iff_forall_not_mem.mpr (fun P hP => hreal ⟨P, hP⟩)
    rw [hzero]
    exact Nat.zero_le _

/-- Sum of stage-row-preserving fiber bounds over all bad-path codes. -/
theorem canonicalDepthBad_count_le_sum_codeStageRows {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      ∑ c : BadPathCode h tvs t,
        Nat.choose (h - (codeStageRows c).card) s *
          Fintype.card (Equiv.Perm (Fin h)) := by
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
    exact Option.noConfusion hcontra
  rw [Finset.filter_false_of_mem hnone, Finset.card_empty, Nat.zero_add]
  refine Finset.sum_le_sum ?_
  intro c _hc
  rw [Finset.filter_filter]
  exact canonicalDepthBad_fiber_count_le_stageRows tvs c

/-- Conditional coarsening: if every code recovers at least `q` distinct rows,
then the stage-row-preserving sum is bounded by the uniform `choose (h-q) s`
row-free multiplicity times the path-code count.  This theorem does not prove
the lower-bound hypothesis for any concrete `q`. -/
theorem canonicalDepthBad_count_le_pathCode_mul_rowFree_of_codeStageRows_card_ge
    {h s t q : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hrows : ∀ c : BadPathCode h tvs t, q ≤ (codeStageRows c).card) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        (Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h))) := by
  classical
  refine Nat.le_trans (canonicalDepthBad_count_le_sum_codeStageRows tvs) ?_
  calc
    (∑ c : BadPathCode h tvs t,
        Nat.choose (h - (codeStageRows c).card) s *
          Fintype.card (Equiv.Perm (Fin h)))
        <= ∑ _c : BadPathCode h tvs t,
          Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h)) := by
          refine Finset.sum_le_sum ?_
          intro c _hc
          refine Nat.mul_le_mul ?_ (Nat.le_refl _)
          exact Nat.choose_le_choose s (Nat.sub_le_sub_left (hrows c) h)
    _ = Fintype.card (BadPathCode h tvs t) *
          (Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h))) := by
           rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

/-- Realized-code-only coarsening: it suffices to supply the `q`-row lower bound
only for bad-path codes whose canonical bad-path fiber is nonempty.  Empty code
fibers contribute zero and impose no row-growth obligation. -/
theorem canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge
    {h s t q : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hrows : ∀ c : BadPathCode h tvs t,
      canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c ->
        q <= (codeStageRows c).card) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        (Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h))) := by
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
    exact Option.noConfusion hcontra
  rw [Finset.filter_false_of_mem hnone, Finset.card_empty, Nat.zero_add]
  calc
    (∑ c : BadPathCode h tvs t,
        (Finset.filter (fun P => (canonicalDepthBadEncoding h tvs t P).2 = some c)
          (Finset.filter (canonicalDepthBad h tvs t) (fullMatchingSpace h s))).card)
        <= ∑ _c : BadPathCode h tvs t,
          Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h)) := by
          refine Finset.sum_le_sum ?_
          intro c _hc
          rw [Finset.filter_filter]
          exact canonicalDepthBadCodeFiber_count_le_rowFree_of_realized_codeStageRows_card_ge
            (h := h) (s := s) (t := t) (q := q) tvs c (hrows c)
    _ = Fintype.card (BadPathCode h tvs t) *
          (Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h))) := by
          rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

end PHPFullMatchingStageRows
end PvNP
