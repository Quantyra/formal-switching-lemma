import PvNP.PHPFullMatchingPathCodeFiberBound
import PvNP.SwitchingEncodeConstruct
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stage-indexed rows for full-matching bad-path codes

This module refines the S2121 path-code row set by keeping the row recovered at
each depth stage of a bad-path code.  The results remain finite full-matching
space counting infrastructure only: they preserve per-stage recovered row
information in the row-free fiber bound, and expose only a conditional
coarsening by a separately supplied lower bound on the number of recovered rows.

No distinct-row theorem is proved here.  The final geometric counting form
discharges only the pure row-free full-square geometric ratio; it remains
conditional on separately supplied realized row-growth.

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
open SwitchingEncodeConstruct

/-! ## Pure row-free geometric arithmetic -/

/-- One-step row-free binomial comparison.  If `n + 1 ≤ h`, then replacing a
row-free universe of size `n + 1` by size `n` costs at most a factor
`(h - s) / h` in cross-multiplied natural-number form. -/
theorem choose_rowFree_one_step_le {h s n : Nat} (hn : n + 1 ≤ h) :
    h * Nat.choose n s ≤ (h - s) * Nat.choose (n + 1) s := by
  by_cases hs : s ≤ n
  · have hs1 : s ≤ n + 1 := Nat.le_trans hs (Nat.le_succ n)
    have hsh : s ≤ h := Nat.le_trans hs1 hn
    have harith : h * (n + 1 - s) ≤ (h - s) * (n + 1) := by
      have hadded : h * (n + 1 - s) + s * (n + 1) ≤
          (h - s) * (n + 1) + s * (n + 1) := by
        calc
          h * (n + 1 - s) + s * (n + 1)
              ≤ h * (n + 1 - s) + h * s := by
                refine Nat.add_le_add_left ?_ _
                rw [Nat.mul_comm h s]
                exact Nat.mul_le_mul_left s hn
          _ = h * (n + 1) := by
                rw [← Nat.mul_add, Nat.sub_add_cancel hs1]
          _ = (h - s) * (n + 1) + s * (n + 1) := by
                rw [← Nat.add_mul, Nat.sub_add_cancel hsh]
      exact Nat.add_le_add_iff_right.mp hadded
    apply Nat.le_of_mul_le_mul_right (c := n + 1)
    · calc
        (h * Nat.choose n s) * (n + 1)
            = h * (Nat.choose n s * (n + 1)) := by ac_rfl
        _ = h * (Nat.choose (n + 1) s * (n + 1 - s)) := by
              rw [Nat.choose_mul_succ_eq]
        _ = Nat.choose (n + 1) s * (h * (n + 1 - s)) := by ac_rfl
        _ ≤ Nat.choose (n + 1) s * ((h - s) * (n + 1)) := by
              exact Nat.mul_le_mul_left _ harith
        _ = ((h - s) * Nat.choose (n + 1) s) * (n + 1) := by ac_rfl
    · exact Nat.succ_pos n
  · have hlt : n < s := Nat.lt_of_not_ge hs
    rw [Nat.choose_eq_zero_of_lt hlt]
    exact Nat.zero_le _

/-- Pure row-free geometric binomial comparison for the full square:
`choose (h-q) s` is at most `choose h s` times `((h-s)/h)^q`, stated without
division. -/
theorem choose_rowFree_geometric_le (h s q : Nat) :
    h ^ q * Nat.choose (h - q) s ≤ (h - s) ^ q * Nat.choose h s := by
  induction q with
  | zero => simp
  | succ q ih =>
      by_cases hq : q < h
      · have hstep := choose_rowFree_one_step_le (h := h) (s := s)
          (n := h - (q + 1)) (by omega)
        have hsub : h - (q + 1) + 1 = h - q := by omega
        rw [hsub] at hstep
        calc
          h ^ (q + 1) * Nat.choose (h - (q + 1)) s
              = h ^ q * (h * Nat.choose (h - (q + 1)) s) := by
                rw [Nat.pow_succ]
                ac_rfl
          _ ≤ h ^ q * ((h - s) * Nat.choose (h - q) s) := by
                exact Nat.mul_le_mul_left _ hstep
          _ = (h - s) * (h ^ q * Nat.choose (h - q) s) := by ac_rfl
          _ ≤ (h - s) * ((h - s) ^ q * Nat.choose h s) := by
                exact Nat.mul_le_mul_left _ ih
          _ = (h - s) ^ (q + 1) * Nat.choose h s := by
                rw [Nat.pow_succ]
                ac_rfl
      · by_cases hs0 : s = 0
        · simp [hs0]
        · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
          have hsubzero : h - (q + 1) = 0 := by omega
          rw [hsubzero, Nat.choose_eq_zero_of_lt hspos]
          exact Nat.zero_le _

/-- Row-free geometric-ratio inequality over the full square matching space.
This is pure finite arithmetic/counting: it uses only the cardinality formula for
`fullMatchingSpace`, not any realized row-growth theorem. -/
theorem rowFree_geometric_ratio_full (h s q : Nat) :
    h ^ q * (Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h))) ≤
      (h - s) ^ q * (fullMatchingSpace h s).card := by
  rw [card_fullMatchingSpace]
  calc
    h ^ q * (Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h)))
        = (h ^ q * Nat.choose (h - q) s) *
            Fintype.card (Equiv.Perm (Fin h)) := by ac_rfl
    _ ≤ ((h - s) ^ q * Nat.choose h s) *
          Fintype.card (Equiv.Perm (Fin h)) := by
          exact Nat.mul_le_mul_right _ (choose_rowFree_geometric_le h s q)
    _ = (h - s) ^ q *
          (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h))) := by ac_rfl

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

/-! ## Realized simple-DNF structural row growth -/

/-- For a realized canonical bad-path code coming from a simple DNF, the recovered
PHP variables are pairwise distinct.  This is only a structural statement about
the term-canonical deepest path; it makes no lower-bound claim beyond the finite
full-square PHP encoding surface. -/
theorem codeStageVar_injective_of_realized_simple {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (c : BadPathCode h tvs t)
    (hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c) :
    Function.Injective (fun k : Fin t => ((c k).1 : Fin (Nat.succ (h * h)))) := by
  classical
  rcases hreal with ⟨P, hP⟩
  rw [canonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨_hspace, hbad, henc⟩ := hP
  have hc : canonicalDepthBadCode tvs t P hbad = c := by
    unfold canonicalDepthBadEncoding at henc
    rw [dif_pos hbad] at henc
    exact Option.some.inj henc
  intro k l hkl
  let T := canonicalRestrictedDNFTree h tvs P
  have hlenk : k.1 < (deepestPath T).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le k.2 hbad
  have hlenl : l.1 < (deepestPath T).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le l.2 hbad
  have hnd : ((deepestPath T).map Prod.fst).Nodup := by
    unfold T canonicalRestrictedDNFTree
    exact deepestPath_var_nodup hsimple (fullRestrictionOf P)
  have hget : ((deepestPath T).map Prod.fst).get ⟨k.1, by simpa using hlenk⟩ =
      ((deepestPath T).map Prod.fst).get ⟨l.1, by simpa using hlenl⟩ := by
    have hkl' :
        ((canonicalDepthBadCode tvs t P hbad k).1 : Fin (Nat.succ (h * h))) =
          ((canonicalDepthBadCode tvs t P hbad l).1 : Fin (Nat.succ (h * h))) := by
      simpa [hc] using hkl
    simpa [canonicalDepthBadCode, T, hlenk, hlenl] using hkl'
  have hidx : (⟨k.1, by simpa using hlenk⟩ : Fin ((deepestPath T).map Prod.fst).length) =
      ⟨l.1, by simpa using hlenl⟩ := hnd.get_inj_iff.mp hget
  have hval :
      (⟨k.1, by simpa using hlenk⟩ : Fin ((deepestPath T).map Prod.fst).length).val =
        (⟨l.1, by simpa using hlenl⟩ : Fin ((deepestPath T).map Prod.fst).length).val :=
    congrArg (fun x : Fin ((deepestPath T).map Prod.fst).length => x.val) hidx
  exact Fin.ext hval

/-- A realized simple-DNF code of length `t` uses at most `h` columns over each
recovered row, so distinct recovered PHP variables force the structural bound
`t ≤ h * |rows|`.  This is the safe replacement for the generally false
unconditional `t ≤ |rows|` statement. -/
theorem canonicalDepthBadCodeFiberNonempty.le_h_mul_codeStageRows_card_of_simple
    {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (c : BadPathCode h tvs t)
    (hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c) :
    t <= h * (codeStageRows c).card := by
  classical
  let stagePair : Fin t -> Fin h × Fin h := fun k =>
    (codeStageRow c k, (codeStageEntry c k).2.1)
  have hinjPair : Function.Injective stagePair := by
    intro k l hkl
    have hvar : ((c k).1 : Fin (Nat.succ (h * h))) =
        ((c l).1 : Fin (Nat.succ (h * h))) := by
      have := congrArg (fun p : Fin h × Fin h => phpVar h h p.1 p.2) hkl
      simpa [stagePair, codeStageEntry_var_eq c k, codeStageEntry_var_eq c l] using this
    exact codeStageVar_injective_of_realized_simple (h := h) (s := s) (t := t)
      hsimple c hreal hvar
  have hsubset : (Finset.univ.image stagePair) ⊆
      (codeStageRows c) ×ˢ (Finset.univ : Finset (Fin h)) := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨k, _hk, rfl⟩
    exact Finset.mem_product.mpr
      ⟨(mem_codeStageRows c (codeStageRow c k)).mpr ⟨k, rfl⟩, Finset.mem_univ _⟩
  calc
    t = (Finset.univ.image stagePair).card := by
      rw [Finset.card_image_of_injective _ hinjPair, Finset.card_univ, Fintype.card_fin]
    _ <= ((codeStageRows c) ×ˢ (Finset.univ : Finset (Fin h))).card :=
      Finset.card_le_card hsubset
    _ = (codeStageRows c).card * h := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ = h * (codeStageRows c).card := by rw [Nat.mul_comm]

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

/-- S2124 specialization at `q = t`: if every realized bad-path code fiber
recovers at least `t` distinct stage rows, then the canonical depth-bad count is
bounded by the path-code count times the `t`-row-free full-square matching
multiplicity.  This theorem only instantiates the supplied realized row-growth
hypothesis; it does not prove that hypothesis. -/
theorem canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hrows : ∀ c : BadPathCode h tvs t,
      canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c ->
        t <= (codeStageRows c).card) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        (Nat.choose (h - t) s * Fintype.card (Equiv.Perm (Fin h))) := by
  exact canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge
    (h := h) (s := s) (t := t) (q := t) tvs hrows

/-- Simple-DNF structural instantiation of the realized-row consumer at
`q = t / h`.  The only row-growth input is the proved finite structural bound
`t ≤ h * |codeStageRows c|`; no stronger distinct-row claim is asserted. -/
theorem canonicalDepthBad_count_le_pathCode_mul_rowFree_of_simple_realized_div_h
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        (Nat.choose (h - t / h) s * Fintype.card (Equiv.Perm (Fin h))) := by
  refine canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge
    (h := h) (s := s) (t := t) (q := t / h) tvs ?_
  intro c hreal
  exact Nat.div_le_of_le_mul
    (canonicalDepthBadCodeFiberNonempty.le_h_mul_codeStageRows_card_of_simple
      (h := h) (s := s) (t := t) hsimple c hreal)

/-- Geometric full-square counting form.  The row-growth hypothesis is the S2124
`q = t` realized-fiber assumption; the pure row-free geometric-ratio inequality
for the full square matching space is discharged by
`rowFree_geometric_ratio_full`.  This theorem does not prove realized row growth
and does not extend the model to rectangular `p > h` injection spaces. -/
theorem canonicalDepthBad_probability_geometric_le_of_realized_codeStageRows_card_ge_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hrows : ∀ c : BadPathCode h tvs t,
      canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c ->
        t <= (codeStageRows c).card) :
    h ^ t * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        ((h - s) ^ t * (fullMatchingSpace h s).card) := by
  have hcount :=
    canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge_t
      (h := h) (s := s) (t := t) tvs hrows
  calc
    h ^ t * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
        <= h ^ t * (Fintype.card (BadPathCode h tvs t) *
          (Nat.choose (h - t) s * Fintype.card (Equiv.Perm (Fin h)))) := by
          exact Nat.mul_le_mul_left _ hcount
    _ = Fintype.card (BadPathCode h tvs t) *
          (h ^ t * (Nat.choose (h - t) s * Fintype.card (Equiv.Perm (Fin h)))) := by
          ac_rfl
    _ <= Fintype.card (BadPathCode h tvs t) *
           ((h - s) ^ t * (fullMatchingSpace h s).card) := by
            exact Nat.mul_le_mul_left _ (rowFree_geometric_ratio_full h s t)

/-- Geometric full-square counting corollary from the simple-DNF structural
realized-fiber replacement, with the Lean-friendly row parameter `q = t / h`. -/
theorem canonicalDepthBad_probability_geometric_le_of_simple_realized_div_h
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    h ^ (t / h) * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Fintype.card (BadPathCode h tvs t) *
        ((h - s) ^ (t / h) * (fullMatchingSpace h s).card) := by
  have hcount :=
    canonicalDepthBad_count_le_pathCode_mul_rowFree_of_simple_realized_div_h
      (h := h) (s := s) (t := t) tvs hsimple
  calc
    h ^ (t / h) * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
        <= h ^ (t / h) * (Fintype.card (BadPathCode h tvs t) *
          (Nat.choose (h - t / h) s * Fintype.card (Equiv.Perm (Fin h)))) := by
          exact Nat.mul_le_mul_left _ hcount
    _ = Fintype.card (BadPathCode h tvs t) *
          (h ^ (t / h) *
            (Nat.choose (h - t / h) s * Fintype.card (Equiv.Perm (Fin h)))) := by
          ac_rfl
    _ <= Fintype.card (BadPathCode h tvs t) *
           ((h - s) ^ (t / h) * (fullMatchingSpace h s).card) := by
           exact Nat.mul_le_mul_left _ (rowFree_geometric_ratio_full h s (t / h))

/-- Thin finite-probability interface for the geometric full-square bound.  This
is just the `EventProbLe` wrapper around
`canonicalDepthBad_probability_geometric_le_of_realized_codeStageRows_card_ge_t`;
it inherits the same supplied realized row-growth hypothesis and proves no such
growth theorem, rectangular injection result, or PHP switching lemma. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_realized_codeStageRows_card_ge_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hrows : ∀ c : BadPathCode h tvs t,
      canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c ->
        t <= (codeStageRows c).card) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
      (Fintype.card (BadPathCode h tvs t) * (h - s) ^ t) (h ^ t) := by
  unfold EventProbLe
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    canonicalDepthBad_probability_geometric_le_of_realized_codeStageRows_card_ge_t
      (h := h) (s := s) (t := t) tvs hrows

/-- `EventProbLe` wrapper for the simple-DNF structural replacement at
`q = t / h`. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
      (Fintype.card (BadPathCode h tvs t) * (h - s) ^ (t / h)) (h ^ (t / h)) := by
  unfold EventProbLe
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    canonicalDepthBad_probability_geometric_le_of_simple_realized_div_h
      (h := h) (s := s) (t := t) tvs hsimple

end PHPFullMatchingStageRows
end PvNP
