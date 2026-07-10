import PvNP.PHPFullMatchingCodeFactor

/-!
# Realized-code count for full-matching bad paths

This module replaces the S2125/S2126 all-`BadPathCode` factor by the number of
codes whose canonical full-square matching fiber is actually nonempty.  The
scope remains finite counting and `EventProbLe` bookkeeping over
`fullMatchingSpace h s` only.

No PHP switching lemma, Frege/PHP lower bound, NP/circuit lower bound,
arbitrary AC0 statement, rectangular `p > h` result, or P-vs-NP claim is stated
or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingRealizedCodeCount

open PHPFullMatchingCanonicalDT
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingStageRows
open PHPFullMatchingProbability
open PHPFullMatchingDistribution
open PHPFullMatchingCodeFactor
open RestrictedPHPFloor
open SwitchingEncodeConstruct

/-! ## Realized bad-path codes -/

/-- The finite set of bad-path codes whose canonical full-matching bad-event
fiber is nonempty. -/
noncomputable def realizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Finset (BadPathCode h tvs t) :=
  by
    classical
    exact Finset.univ.filter
      (canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs)

/-- Membership in `realizedBadPathCodes` is exactly nonemptiness of the canonical
bad-code fiber. -/
theorem mem_realizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (c : BadPathCode h tvs t) :
    c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ↔
      canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c := by
  classical
  simp [realizedBadPathCodes]

/-- The realized-code set is bounded by the ambient bad-path-code type. -/
theorem realizedBadPathCodes_card_le_badPathCode {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <=
      Fintype.card (BadPathCode h tvs t) := by
  classical
  rw [← Finset.card_univ]
  exact Finset.card_le_card (by intro c _hc; exact Finset.mem_univ c)

/-! ## Counting over realized fibers only -/

/-- Empty/unrealized codes have zero canonical bad-code fiber. -/
theorem canonicalDepthBadCodeFiber_card_eq_zero_of_not_mem_realizedBadPathCodes
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t)
    (hc : c ∉ realizedBadPathCodes (h := h) (s := s) (t := t) tvs) :
    (canonicalDepthBadCodeFiber (h := h) (s := s) (t := t) tvs c).card = 0 := by
  classical
  have hnot : ¬ canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c := by
    intro hreal
    exact hc ((mem_realizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mpr hreal)
  rw [Finset.card_eq_zero]
  exact Finset.eq_empty_iff_forall_not_mem.mpr (fun P hP => hnot ⟨P, hP⟩)

/-- Realized-code-only coarsening: the uniform row-free multiplicity is paid only
for codes whose canonical bad-path fiber is nonempty. -/
theorem canonicalDepthBad_count_le_realizedCode_mul_rowFree_of_realized_codeStageRows_card_ge
    {h s t q : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hrows : ∀ c : BadPathCode h tvs t,
      c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ->
        q <= (codeStageRows c).card) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
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
  let C := Nat.choose (h - q) s * Fintype.card (Equiv.Perm (Fin h))
  calc
    (∑ c : BadPathCode h tvs t,
        (Finset.filter (fun P => (canonicalDepthBadEncoding h tvs t P).2 = some c)
          (Finset.filter (canonicalDepthBad h tvs t) (fullMatchingSpace h s))).card)
        <= ∑ c : BadPathCode h tvs t,
          if c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs then C else 0 := by
          refine Finset.sum_le_sum ?_
          intro c _hc
          by_cases hmem : c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs
          · simp [hmem, C]
            rw [Finset.filter_filter]
            exact canonicalDepthBadCodeFiber_count_le_rowFree_of_realized_codeStageRows_card_ge
              (h := h) (s := s) (t := t) (q := q) tvs c
              (fun _ => hrows c hmem)
          · have hzero :=
              canonicalDepthBadCodeFiber_card_eq_zero_of_not_mem_realizedBadPathCodes
                (h := h) (s := s) (t := t) tvs c hmem
            rw [Finset.filter_filter]
            simpa [hmem, canonicalDepthBadCodeFiber] using Nat.le_of_eq hzero
    _ = (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card * C := by
          rw [← Finset.sum_filter]
          simp [realizedBadPathCodes, C]

/-- Simple-DNF structural instantiation at `q = t / h`, with the code factor
restricted to realized bad-path codes. -/
theorem canonicalDepthBad_count_le_realizedCode_mul_rowFree_of_simple_realized_div_h
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
        (Nat.choose (h - t / h) s * Fintype.card (Equiv.Perm (Fin h))) := by
  refine canonicalDepthBad_count_le_realizedCode_mul_rowFree_of_realized_codeStageRows_card_ge
    (h := h) (s := s) (t := t) (q := t / h) tvs ?_
  intro c hmem
  exact Nat.div_le_of_le_mul
    (canonicalDepthBadCodeFiberNonempty.le_h_mul_codeStageRows_card_of_simple
      (h := h) (s := s) (t := t) hsimple c
      ((mem_realizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mp hmem))

/-- Geometric full-square counting form with the numerator using only realized
bad-path codes. -/
theorem canonicalDepthBad_probability_geometric_le_of_simple_realizedCode_div_h
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    h ^ (t / h) * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
        ((h - s) ^ (t / h) * (fullMatchingSpace h s).card) := by
  have hcount :=
    canonicalDepthBad_count_le_realizedCode_mul_rowFree_of_simple_realized_div_h
      (h := h) (s := s) (t := t) tvs hsimple
  calc
    h ^ (t / h) * eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
        <= h ^ (t / h) *
          ((realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
            (Nat.choose (h - t / h) s * Fintype.card (Equiv.Perm (Fin h)))) := by
          exact Nat.mul_le_mul_left _ hcount
    _ = (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
          (h ^ (t / h) *
            (Nat.choose (h - t / h) s * Fintype.card (Equiv.Perm (Fin h)))) := by
          ac_rfl
    _ <= (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
          ((h - s) ^ (t / h) * (fullMatchingSpace h s).card) := by
          exact Nat.mul_le_mul_left _ (rowFree_geometric_ratio_full h s (t / h))

/-- `EventProbLe` wrapper for the realized-code geometric simple-DNF bound. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_simple_realizedCode_div_h
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
      ((realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
        (h - s) ^ (t / h)) (h ^ (t / h)) := by
  unfold EventProbLe
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    canonicalDepthBad_probability_geometric_le_of_simple_realizedCode_div_h
      (h := h) (s := s) (t := t) tvs hsimple

/-! ## Formal obstruction for the realized-code factor -/

/-- In a regime where the row-free factor is at least one, any below-one
realized-code numerator forces the realized-code factor itself below the
denominator. -/
theorem realizedCode_nontrivial_requires_realized_card_lt_denominator
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hfree : 1 <= (h - s) ^ (t / h))
    (hnum : (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
        (h - s) ^ (t / h) < h ^ (t / h)) :
    (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card < h ^ (t / h) := by
  calc
    (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card
        = (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card * 1 := by
          rw [Nat.mul_one]
    _ <= (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
          (h - s) ^ (t / h) := by
          exact Nat.mul_le_mul_left _ hfree
    _ < h ^ (t / h) := hnum

/-- If the denominator is already no larger than the realized-code factor, this
realized-code route cannot give a below-one bound whenever the row-free factor is
at least one. -/
theorem realizedCode_nontrivial_impossible_of_denominator_le_realized_card
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hfree : 1 <= (h - s) ^ (t / h)) :
    h ^ (t / h) <=
        (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card ->
    ¬ ((realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
        (h - s) ^ (t / h) < h ^ (t / h)) := by
  intro hbig hnum
  exact not_lt_of_ge hbig
    (realizedCode_nontrivial_requires_realized_card_lt_denominator tvs hfree hnum)

end PHPFullMatchingRealizedCodeCount
end PvNP
