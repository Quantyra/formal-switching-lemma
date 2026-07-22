import PvNP.PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
import PvNP.PHPMatchingEncodePackageFiber

/-!
# S2215: ell-free package bound versus the honest denominator

For the fixed `Fin 4` / `searchD4mp` / `t = 3` package, the S2214 `G1`+`G2`
grade bound removes the ell-dependent `G3` factor.  Summing its only possible
grades gives `3072` at `ell = 3`, which is still **TRIVIAL** versus the honest
denominator `16`.  The independently classified exact cardinality remains
`6`, hence is **STRICT** versus that denominator.

This is package-only: no general GA-4 or release-level conclusion is claimed.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodePackageDenomCompare

open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodePackageCount
open PHPMatchingEncodePackageFiber
open PHPMatchingEncodeAnswerAlphabetLengthTwoPackage

/-- Sum the only two possible package grades after eliminating `G3`. -/
theorem vbadMatchings_searchD4mp_two_card_le_ell_free (ell : Nat) :
    (vbadMatchings searchD4mp 2 ell).card ≤
      (honestMatchingSpace 4 4 (ell - 2)).card * 16 +
      (honestMatchingSpace 4 4 (ell - 3)).card * 64 := by
  have hsplit : (vbadMatchings searchD4mp 2 ell).card =
      (badGrade ell 2).card + (badGrade ell 3).card := by
    calc
      (vbadMatchings searchD4mp 2 ell).card =
          (Finset.univ : Finset (SearchD4mpBad ell)).card := by
        simp [SearchD4mpBad]
      _ = (badGrade ell 2 ∪ badGrade ell 3).card := by
        rw [badGrade_two_union_three]
      _ = (badGrade ell 2).card + (badGrade ell 3).card :=
        Finset.card_union_of_disjoint (badGrade_two_disjoint_three ell)
  have h2 := badGrade_searchD4mp_G1G2_card_le ell 2
  have h3 := badGrade_searchD4mp_G1G2_card_le ell 3
  norm_num at h2 h3 ⊢
  rw [hsplit]
  omega

set_option maxRecDepth 4096 in
/-- At `ell = 3`, the ell-free grade sum is `96 * 16 + 24 * 64 = 3072`. -/
theorem vbadMatchings_searchD4mp_two_three_card_le_ell_free :
    (vbadMatchings searchD4mp 2 3).card ≤ 3072 := by
  have h := vbadMatchings_searchD4mp_two_card_le_ell_free 3
  rw [honestMatchingSpace_four_four_one_card,
    honestMatchingSpace_four_four_zero_card] at h
  norm_num at h
  exact h

set_option maxRecDepth 4096 in
/-- Classification pin: the new upper bound exceeds the honest denominator. -/
theorem searchD4mp_ell_free_bound_exceeds_denominator :
    (honestMatchingSpace 4 4 3).card < 3072 := by
  rw [honestMatchingSpace_four_four_three_card]
  omega

set_option maxRecDepth 4096 in
/-- Therefore the numeric package bound is not a strict denominator bound. -/
theorem searchD4mp_ell_free_bound_not_strict :
    ¬ (3072 < (honestMatchingSpace 4 4 3).card) := by
  rw [honestMatchingSpace_four_four_three_card]
  omega

/-- S2209's exact package classification remains available for comparison. -/
theorem searchD4mp_exact_card_eq_six :
    (vbadMatchings searchD4mp 2 3).card = 6 :=
  vbadMatchings_searchD4mp_two_three_card_eq

/-- Unlike the ell-free upper bound, the exact package cardinality is strict. -/
theorem searchD4mp_exact_card_strict_denominator :
    (vbadMatchings searchD4mp 2 3).card <
      (honestMatchingSpace 4 4 3).card :=
  vbadMatchings_searchD4mp_two_three_card_lt_denominator

/-- S2215 summary: upper-bound verdict TRIVIAL, exact-card verdict STRICT. -/
theorem package_denom_compare_s2215_summary :
    (vbadMatchings searchD4mp 2 3).card ≤ 3072 ∧
      (honestMatchingSpace 4 4 3).card < 3072 ∧
      (vbadMatchings searchD4mp 2 3).card = 6 ∧
      (vbadMatchings searchD4mp 2 3).card <
        (honestMatchingSpace 4 4 3).card :=
  ⟨vbadMatchings_searchD4mp_two_three_card_le_ell_free,
    searchD4mp_ell_free_bound_exceeds_denominator,
    searchD4mp_exact_card_eq_six,
    searchD4mp_exact_card_strict_denominator⟩

end PHPMatchingEncodePackageDenomCompare
end PvNP
