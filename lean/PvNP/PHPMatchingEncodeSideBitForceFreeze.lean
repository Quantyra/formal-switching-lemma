import PvNP.PHPMatchingEncodeSideBitPackage
import PvNP.PHPMatchingEncodePackageOracleFreeze

/-!
# S2220 STOP-LOSS: side-bit counting for force

S2218 supplies infrastructure only: its extra side-bit factor cannot improve
the S2214 fixed-package bound.  A pivot is required, while walked-pair recovery
remains open as the residual-class freeze.

No GA-4, switching, P-vs-NP, or v0.11.0 conclusion is claimed.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodeSideBitForceFreeze

open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodePackageCount
open PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
open PHPMatchingEncodeSideBitPackage
open PHPMatchingEncodePackageDenomCompare

/-- S2220 stop-loss summary: the side-bit route only enlarges the S2214 bound,
while the fixed oracle remains `3072` TRIVIAL and exact-cardinality `6` STRICT. -/
theorem sidebit_force_freeze_s2220_summary :
    (∀ ell j, (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) ∧
    (∀ ell j, (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j) ∧
    (∀ ell j, (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j) ∧
    (vbadMatchings searchD4mp 2 3).card ≤ 3072 ∧
    (honestMatchingSpace 4 4 3).card < 3072 ∧
    (vbadMatchings searchD4mp 2 3).card = 6 ∧
    6 < (honestMatchingSpace 4 4 3).card := by
  refine ⟨badGrade_searchD4mp_G1G2_card_le,
    badGrade_searchD4mp_sidebit_card_le, ?_,
    vbadMatchings_searchD4mp_two_three_card_le_ell_free,
    searchD4mp_ell_free_bound_exceeds_denominator,
    searchD4mp_exact_card_eq_six, ?_⟩
  · intro ell j
    have hpow : 1 ≤ 4 ^ j :=
      Nat.one_le_pow _ _ (by decide : 0 < 4)
    simpa using Nat.mul_le_mul_left
      ((honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) hpow
  · simpa [searchD4mp_exact_card_eq_six] using
      searchD4mp_exact_card_strict_denominator

end PHPMatchingEncodeSideBitForceFreeze
end PvNP
