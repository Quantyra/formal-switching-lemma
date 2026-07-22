import PvNP.PHPMatchingEncodeSideBitImage
import PvNP.PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
import PvNP.PHPMatchingEncodePackageCount

/-!
# S2218: fixed package side-bit source bound

The existing `searchD4mp` `G1`/`G2` package injectivity makes the general
side-bit image estimate a source estimate on each package grade.  This is a
fixed-package consumer, not a new general residual, GA-4, switching, or
release result; the `Fin 4` `6/16` result remains regression-only.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeSideBitPackage

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeAnswerAlphabetLengthTwo
open PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
open PHPMatchingEncodePackageInj
open PHPMatchingEncodePackageCount
open PHPMatchingEncodeSideBitImage

/-- The package grade is exactly the general side-bit grade specialized to
`searchD4mp`. -/
theorem badGrade_eq_sideBitBadGrade (ell j : Nat) :
    (show Finset (BadEncodeDomain 4 3 ell
        PHPMatchingEncodeMultiPreimage.searchD4mp) from
      PHPMatchingEncodePackageCount.badGrade ell j) =
      sideBitBadGrade (h := 4) (w := 2) 3 ell
        PHPMatchingEncodeMultiPreimage.searchD4mp
        PHPMatchingEncodeMultiPreimage.searchD4mp_width j := by
  ext rho
  simp only [badGrade, sideBitBadGrade, Finset.mem_filter, Finset.mem_univ,
    true_and]
  let hmem := (mem_vbadMatchings PHPMatchingEncodeMultiPreimage.searchD4mp
    (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth
      (canonicalVMDT PHPMatchingEncodeMultiPreimage.searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  have hcode : PHPMatchingEncodePackageCount.packageEncode rho =
      badEncode PHPMatchingEncodeMultiPreimage.searchD4mp_width rho := by
    simp [packageEncode, badEncode, hmem, ht]
  rw [hcode]

/-- Existing package `G1`/`G2` injectivity implies side-bit injectivity on
every fixed package grade; the side bits themselves are not used here. -/
theorem sideBitEncode_injOn_searchD4mp_badGrade (ell j : Nat) :
    Set.InjOn (sideBitEncode (h := 4) (w := 2) (t := 3) (ell := ell)
        (D := PHPMatchingEncodeMultiPreimage.searchD4mp)
        PHPMatchingEncodeMultiPreimage.searchD4mp_width)
      (↑(sideBitBadGrade (h := 4) (w := 2) 3 ell
          PHPMatchingEncodeMultiPreimage.searchD4mp
          PHPMatchingEncodeMultiPreimage.searchD4mp_width j) :
        Set (BadEncodeDomain 4 3 ell
          PHPMatchingEncodeMultiPreimage.searchD4mp)) := by
  have hinjG := badEncode_G1G2_injOn_atMostTwoBlockGrade
    (t := 3) (ell := ell) PHPMatchingEncodeMultiPreimage.searchD4mp
      PHPMatchingEncodeMultiPreimage.searchD4mp_width j
      encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three
  intro rho hrho rho' hrho' heq
  apply hinjG
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hrho).2⟩
    let hmem := (mem_vbadMatchings PHPMatchingEncodeMultiPreimage.searchD4mp
      (3 - 1) ell rho.1).mp rho.2
    let ht : 3 ≤ vmdtDepth
        (canonicalVMDT PHPMatchingEncodeMultiPreimage.searchD4mp rho.1) :=
      Nat.le_of_pred_lt hmem.2
    exact enteredTermsOf_length_le_two_searchD4mp_t_three
      rho.1 hmem.1.1 hmem.1.2 ht
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hrho').2⟩
    let hmem := (mem_vbadMatchings PHPMatchingEncodeMultiPreimage.searchD4mp
      (3 - 1) ell rho'.1).mp rho'.2
    let ht : 3 ≤ vmdtDepth
        (canonicalVMDT PHPMatchingEncodeMultiPreimage.searchD4mp rho'.1) :=
      Nat.le_of_pred_lt hmem.2
    exact enteredTermsOf_length_le_two_searchD4mp_t_three
      rho'.1 hmem.1.1 hmem.1.2 ht
  · exact congrArg (fun p => (p.1, p.2.1)) heq

/-- Side-bit package grade bound.  The `4^j` factor comes from the new
ell-independent side stream. -/
theorem badGrade_searchD4mp_sidebit_card_le (ell j : Nat) :
    (PHPMatchingEncodePackageCount.badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j := by
  calc
    (PHPMatchingEncodePackageCount.badGrade ell j).card =
        (sideBitBadGrade (h := 4) (w := 2) 3 ell
          PHPMatchingEncodeMultiPreimage.searchD4mp
          PHPMatchingEncodeMultiPreimage.searchD4mp_width j).card :=
      congrArg Finset.card (badGrade_eq_sideBitBadGrade ell j)
    _ ≤ (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j :=
      sideBitBadGrade_card_le_of_injOn
        PHPMatchingEncodeMultiPreimage.searchD4mp
        PHPMatchingEncodeMultiPreimage.searchD4mp_width
        (sideBitEncode_injOn_searchD4mp_badGrade ell j)

/-- S2218 package summary: grade identification, inherited injectivity, and
the resulting fixed-package source bound. -/
theorem sidebit_package_s2218_summary :
    (∀ ell j : Nat,
      (show Finset (BadEncodeDomain 4 3 ell
          PHPMatchingEncodeMultiPreimage.searchD4mp) from
        PHPMatchingEncodePackageCount.badGrade ell j) =
        sideBitBadGrade (h := 4) (w := 2) 3 ell
          PHPMatchingEncodeMultiPreimage.searchD4mp
          PHPMatchingEncodeMultiPreimage.searchD4mp_width j) ∧
    (∀ ell j : Nat,
      Set.InjOn (sideBitEncode (h := 4) (w := 2) (t := 3) (ell := ell)
          (D := PHPMatchingEncodeMultiPreimage.searchD4mp)
          PHPMatchingEncodeMultiPreimage.searchD4mp_width)
        (↑(sideBitBadGrade (h := 4) (w := 2) 3 ell
            PHPMatchingEncodeMultiPreimage.searchD4mp
            PHPMatchingEncodeMultiPreimage.searchD4mp_width j) :
          Set (BadEncodeDomain 4 3 ell
            PHPMatchingEncodeMultiPreimage.searchD4mp))) ∧
    (∀ ell j : Nat,
      (PHPMatchingEncodePackageCount.badGrade ell j).card ≤
        (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j) :=
  ⟨badGrade_eq_sideBitBadGrade,
    sideBitEncode_injOn_searchD4mp_badGrade,
    badGrade_searchD4mp_sidebit_card_le⟩

end PHPMatchingEncodeSideBitPackage
end PvNP
