import PvNP.PHPMatchingEncodeAnswerAlphabetLengthTwo
import PvNP.PHPMatchingEncodePackageInj
import PvNP.PHPMatchingEncodePackageCount

/-!
# S2214: Fin4 package discharge of the G1/G2 length-two residual

This file discharges the S2213 path-exit residual only for `searchD4mp` at
`t = 3`.  It does not establish a general residual or general GA-4 bound; the
package asymptotic stop-loss remains in force.
-/

namespace PvNP
namespace PHPMatchingEncodeAnswerAlphabetLengthTwoPackage

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeFiberSearch
open PHPMatchingEncodeLengthTwoClass
open PHPMatchingEncodePackageInj
open PHPMatchingEncodePackageCount
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeAnswerAlphabetLengthTwo

/-- At free-count three, equality of `G2` excludes the only cross-case in the
length-two classification. -/
theorem encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three_ell_three :
    EncodeMatchG1G2LengthTwoPathExitEqResidual (p := 4) (h := 4) (w := 2)
      (t := 3) (ell := 3) rfl searchD4mp searchD4mp_width := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ _hG1 hG2 hlen
  have h1 := length_two_free_count_three_eq_rhoA_or_rhoB rho₁ hrho₁ hell₁ ht₁
    hlen
  have hlen₂ : (enteredTermsOf rho₂ searchD4mp 3).length = 2 := by
    calc
      (enteredTermsOf rho₂ searchD4mp 3).length =
          (encodeMatch rfl rho₂ searchD4mp hrho₂ hell₂ ht₂
            searchD4mp_width).G2.length :=
        enteredTermsOf_length_eq_G2 rfl rho₂ searchD4mp hrho₂ hell₂ ht₂
          searchD4mp_width
      _ = (encodeMatch rfl rho₁ searchD4mp hrho₁ hell₁ ht₁
            searchD4mp_width).G2.length := by rw [hG2]
      _ = (enteredTermsOf rho₁ searchD4mp 3).length :=
        (enteredTermsOf_length_eq_G2 rfl rho₁ searchD4mp hrho₁ hell₁ ht₁
          searchD4mp_width).symm
      _ = 2 := hlen
  have h2 := length_two_free_count_three_eq_rhoA_or_rhoB rho₂ hrho₂ hell₂ ht₂
    hlen₂
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · simp [h1, h2]
  · subst h1; subst h2
    exact absurd hG2 (encodeMatch_G2_rhoA_ne_rhoB ht₁ ht₂)
  · subst h1; subst h2
    exact absurd hG2 (Ne.symm (encodeMatch_G2_rhoA_ne_rhoB ht₂ ht₁))
  · simp [h1, h2]

/-- The G1/G2 path-exit residual for every free-count in the fixed Fin4
package.  Depth eligibility leaves only free-counts three and four; the latter
has the unique empty base. -/
theorem encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three
    {ell : Nat} :
    EncodeMatchG1G2LengthTwoPathExitEqResidual (p := 4) (h := 4) (w := 2)
      (t := 3) (ell := ell) rfl searchD4mp searchD4mp_width := by
  by_cases h : ell = 3
  · subst h
    exact encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three_ell_three
  · intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ _ht₂ _hG1 _hG2 _hlen
    have hcard : ell ≤ 4 := by
      have hle : (freePigeons rho₁).card ≤ Fintype.card (Fin 4) :=
        Finset.card_le_univ _
      simpa [hell₁, Fintype.card_fin] using hle
    have hdepth := vmdtDepth_canonicalVMDT_le_freePigeons searchD4mp rho₁
    have hell : ell = 4 := by omega
    have h1 := unique_ell_four rho₁ hrho₁ (by rw [hell₁, hell])
    have h2 := unique_ell_four rho₂ hrho₂ (by rw [hell₂, hell])
    simp [h1, h2]

/-- Honest-times-mcode grade bound for the fixed package's at-most-two-block
domain. -/
theorem atMostTwoBlockGradeDomain_searchD4mp_t_three_card_le (ell j : Nat) :
    (atMostTwoBlockGradeDomain (t := 3) (ell := ell) searchD4mp
      searchD4mp_width j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j :=
  atMostTwoBlockGradeDomain_card_le searchD4mp searchD4mp_width j
    encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three

/-- The package `badGrade` is wholly contained in the at-most-two-block slice,
so the S2214 bound removes the old `G3` alphabet factor on this fixed grade. -/
theorem badGrade_searchD4mp_G1G2_card_le (ell j : Nat) :
    (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j := by
  have heq : badGrade ell j =
      atMostTwoBlockGradeDomain (t := 3) (ell := ell) searchD4mp
        searchD4mp_width j := by
    ext rho
    simp only [badGrade, atMostTwoBlockGradeDomain, Finset.mem_filter,
      Finset.mem_univ, true_and]
    let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
    let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
      Nat.le_of_pred_lt hmem.2
    have hlen := enteredTermsOf_length_le_two_searchD4mp_t_three
      (ell := ell) rho.1 hmem.1.1 hmem.1.2 ht
    have hcode : packageEncode rho = badEncode searchD4mp_width rho := by
      simp [packageEncode, badEncode, hmem, ht]
    rw [← hcode]
    exact iff_and_self.mpr (fun _ => hlen)
  rw [heq]
  exact atMostTwoBlockGradeDomain_searchD4mp_t_three_card_le ell j

/-- S2214 package summary: the fixed residual is discharged and consumed by
the at-most-two-block grade bound. -/
theorem path_exit_residual_s2214_summary :
    (∀ ell : Nat,
      EncodeMatchG1G2LengthTwoPathExitEqResidual (p := 4) (h := 4) (w := 2)
        (t := 3) (ell := ell) rfl searchD4mp searchD4mp_width) ∧
      (∀ ell j : Nat,
        (atMostTwoBlockGradeDomain (t := 3) (ell := ell) searchD4mp
          searchD4mp_width j).card ≤
          (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) ∧
      (∀ ell j : Nat,
        (badGrade ell j).card ≤
          (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) :=
  ⟨fun _ell =>
      encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three,
    atMostTwoBlockGradeDomain_searchD4mp_t_three_card_le,
    badGrade_searchD4mp_G1G2_card_le⟩

end PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
end PvNP
