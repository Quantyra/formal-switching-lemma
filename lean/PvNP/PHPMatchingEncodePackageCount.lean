import PvNP.PHPMatchingEncodePackageInj
import PvNP.PHPFullMatchingDistribution

/-!
# S2208: searchD4mp / t = 3 package counting consumer

This module counts only the `Fin 4` / `searchD4mp` / `t = 3` package.
The resulting mcode upper bound is **TRIVIAL** versus the honest denominator;
no general GA-4 or release-level conclusion is claimed.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodePackageCount

open Classical
open PHPFullMatchingDistribution
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodePackageInj

abbrev SearchD4mpBad (ell : Nat) :=
  {rho : MatchingMap 4 4 // rho ∈ vbadMatchings searchD4mp (3 - 1) ell}

def packageEncode {ell : Nat} (rho : SearchD4mpBad ell) :
    MatchEncode 4 4 2 3 ell :=
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := ell) rfl
    rho.1 searchD4mp hmem.1.1 hmem.1.2 ht searchD4mp_width

theorem packageEncode_injective {ell : Nat} :
    Function.Injective (packageEncode (ell := ell)) := by
  exact encodeMatch_subtype_injective_searchD4mp_t_three

private theorem packageEncode_data {ell : Nat} (rho : SearchD4mpBad ell) :
    (∀ b ∈ (packageEncode rho).G2, Finset.Nonempty b) ∧
      codeSize (packageEncode rho).G2 = (packageEncode rho).j := by
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  simpa [packageEncode, hmem, ht] using
    encodeMatch_mem_gradedCode rho.1 searchD4mp hmem.1.1 hmem.1.2 rfl ht
      searchD4mp_width

theorem packageEncode_j_range {ell : Nat} (rho : SearchD4mpBad ell) :
    2 ≤ (packageEncode rho).j ∧ (packageEncode rho).j ≤ 3 := by
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  have hbeta := traceBetaDeep_wellFormed_codeSize
    (w := 2) rho.1 searchD4mp hmem.1.1 ht searchD4mp_width
  have hsteps := leftmostLiveDeepFeed_vtrace_eventsSteps_length
    (t := 3) rfl rho.1 searchD4mp hmem.1.1 ht
  have hdrop := vtrace_drop_range (freePigeons rho.1).card rho.1 searchD4mp
    (leftmostLiveDeepFeed rho.1 searchD4mp 3)
  have hdropv :
      ((blockSigmas (blocksOf
        (vtrace rho.1 searchD4mp
          (leftmostLiveDeepFeed rho.1 searchD4mp 3)))).join).length ≤
          (eventsSteps (vtrace rho.1 searchD4mp
            (leftmostLiveDeepFeed rho.1 searchD4mp 3))).length ∧
        (eventsSteps (vtrace rho.1 searchD4mp
          (leftmostLiveDeepFeed rho.1 searchD4mp 3))).length ≤
          2 * ((blockSigmas (blocksOf
            (vtrace rho.1 searchD4mp
              (leftmostLiveDeepFeed rho.1 searchD4mp 3)))).join).length := by
    simpa [vtrace] using hdrop
  have hdrop' :
      ((blockSigmas (blocksOf
        (vtrace rho.1 searchD4mp
          (leftmostLiveDeepFeed rho.1 searchD4mp 3)))).join).length ≤ 3 ∧
        3 ≤ 2 * ((blockSigmas (blocksOf
          (vtrace rho.1 searchD4mp
            (leftmostLiveDeepFeed rho.1 searchD4mp 3)))).join).length := by
    rw [hsteps] at hdropv
    exact hdropv
  have hj : (packageEncode rho).j =
      ((blockSigmas (blocksOf
        (vtrace rho.1 searchD4mp
          (leftmostLiveDeepFeed rho.1 searchD4mp 3)))).join).length := by
    simpa [packageEncode, hmem, ht, encodeMatch] using hbeta.2
  omega

theorem packageEncode_j_eq_two_or_three {ell : Nat} (rho : SearchD4mpBad ell) :
    (packageEncode rho).j = 2 ∨ (packageEncode rho).j = 3 := by
  have h := packageEncode_j_range rho
  omega

def badGrade (ell j : Nat) : Finset (SearchD4mpBad ell) :=
  Finset.univ.filter (fun rho => (packageEncode rho).j = j)

theorem badGrade_two_union_three (ell : Nat) :
    (Finset.univ : Finset (SearchD4mpBad ell)) =
      badGrade ell 2 ∪ badGrade ell 3 := by
  apply Finset.Subset.antisymm
  · intro rho _
    rcases packageEncode_j_eq_two_or_three rho with hj | hj
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  · exact Finset.subset_univ _

theorem badGrade_two_disjoint_three (ell : Nat) :
    Disjoint (badGrade ell 2) (badGrade ell 3) := by
  apply Finset.disjoint_left.mpr
  intro rho htwo hthree
  have h2 : (packageEncode rho).j = 2 := (Finset.mem_filter.mp htwo).2
  have h3 : (packageEncode rho).j = 3 := (Finset.mem_filter.mp hthree).2
  omega

def gradePayloads (ell j : Nat) :
    Finset (List (Finset (Fin 2)) × (Fin 3 → Fin (2 * ell))) :=
  (badGrade ell j).image
    (fun rho => ((packageEncode rho).G2, (packageEncode rho).G3))

theorem gradePayloads_card_le (ell j : Nat) :
    (gradePayloads ell j).card ≤ (2 * 2) ^ j * (2 * ell) ^ 3 := by
  apply mcode_answers_family_card_le
  · intro cs hcs b hb
    rw [gradePayloads, Finset.mem_image] at hcs
    rcases hcs with ⟨rho, _hrho, rfl⟩
    exact (packageEncode_data rho).1 b hb
  · intro cs hcs
    rw [gradePayloads, Finset.mem_image] at hcs
    rcases hcs with ⟨rho, hrho, rfl⟩
    have hj : (packageEncode rho).j = j := (Finset.mem_filter.mp hrho).2
    rw [(packageEncode_data rho).2, hj]

theorem packageEncode_G1_mem_honest {ell j : Nat}
    {rho : SearchD4mpBad ell} (hrho : rho ∈ badGrade ell j) :
    (packageEncode rho).G1 ∈ honestMatchingSpace 4 4 (ell - j) := by
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  rw [mem_honestMatchingSpace]
  constructor
  · simpa [packageEncode, hmem, ht, encodeMatch] using
      encodeExt_isMatching rho.1 searchD4mp
        (leftmostLiveDeepFeed rho.1 searchD4mp 3) hmem.1.1
  · have hfree := encodeMatch_freePigeons_card (w := 2) (t := 3) rfl rho.1
      searchD4mp hmem.1.1 hmem.1.2 ht searchD4mp_width
    have hj : (packageEncode rho).j = j := (Finset.mem_filter.mp hrho).2
    have hfree' : (freePigeons (packageEncode rho).G1).card =
        ell - (packageEncode rho).j := by
      simpa [packageEncode] using hfree
    rw [hj] at hfree'
    exact hfree'

theorem badGrade_card_le (ell j : Nat) :
    (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card *
        ((2 * 2) ^ j * (2 * ell) ^ 3) := by
  let target := (honestMatchingSpace 4 4 (ell - j)).product (gradePayloads ell j)
  let f : SearchD4mpBad ell →
      MatchingMap 4 4 × (List (Finset (Fin 2)) × (Fin 3 → Fin (2 * ell))) :=
    fun rho => ((packageEncode rho).G1,
      ((packageEncode rho).G2, (packageEncode rho).G3))
  have hmap : ∀ rho ∈ badGrade ell j, f rho ∈ target := by
    intro rho hrho
    apply Finset.mem_product.mpr
    exact ⟨packageEncode_G1_mem_honest hrho,
      Finset.mem_image.mpr ⟨rho, hrho, rfl⟩⟩
  have hinj : Set.InjOn f (↑(badGrade ell j) : Set (SearchD4mpBad ell)) := by
    intro rho hrho rho' hrho' heq
    apply packageEncode_injective
    have hj : (packageEncode rho).j = j := (Finset.mem_filter.mp hrho).2
    have hj' : (packageEncode rho').j = j := (Finset.mem_filter.mp hrho').2
    dsimp only [f] at heq
    cases hcode : packageEncode rho with
    | mk G1 G2 G3 k =>
      cases hcode' : packageEncode rho' with
      | mk G1' G2' G3' k' =>
        simp only [hcode, hcode'] at heq hj hj' ⊢
        simp_all
  calc
    (badGrade ell j).card ≤ target.card :=
      Finset.card_le_card_of_injOn f hmap hinj
    _ = (honestMatchingSpace 4 4 (ell - j)).card *
        (gradePayloads ell j).card := Finset.card_product _ _
    _ ≤ (honestMatchingSpace 4 4 (ell - j)).card *
        ((2 * 2) ^ j * (2 * ell) ^ 3) :=
      Nat.mul_le_mul_left _ (gradePayloads_card_le ell j)

theorem vbadMatchings_searchD4mp_two_card_le (ell : Nat) :
    (vbadMatchings searchD4mp 2 ell).card ≤
      (honestMatchingSpace 4 4 (ell - 2)).card * (16 * (2 * ell) ^ 3) +
      (honestMatchingSpace 4 4 (ell - 3)).card * (64 * (2 * ell) ^ 3) := by
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
  have h2 := badGrade_card_le ell 2
  have h3 := badGrade_card_le ell 3
  norm_num at h2 h3 ⊢
  rw [hsplit]
  omega

set_option maxRecDepth 4096 in
theorem honestMatchingSpace_four_four_zero_card :
    (honestMatchingSpace 4 4 0).card = 24 := by
  have h := card_fullMatchingSpace_eq_factorial_mul (h := 4) (ell := 0) (by omega)
  rw [card_fullMatchingSpace, Fintype.card_perm] at h
  norm_num [Nat.factorial] at h ⊢
  exact h

set_option maxRecDepth 4096 in
theorem honestMatchingSpace_four_four_one_card :
    (honestMatchingSpace 4 4 1).card = 96 := by
  have h := card_fullMatchingSpace_eq_factorial_mul (h := 4) (ell := 1) (by omega)
  rw [card_fullMatchingSpace, Fintype.card_perm] at h
  norm_num [Nat.factorial] at h ⊢
  exact h

set_option maxRecDepth 4096 in
theorem honestMatchingSpace_four_four_three_card :
    (honestMatchingSpace 4 4 3).card = 16 := by
  have h := card_fullMatchingSpace_eq_factorial_mul (h := 4) (ell := 3) (by omega)
  rw [card_fullMatchingSpace, Fintype.card_perm] at h
  norm_num [Nat.factorial] at h ⊢
  omega

set_option maxRecDepth 4096 in
theorem vbadMatchings_searchD4mp_two_three_card_le :
    (vbadMatchings searchD4mp 2 3).card ≤ 663552 := by
  have h := vbadMatchings_searchD4mp_two_card_le 3
  rw [honestMatchingSpace_four_four_one_card,
    honestMatchingSpace_four_four_zero_card] at h
  norm_num at h
  exact h

theorem rhoA_mem_vbadMatchings_searchD4mp_two_three :
    rhoA ∈ vbadMatchings searchD4mp 2 3 := by
  rw [PHPMatchingEncodeDisposal.mem_vbadMatchings_succ_le]
  exact ⟨⟨isMatching_rhoA, freePigeons_rhoA⟩, rhoA_depth_ge_three⟩

theorem rhoB_mem_vbadMatchings_searchD4mp_two_three :
    rhoB ∈ vbadMatchings searchD4mp 2 3 := by
  rw [PHPMatchingEncodeDisposal.mem_vbadMatchings_succ_le]
  exact ⟨⟨isMatching_rhoB, freePigeons_rhoB⟩, rhoB_depth_ge_three⟩

theorem vbadMatchings_searchD4mp_two_three_card_ge_two :
    2 ≤ (vbadMatchings searchD4mp 2 3).card := by
  let pair : Finset (MatchingMap 4 4) := {rhoA, rhoB}
  have hpair : pair ⊆ vbadMatchings searchD4mp 2 3 := by
    intro rho hrho
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hrho
    rcases hrho with rfl | rfl
    · exact rhoA_mem_vbadMatchings_searchD4mp_two_three
    · exact rhoB_mem_vbadMatchings_searchD4mp_two_three
  have hc := Finset.card_le_card hpair
  have hp : pair.card = 2 := by simp [pair, rhoA_ne_rhoB]
  omega

theorem searchD4mp_package_code_bound_exceeds_denominator :
    (honestMatchingSpace 4 4 3).card < 663552 := by
  rw [honestMatchingSpace_four_four_three_card]
  omega

theorem searchD4mp_package_code_bound_not_strict :
    ¬ (663552 < (honestMatchingSpace 4 4 3).card) := by
  rw [honestMatchingSpace_four_four_three_card]
  omega

theorem vbadMatchings_searchD4mp_two_three_card_le_denominator :
    (vbadMatchings searchD4mp 2 3).card ≤
      (honestMatchingSpace 4 4 3).card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Summary: package counting consumer; mcode bound is TRIVIAL vs honest denom. -/
theorem package_count_searchD4mp_t_three_summary :
    2 ≤ (vbadMatchings searchD4mp 2 3).card ∧
      (vbadMatchings searchD4mp 2 3).card ≤ 663552 ∧
      (honestMatchingSpace 4 4 3).card < 663552 ∧
      (vbadMatchings searchD4mp 2 3).card ≤
        (honestMatchingSpace 4 4 3).card :=
  ⟨vbadMatchings_searchD4mp_two_three_card_ge_two,
    vbadMatchings_searchD4mp_two_three_card_le,
    searchD4mp_package_code_bound_exceeds_denominator,
    vbadMatchings_searchD4mp_two_three_card_le_denominator⟩

end PHPMatchingEncodePackageCount
end PvNP
