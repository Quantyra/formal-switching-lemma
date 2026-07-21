import PvNP.PHPMatchingEncodePackageCount
import Mathlib.Tactic.FinCases

/-!
# S2209: exact `Fin 4` package fiber

For `searchD4mp`, `t = 3`, and `ell = 3`, the S2208 mcode bound `663552`
is TRIVIAL.  This bounded package instead has exactly six bad bases, and six
is STRICTLY smaller than the honest denominator `16`.

This is only a finite package classification.  It is not general GA-4, a PHP
switching lemma, a lower bound, or a P-versus-NP result.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodePackageFiber

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeFiberSearch
open PHPMatchingEncodeLengthTwoClass
open PHPMatchingEncodePackageInj
open PHPMatchingEncodePackageCount
open PHPMatchingEncodeDisposal
open PHPMatchingDeterministicEncode

def packageBadIndex : Fin 6 → MatchingMap 4 4
  | 0 => singleMatching 0 0
  | 1 => singleMatching 1 1
  | 2 => singleMatching 2 2
  | 3 => rhoA
  | 4 => rhoB
  | 5 => singleMatching 3 3

def exactPackageBadBases : Finset (MatchingMap 4 4) :=
  Finset.univ.image packageBadIndex

theorem packageBadIndex_injective : Function.Injective packageBadIndex := by
  have hsingle : Function.Injective
      (fun e : Fin 4 × Fin 4 => singleMatching e.1 e.2) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    by_cases hij : i = j
    · subst j
      have hab := congrFun h i
      simp [singleMatching] at hab
      exact Prod.ext rfl hab
    · have hab := congrFun h i
      simp [singleMatching, hij] at hab
  let pairIndex : Fin 6 → Fin 4 × Fin 4
    | 0 => ((0 : Fin 4), (0 : Fin 4))
    | 1 => ((1 : Fin 4), (1 : Fin 4))
    | 2 => ((2 : Fin 4), (2 : Fin 4))
    | 3 => ((2 : Fin 4), (3 : Fin 4))
    | 4 => ((3 : Fin 4), (2 : Fin 4))
    | 5 => ((3 : Fin 4), (3 : Fin 4))
  let recover : Fin 4 × Fin 4 → Fin 6 := fun e =>
    if e.1 = 0 then 0
    else if e.1 = 1 then 1
    else if e.1 = 2 then (if e.2 = 2 then 2 else 3)
    else if e.2 = 2 then 4 else 5
  have hpair : Function.Injective pairIndex := by
    apply Function.LeftInverse.injective (g := recover)
    intro i
    fin_cases i <;> simp [pairIndex, recover]
  have hrepr (k : Fin 6) :
      packageBadIndex k = singleMatching (pairIndex k).1 (pairIndex k).2 := by
    fin_cases k <;> rfl
  intro i j hij
  apply hpair
  apply hsingle
  rw [hrepr i, hrepr j] at hij
  exact hij

theorem exactPackageBadBases_card : exactPackageBadBases.card = 6 := by
  rw [exactPackageBadBases, Finset.card_image_of_injective _ packageBadIndex_injective]
  simp

private theorem packageBadIndex_mem (i : Fin 6) :
    packageBadIndex i ∈ exactPackageBadBases :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

private theorem depth_ge_three_of_three_queries
    {rho : MatchingMap 4 4} {i k : Fin 4} {b : Fin 4}
    {f : Fin 4 → VMDTree 4 4} {g : Fin 4 → VMDTree 4 4}
    {u : Fin 4 → VMDTree 4 4} (a q : Fin 4)
    (h0 : canonicalVMDT searchD4mp rho = .pquery i f)
    (h1 : f a = .hquery b g) (h2 : g q = .pquery k u) :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho) := by
  rw [h0]
  have hk : 1 ≤ vmdtDepth (.pquery k u) := by
    rw [vmdtDepth_pquery]
    omega
  have hb : 2 ≤ vmdtDepth (.hquery b g) := by
    have hchild := vmdtDepth_hquery_ge_child b g q
    rw [h2] at hchild
    omega
  have hi := vmdtDepth_pquery_ge_child i f a
  rw [h1] at hi
  omega

private def d0 : MatchingMap 4 4 := singleMatching (0 : Fin 4) 0
private def d0m1 : MatchingMap 4 4 :=
  compose d0 (singleMatching (2 : Fin 4) 1)
private def d0m2 : MatchingMap 4 4 :=
  compose d0m1 (singleMatching (1 : Fin 4) 3)

private theorem diagonal_zero_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp (singleMatching (0 : Fin 4) 0)) := by
  let f : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d0 a = true then .leaf false
    else vwalkAux 2 (compose d0 (singleMatching (2 : Fin 4) a))
      [Sum.inr (3 : Fin 4), Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] [termB]
  let g : Fin 4 → VMDTree 4 4 := fun q =>
    if (d0m1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose d0m1 (singleMatching q (3 : Fin 4)))
      [Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] [termB]
  let u : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d0m2 a = true then .leaf false
    else vwalkAux 0 (compose d0m2 (singleMatching (3 : Fin 4) a))
      [Sum.inr (2 : Fin 4)] [termB]
  apply depth_ge_three_of_three_queries (rho := d0) (a := (1 : Fin 4))
    (q := (1 : Fin 4)) (i := (2 : Fin 4)) (b := (3 : Fin 4))
    (k := (3 : Fin 4)) (f := f) (g := g) (u := u)
  · unfold canonicalVMDT
    have hfree : (freePigeons d0).card = 3 :=
      freePigeons_of_mem_allSingleEdge4 (by simp [d0, allSingleEdge4])
    rw [hfree, searchD4mp_eq]
    rw [vwalk_skip_falsified 3 d0 termA [termB] (by decide) (by decide)]
    simpa [f] using
      (vwalk_entry_pigeon (fuel' := 2) d0 termB [] (2 : Fin 4)
        [Sum.inr (3 : Fin 4), Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)]
        (by decide) (by decide) (by decide) (by decide))
  · have hused : holeUsed d0 (1 : Fin 4) = false := by decide
    simp only [f, hused, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d0m1 (Sum.inr (3 : Fin 4)) = false := by decide
    simpa [d0m1, g] using
      (vblock_query_hole 1 d0m1 (3 : Fin 4)
        [Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] [termB] hcov)
  · have hfree : (d0m1 (1 : Fin 4)).isSome = false := by decide
    simp only [g, hfree, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d0m2 (Sum.inl (3 : Fin 4)) = false := by decide
    simpa [d0m2, u] using
      (vblock_query_pigeon 0 d0m2 (3 : Fin 4)
        [Sum.inr (2 : Fin 4)] [termB] hcov)

private def d1 : MatchingMap 4 4 := singleMatching (1 : Fin 4) 1
private def d1m1 : MatchingMap 4 4 :=
  compose d1 (singleMatching (2 : Fin 4) 0)
private def d1m2 : MatchingMap 4 4 :=
  compose d1m1 (singleMatching (0 : Fin 4) 3)

private theorem diagonal_one_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp (singleMatching (1 : Fin 4) 1)) := by
  let f : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d1 a = true then .leaf false
    else vwalkAux 2 (compose d1 (singleMatching (2 : Fin 4) a))
      [Sum.inr (3 : Fin 4), Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] [termB]
  let g : Fin 4 → VMDTree 4 4 := fun q =>
    if (d1m1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose d1m1 (singleMatching q (3 : Fin 4)))
      [Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] [termB]
  let u : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d1m2 a = true then .leaf false
    else vwalkAux 0 (compose d1m2 (singleMatching (3 : Fin 4) a))
      [Sum.inr (2 : Fin 4)] [termB]
  apply depth_ge_three_of_three_queries (rho := d1) (a := (0 : Fin 4))
    (q := (0 : Fin 4)) (i := (2 : Fin 4)) (b := (3 : Fin 4))
    (k := (3 : Fin 4)) (f := f) (g := g) (u := u)
  · unfold canonicalVMDT
    have hfree : (freePigeons d1).card = 3 :=
      freePigeons_of_mem_allSingleEdge4 (by simp [d1, allSingleEdge4])
    rw [hfree, searchD4mp_eq]
    rw [vwalk_skip_falsified 3 d1 termA [termB] (by decide) (by decide)]
    simpa [f] using
      (vwalk_entry_pigeon (fuel' := 2) d1 termB [] (2 : Fin 4)
        [Sum.inr (3 : Fin 4), Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)]
        (by decide) (by decide) (by decide) (by decide))
  · have hused : holeUsed d1 (0 : Fin 4) = false := by decide
    simp only [f, hused, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d1m1 (Sum.inr (3 : Fin 4)) = false := by decide
    simpa [d1m1, g] using
      (vblock_query_hole 1 d1m1 (3 : Fin 4)
        [Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] [termB] hcov)
  · have hfree : (d1m1 (0 : Fin 4)).isSome = false := by decide
    simp only [g, hfree, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d1m2 (Sum.inl (3 : Fin 4)) = false := by decide
    simpa [d1m2, u] using
      (vblock_query_pigeon 0 d1m2 (3 : Fin 4)
        [Sum.inr (2 : Fin 4)] [termB] hcov)

private def d2 : MatchingMap 4 4 := singleMatching (2 : Fin 4) 2
private def d2m1 : MatchingMap 4 4 :=
  compose d2 (singleMatching (0 : Fin 4) 3)
private def d2m2 : MatchingMap 4 4 :=
  compose d2m1 (singleMatching (3 : Fin 4) 1)

private theorem diagonal_two_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp (singleMatching (2 : Fin 4) 2)) := by
  let f : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d2 a = true then .leaf false
    else vwalkAux 2 (compose d2 (singleMatching (0 : Fin 4) a))
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
  let g : Fin 4 → VMDTree 4 4 := fun q =>
    if (d2m1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose d2m1 (singleMatching q (1 : Fin 4)))
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
  let u : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d2m2 a = true then .leaf false
    else vwalkAux 0 (compose d2m2 (singleMatching (1 : Fin 4) a))
      [Sum.inr (0 : Fin 4)] searchD4mp
  apply depth_ge_three_of_three_queries (rho := d2) (a := (3 : Fin 4))
    (q := (3 : Fin 4)) (i := (0 : Fin 4)) (b := (1 : Fin 4))
    (k := (1 : Fin 4)) (f := f) (g := g) (u := u)
  · unfold canonicalVMDT
    have hfree : (freePigeons d2).card = 3 :=
      freePigeons_of_mem_allSingleEdge4 (by simp [d2, allSingleEdge4])
    rw [hfree, searchD4mp_eq]
    simpa [f] using
      (vwalk_entry_pigeon (fuel' := 2) d2 termA [termB] (0 : Fin 4)
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        (by decide) (by decide) (by decide) (by decide))
  · have hused : holeUsed d2 (3 : Fin 4) = false := by decide
    simp only [f, hused, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d2m1 (Sum.inr (1 : Fin 4)) = false := by decide
    simpa [d2m1, g] using
      (vblock_query_hole 1 d2m1 (1 : Fin 4)
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp hcov)
  · have hfree : (d2m1 (3 : Fin 4)).isSome = false := by decide
    simp only [g, hfree, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d2m2 (Sum.inl (1 : Fin 4)) = false := by decide
    simpa [d2m2, u] using
      (vblock_query_pigeon 0 d2m2 (1 : Fin 4)
        [Sum.inr (0 : Fin 4)] searchD4mp hcov)

private def d3 : MatchingMap 4 4 := singleMatching (3 : Fin 4) 3
private def d3m1 : MatchingMap 4 4 :=
  compose d3 (singleMatching (0 : Fin 4) 2)
private def d3m2 : MatchingMap 4 4 :=
  compose d3m1 (singleMatching (2 : Fin 4) 1)

private theorem diagonal_three_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp (singleMatching (3 : Fin 4) 3)) := by
  let f : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d3 a = true then .leaf false
    else vwalkAux 2 (compose d3 (singleMatching (0 : Fin 4) a))
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
  let g : Fin 4 → VMDTree 4 4 := fun q =>
    if (d3m1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose d3m1 (singleMatching q (1 : Fin 4)))
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
  let u : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed d3m2 a = true then .leaf false
    else vwalkAux 0 (compose d3m2 (singleMatching (1 : Fin 4) a))
      [Sum.inr (0 : Fin 4)] searchD4mp
  apply depth_ge_three_of_three_queries (rho := d3) (a := (2 : Fin 4))
    (q := (2 : Fin 4)) (i := (0 : Fin 4)) (b := (1 : Fin 4))
    (k := (1 : Fin 4)) (f := f) (g := g) (u := u)
  · unfold canonicalVMDT
    have hfree : (freePigeons d3).card = 3 :=
      freePigeons_of_mem_allSingleEdge4 (by simp [d3, allSingleEdge4])
    rw [hfree, searchD4mp_eq]
    simpa [f] using
      (vwalk_entry_pigeon (fuel' := 2) d3 termA [termB] (0 : Fin 4)
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        (by decide) (by decide) (by decide) (by decide))
  · have hused : holeUsed d3 (2 : Fin 4) = false := by decide
    simp only [f, hused, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d3m1 (Sum.inr (1 : Fin 4)) = false := by decide
    simpa [d3m1, g] using
      (vblock_query_hole 1 d3m1 (1 : Fin 4)
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp hcov)
  · have hfree : (d3m1 (2 : Fin 4)).isSome = false := by decide
    simp only [g, hfree, Bool.false_eq_true, ↓reduceIte]
    have hcov : vertexCoveredB d3m2 (Sum.inl (1 : Fin 4)) = false := by decide
    simpa [d3m2, u] using
      (vblock_query_pigeon 0 d3m2 (1 : Fin 4)
        [Sum.inr (0 : Fin 4)] searchD4mp hcov)

theorem diagonal_depth_ge_three (i : Fin 4) :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp (singleMatching i i)) := by
  fin_cases i
  · exact diagonal_zero_depth_ge_three
  · exact diagonal_one_depth_ge_three
  · exact diagonal_two_depth_ge_three
  · exact diagonal_three_depth_ge_three

theorem diagonal_mem_vbadMatchings_searchD4mp_two_three (i : Fin 4) :
    singleMatching i i ∈ vbadMatchings searchD4mp 2 3 := by
  rw [mem_vbadMatchings_succ_le]
  refine ⟨⟨isMatching_singleMatching i i, ?_⟩, diagonal_depth_ge_three i⟩
  apply freePigeons_of_mem_allSingleEdge4
  fin_cases i <;> simp [allSingleEdge4]

theorem vbadMatchings_searchD4mp_two_three_eq :
    vbadMatchings searchD4mp 2 3 = exactPackageBadBases := by
  apply Finset.Subset.antisymm
  · intro rho hrho
    have hmem := (mem_vbadMatchings_succ_le searchD4mp 2 3 rho).mp hrho
    rcases hmem with ⟨⟨hmatch, hfree⟩, hdepth⟩
    obtain ⟨i, a, rfl⟩ :=
      eq_singleMatching_of_free_count_three rho hmatch hfree
    fin_cases i <;> fin_cases a
    · simpa [packageBadIndex] using packageBadIndex_mem 0
    · exact (not_depth_ge_three_singleMatching_0_1 hdepth).elim
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · exact (not_depth_ge_three_singleMatching_1_0 hdepth).elim
    · simpa [packageBadIndex] using packageBadIndex_mem 1
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · simpa [packageBadIndex] using packageBadIndex_mem 2
    · simpa [packageBadIndex] using packageBadIndex_mem 3
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · exact (not_depth_ge_three_of_both_search_terms_falsified _ hfree
        (by decide) (by decide) hdepth).elim
    · simpa [packageBadIndex] using packageBadIndex_mem 4
    · simpa [packageBadIndex] using packageBadIndex_mem 5
  · intro rho hrho
    rw [exactPackageBadBases, Finset.mem_image] at hrho
    rcases hrho with ⟨i, _hi, rfl⟩
    fin_cases i
    · exact diagonal_mem_vbadMatchings_searchD4mp_two_three 0
    · exact diagonal_mem_vbadMatchings_searchD4mp_two_three 1
    · exact diagonal_mem_vbadMatchings_searchD4mp_two_three 2
    · exact rhoA_mem_vbadMatchings_searchD4mp_two_three
    · exact rhoB_mem_vbadMatchings_searchD4mp_two_three
    · exact diagonal_mem_vbadMatchings_searchD4mp_two_three 3

theorem vbadMatchings_searchD4mp_two_three_card_eq :
    (vbadMatchings searchD4mp 2 3).card = 6 := by
  rw [vbadMatchings_searchD4mp_two_three_eq]
  exact exactPackageBadBases_card

noncomputable def realizedPackageEncodeImage : Finset (MatchEncode 4 4 2 3 3) :=
  (Finset.univ : Finset (SearchD4mpBad 3)).image packageEncode

theorem realizedPackageEncodeImage_card_eq_six :
    realizedPackageEncodeImage.card = 6 := by
  rw [realizedPackageEncodeImage,
    Finset.card_image_of_injective _ packageEncode_injective]
  calc
    (Finset.univ : Finset (SearchD4mpBad 3)).card =
        (vbadMatchings searchD4mp 2 3).card := by
      simp [SearchD4mpBad]
    _ = 6 := vbadMatchings_searchD4mp_two_three_card_eq

theorem vbadMatchings_searchD4mp_two_three_card_lt_denominator :
    (vbadMatchings searchD4mp 2 3).card <
      (honestMatchingSpace 4 4 3).card := by
  rw [vbadMatchings_searchD4mp_two_three_card_eq,
    honestMatchingSpace_four_four_three_card]
  omega

theorem package_fiber_searchD4mp_t_three_summary :
    (vbadMatchings searchD4mp 2 3).card = 6 ∧
      realizedPackageEncodeImage.card = 6 ∧
      (honestMatchingSpace 4 4 3).card = 16 ∧
      (vbadMatchings searchD4mp 2 3).card <
        (honestMatchingSpace 4 4 3).card :=
  ⟨vbadMatchings_searchD4mp_two_three_card_eq,
    realizedPackageEncodeImage_card_eq_six,
    honestMatchingSpace_four_four_three_card,
    vbadMatchings_searchD4mp_two_three_card_lt_denominator⟩

end PHPMatchingEncodePackageFiber
end PvNP
