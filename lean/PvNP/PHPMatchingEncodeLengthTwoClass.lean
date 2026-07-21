import PvNP.PHPMatchingEncodeFiberSearch

import Mathlib.Tactic.FinCases



/-!

# S2206: length-2 free-count-3 base classification on searchD4mp



Board `Fin 4`, dual width-2 DNF `searchD4mp`, depth `t = 3`, free-count

`ell = 3`.



* Depth barriers: both-terms-falsified bases (8 single edges); dual edges

  `(0,1)` and `(1,0)` have canonical depth ≤ 2.

* Diagonal single edges `(0,0),(1,1),(2,2),(3,3)` never realize entered-term

  length 2 under depth ≥ 3 (only one non-falsified search term at the base).

* Every free-count-3 length-2 depth-eligible base equals `rhoA` or `rhoB`.

* `EncodeMatchLengthTwoExitEqResidual` discharged at `ell = 3` (and packaged

  for all free-counts with the S2205 `ell ≠ 3` barriers).



INTEGRITY: no sorry, no admit, no new axiom, no native_decide. No v0.11.0.

-/



namespace PvNP

namespace PHPMatchingEncodeLengthTwoClass



open PHPMatchingComposition

open PHPMatchingCanonicalMDT

open PHPMatchingVertexTree

open PHPMatchingExtensionEncode

open PHPMatchingDeterministicEncode

open PHPMatchingEncodeInjectivity

open PHPMatchingEncodeMultiPreimage

open PHPMatchingEncodeFiberSearch

open PHPMatchingEncodeCollisionSearch

open RestrictedPHPFloor



private theorem termA_leg : termMatchingLegalB termA = true := by decide

private theorem termB_leg : termMatchingLegalB termB = true := by decide



private theorem finList4 : finList 4 = [(0 : Fin 4), 1, 2, 3] := by

  unfold finList

  simp [List.range_succ, List.range_zero]



private theorem free3 (i a : Fin 4) :

    (freePigeons (singleMatching i a)).card = 3 :=

  freePigeons_of_mem_allSingleEdge4 (by

    fin_cases i <;> fin_cases a <;> simp [allSingleEdge4])



private theorem depth0_both_fals

    (rho : MatchingMap 4 4) (hell : (freePigeons rho).card = 3)

    (hA : termFalsifiedB rho termA = true)

    (hB : termFalsifiedB rho termB = true) :

    vmdtDepth (canonicalVMDT searchD4mp rho) = 0 := by

  unfold canonicalVMDT

  rw [hell, searchD4mp_eq]

  rw [vwalk_skip_falsified 3 rho termA [termB] termA_leg hA]

  rw [vwalk_skip_falsified 3 rho termB [] termB_leg hB]

  rw [vwalk_nil, vmdtDepth_leaf]



private theorem not_ge3_both_fals

    (rho : MatchingMap 4 4) (hell : (freePigeons rho).card = 3)

    (hA : termFalsifiedB rho termA = true)

    (hB : termFalsifiedB rho termB = true) :

    Not (3 <= vmdtDepth (canonicalVMDT searchD4mp rho)) := by

  have h := depth0_both_fals rho hell hA hB; omega



/-! ## Depth ≤ 2 for singleMatching (0,1) -/



private def r01 : MatchingMap 4 4 := singleMatching (0 : Fin 4) 1



private theorem hu01_0 : holeUsed r01 (0 : Fin 4) = false := by

  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

  rintro ⟨i, hi⟩; fin_cases i <;> simp [r01, singleMatching] at hi

private theorem hu01_1 : holeUsed r01 (1 : Fin 4) = true := by

  rw [holeUsed_eq_true_iff]; exact ⟨0, by simp [r01, singleMatching]⟩

private theorem hu01_2 : holeUsed r01 (2 : Fin 4) = false := by

  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

  rintro ⟨i, hi⟩; fin_cases i <;> simp [r01, singleMatching] at hi

private theorem hu01_3 : holeUsed r01 (3 : Fin 4) = false := by

  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

  rintro ⟨i, hi⟩; fin_cases i <;> simp [r01, singleMatching] at hi



private theorem tv01 :

    termVertices r01 termA =

      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] := by

  unfold termVertices termA pairUnresolvedB r01 singleMatching

  simp [holeUsed, finList4]



private def m01 (a : Fin 4) : MatchingMap 4 4 :=

  compose r01 (singleMatching (1 : Fin 4) a)



private theorem m01_app (a : Fin 4) :

    m01 a = fun i =>

      if i = (0 : Fin 4) then some (1 : Fin 4)

      else if i = (1 : Fin 4) then some a else none := by

  funext i

  simp [m01, r01, compose, singleMatching]

  split_ifs <;> simp_all



private theorem depth_m01_0 :

    vmdtDepth (vwalkAux 2 (m01 0) [Sum.inr (0 : Fin 4)] [termA, termB]) = 0 := by

  have hcov : vertexCoveredB (m01 0) (Sum.inr (0 : Fin 4)) = true := by

    simp [vertexCoveredB, holeUsed, finList4, m01_app]

  rw [vblock_skip_covered 2 (m01 0) (Sum.inr (0 : Fin 4)) [] [termA, termB] hcov]

  have hsat : termSatisfiedB (m01 0) termA = true := by

    simp [termSatisfiedB, termA, pairSatB, m01_app]

  have hfals : termFalsifiedB (m01 0) termA = false := by

    simp [termFalsifiedB, termA, pairFalsB, m01_app, holeUsed, finList4]

  rw [vwalk_stop_satisfied 2 (m01 0) termA [termB] termA_leg hfals hsat,

    vmdtDepth_leaf]



private theorem depth_m01_2_child (q : Fin 4) :

    vmdtDepth

      (if ((m01 2) q).isSome = true then (.leaf false : VMDTree 4 4)

       else vwalkAux 1 (compose (m01 2) (singleMatching q (0 : Fin 4)))

         [] [termA, termB]) = 0 := by

  by_cases hq : ((m01 2) q).isSome = true

  · simp [hq, vmdtDepth_leaf]

  · simp only [hq, Bool.false_eq_true, ↓reduceIte]

    let mu' := compose (m01 2) (singleMatching q (0 : Fin 4))

    have hAf : termFalsifiedB mu' termA = true := by

      unfold termFalsifiedB termA pairFalsB

      have h1 : mu' (1 : Fin 4) = some (2 : Fin 4) := by

        simp [mu', compose, singleMatching, m01_app]

      simp [h1]

    rw [vwalk_skip_falsified 1 mu' termA [termB] termA_leg hAf]

    have hBf : termFalsifiedB mu' termB = true := by

      have hqfree : q = 2 ∨ q = 3 := by

        fin_cases q <;> simp [m01_app] at hq ⊢

      unfold termFalsifiedB termB pairFalsB

      have h2u : holeUsed mu' (2 : Fin 4) = true := by

        rw [holeUsed_eq_true_iff]

        exact ⟨1, by simp [mu', compose, singleMatching, m01_app]⟩

      rcases hqfree with rfl | rfl

      · have h2 : mu' (2 : Fin 4) = some (0 : Fin 4) := by

          simp [mu', compose, singleMatching, m01_app]

        simp [h2]

      · have h3 : mu' (3 : Fin 4) = some (0 : Fin 4) := by

          simp [mu', compose, singleMatching, m01_app]

        simp [h3]

    rw [vwalk_skip_falsified 1 mu' termB [] termB_leg hBf, vwalk_nil,

      vmdtDepth_leaf]



private theorem depth_m01_2 :

    vmdtDepth (vwalkAux 2 (m01 2) [Sum.inr (0 : Fin 4)] [termA, termB]) = 1 := by

  have h0 : holeUsed (m01 2) (0 : Fin 4) = false := by

    rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

    rintro ⟨i, hi⟩; fin_cases i <;> simp [m01_app] at hi

  have hcov : vertexCoveredB (m01 2) (Sum.inr (0 : Fin 4)) = false := by

    simp [vertexCoveredB, h0]

  rw [vblock_query_hole (fuel' := 1) (m01 2) (0 : Fin 4) [] [termA, termB]

    hcov, vmdtDepth_hquery]

  have hsup :

      (Finset.univ.sup fun q =>

        vmdtDepth

          (if ((m01 2) q).isSome = true then (.leaf false : VMDTree 4 4)

           else vwalkAux 1 (compose (m01 2) (singleMatching q (0 : Fin 4)))

             [] [termA, termB])) = 0 := by

    apply le_antisymm

    · exact Finset.sup_le (fun q _ => (depth_m01_2_child q).le)

    · exact Nat.zero_le _

  omega



private theorem depth_m01_3_child (q : Fin 4) :

    vmdtDepth

      (if ((m01 3) q).isSome = true then (.leaf false : VMDTree 4 4)

       else vwalkAux 1 (compose (m01 3) (singleMatching q (0 : Fin 4)))

         [] [termA, termB]) = 0 := by

  by_cases hq : ((m01 3) q).isSome = true

  · simp [hq, vmdtDepth_leaf]

  · simp only [hq, Bool.false_eq_true, ↓reduceIte]

    let mu' := compose (m01 3) (singleMatching q (0 : Fin 4))

    have hAf : termFalsifiedB mu' termA = true := by

      unfold termFalsifiedB termA pairFalsB

      have h1 : mu' (1 : Fin 4) = some (3 : Fin 4) := by

        simp [mu', compose, singleMatching, m01_app]

      simp [h1]

    rw [vwalk_skip_falsified 1 mu' termA [termB] termA_leg hAf]

    have hBf : termFalsifiedB mu' termB = true := by

      have hqfree : q = 2 ∨ q = 3 := by

        fin_cases q <;> simp [m01_app] at hq ⊢

      unfold termFalsifiedB termB pairFalsB

      rcases hqfree with rfl | rfl

      · have h2 : mu' (2 : Fin 4) = some (0 : Fin 4) := by

          simp [mu', compose, singleMatching, m01_app]

        simp [h2]

      · have h3 : mu' (3 : Fin 4) = some (0 : Fin 4) := by

          simp [mu', compose, singleMatching, m01_app]

        simp [h3]

    rw [vwalk_skip_falsified 1 mu' termB [] termB_leg hBf, vwalk_nil,

      vmdtDepth_leaf]



private theorem depth_m01_3 :

    vmdtDepth (vwalkAux 2 (m01 3) [Sum.inr (0 : Fin 4)] [termA, termB]) = 1 := by

  have h0 : holeUsed (m01 3) (0 : Fin 4) = false := by

    rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

    rintro ⟨i, hi⟩; fin_cases i <;> simp [m01_app] at hi

  have hcov : vertexCoveredB (m01 3) (Sum.inr (0 : Fin 4)) = false := by

    simp [vertexCoveredB, h0]

  rw [vblock_query_hole (fuel' := 1) (m01 3) (0 : Fin 4) [] [termA, termB]

    hcov, vmdtDepth_hquery]

  have hsup :

      (Finset.univ.sup fun q =>

        vmdtDepth

          (if ((m01 3) q).isSome = true then (.leaf false : VMDTree 4 4)

           else vwalkAux 1 (compose (m01 3) (singleMatching q (0 : Fin 4)))

             [] [termA, termB])) = 0 := by

    apply le_antisymm

    · exact Finset.sup_le (fun q _ => (depth_m01_3_child q).le)

    · exact Nat.zero_le _

  omega



private theorem child01_le1 (a : Fin 4) :

    vmdtDepth

      (if holeUsed r01 a = true then (.leaf false : VMDTree 4 4)

       else vwalkAux 2 (m01 a) [Sum.inr (0 : Fin 4)] [termA, termB]) <= 1 := by

  revert a

  intro a

  fin_cases a

  · simp [hu01_0, depth_m01_0]

  · simp [hu01_1, vmdtDepth_leaf]

  · simp [hu01_2, depth_m01_2]

  · simp [hu01_3, depth_m01_3]



private theorem r01_depth_le2 :

    vmdtDepth (canonicalVMDT searchD4mp r01) <= 2 := by

  unfold canonicalVMDT

  have hell : (freePigeons r01).card = 3 := free3 0 1

  rw [hell, searchD4mp_eq]

  have hfals : termFalsifiedB r01 termA = false := by decide

  have hsat : termSatisfiedB r01 termA = false := by decide

  have hentry :=

    vwalk_entry_pigeon (fuel' := 2) r01 termA [termB] (1 : Fin 4)

      [Sum.inr (0 : Fin 4)] termA_leg hfals hsat tv01

  rw [hentry, vmdtDepth_pquery]

  have hsup :

      (Finset.univ.sup fun a =>

        vmdtDepth

          (if holeUsed r01 a = true then (.leaf false : VMDTree 4 4)

           else vwalkAux 2 (compose r01 (singleMatching (1 : Fin 4) a))

             [Sum.inr (0 : Fin 4)] [termA, termB])) <= 1 :=

    Finset.sup_le (fun a _ => by simpa [m01] using child01_le1 a)

  omega



private theorem not_ge3_r01 :

    Not (3 <= vmdtDepth (canonicalVMDT searchD4mp r01)) := by

  have h := r01_depth_le2; omega



/-- Public: depth barrier for singleMatching 0 1. -/

theorem not_depth_ge_three_singleMatching_0_1 :

    Not (3 <= vmdtDepth (canonicalVMDT searchD4mp (singleMatching (0 : Fin 4) 1))) :=

  not_ge3_r01



/-- Public: both-terms-falsified depth barrier. -/

theorem not_depth_ge_three_of_both_search_terms_falsified

    (rho : MatchingMap 4 4) (hell : (freePigeons rho).card = 3)

    (hA : termFalsifiedB rho termA = true)

    (hB : termFalsifiedB rho termB = true) :

    Not (3 <= vmdtDepth (canonicalVMDT searchD4mp rho)) :=

  not_ge3_both_fals rho hell hA hB



/-! ## Depth ≤ 2 for singleMatching (1,0) (dual of (0,1)) -/



private def r10 : MatchingMap 4 4 := singleMatching (1 : Fin 4) 0



private theorem hu10_0 : holeUsed r10 (0 : Fin 4) = true := by

  rw [holeUsed_eq_true_iff]; exact ⟨1, by simp [r10, singleMatching]⟩

private theorem hu10_1 : holeUsed r10 (1 : Fin 4) = false := by

  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

  rintro ⟨i, hi⟩; fin_cases i <;> simp [r10, singleMatching] at hi

private theorem hu10_2 : holeUsed r10 (2 : Fin 4) = false := by

  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

  rintro ⟨i, hi⟩; fin_cases i <;> simp [r10, singleMatching] at hi

private theorem hu10_3 : holeUsed r10 (3 : Fin 4) = false := by

  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

  rintro ⟨i, hi⟩; fin_cases i <;> simp [r10, singleMatching] at hi



private theorem tv10 :

    termVertices r10 termA =

      [Sum.inl (0 : Fin 4), Sum.inr (1 : Fin 4)] := by

  unfold termVertices termA pairUnresolvedB r10 singleMatching

  simp [holeUsed, finList4]



private def m10 (a : Fin 4) : MatchingMap 4 4 :=

  compose r10 (singleMatching (0 : Fin 4) a)



private theorem m10_app (a : Fin 4) :

    m10 a = fun i =>

      if i = (1 : Fin 4) then some (0 : Fin 4)

      else if i = (0 : Fin 4) then some a else none := by

  funext i

  simp [m10, r10, compose, singleMatching]

  split_ifs <;> simp_all



private theorem depth_m10_1 :

    vmdtDepth (vwalkAux 2 (m10 1) [Sum.inr (1 : Fin 4)] [termA, termB]) = 0 := by

  have hcov : vertexCoveredB (m10 1) (Sum.inr (1 : Fin 4)) = true := by

    simp [vertexCoveredB, holeUsed, finList4, m10_app]

  rw [vblock_skip_covered 2 (m10 1) (Sum.inr (1 : Fin 4)) [] [termA, termB] hcov]

  have hsat : termSatisfiedB (m10 1) termA = true := by

    simp [termSatisfiedB, termA, pairSatB, m10_app]

  have hfals : termFalsifiedB (m10 1) termA = false := by

    simp [termFalsifiedB, termA, pairFalsB, m10_app, holeUsed, finList4]

  rw [vwalk_stop_satisfied 2 (m10 1) termA [termB] termA_leg hfals hsat,

    vmdtDepth_leaf]



private theorem depth_m10_2_child (q : Fin 4) :

    vmdtDepth

      (if ((m10 2) q).isSome = true then (.leaf false : VMDTree 4 4)

       else vwalkAux 1 (compose (m10 2) (singleMatching q (1 : Fin 4)))

         [] [termA, termB]) = 0 := by

  by_cases hq : ((m10 2) q).isSome = true

  · simp [hq, vmdtDepth_leaf]

  · simp only [hq, Bool.false_eq_true, ↓reduceIte]

    let mu' := compose (m10 2) (singleMatching q (1 : Fin 4))

    have hAf : termFalsifiedB mu' termA = true := by

      unfold termFalsifiedB termA pairFalsB

      have h0 : mu' (0 : Fin 4) = some (2 : Fin 4) := by

        simp [mu', compose, singleMatching, m10_app]

      simp [h0]

    rw [vwalk_skip_falsified 1 mu' termA [termB] termA_leg hAf]

    have hBf : termFalsifiedB mu' termB = true := by

      have hqfree : q = 2 ∨ q = 3 := by

        fin_cases q <;> simp [m10_app] at hq ⊢

      unfold termFalsifiedB termB pairFalsB

      rcases hqfree with rfl | rfl

      · have h2 : mu' (2 : Fin 4) = some (1 : Fin 4) := by

          simp [mu', compose, singleMatching, m10_app]

        simp [h2]

      · have h3 : mu' (3 : Fin 4) = some (1 : Fin 4) := by

          simp [mu', compose, singleMatching, m10_app]

        simp [h3]

    rw [vwalk_skip_falsified 1 mu' termB [] termB_leg hBf, vwalk_nil,

      vmdtDepth_leaf]



private theorem depth_m10_2 :

    vmdtDepth (vwalkAux 2 (m10 2) [Sum.inr (1 : Fin 4)] [termA, termB]) = 1 := by

  have h1 : holeUsed (m10 2) (1 : Fin 4) = false := by

    rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

    rintro ⟨i, hi⟩; fin_cases i <;> simp [m10_app] at hi

  have hcov : vertexCoveredB (m10 2) (Sum.inr (1 : Fin 4)) = false := by

    simp [vertexCoveredB, h1]

  rw [vblock_query_hole (fuel' := 1) (m10 2) (1 : Fin 4) [] [termA, termB]

    hcov, vmdtDepth_hquery]

  have hsup :

      (Finset.univ.sup fun q =>

        vmdtDepth

          (if ((m10 2) q).isSome = true then (.leaf false : VMDTree 4 4)

           else vwalkAux 1 (compose (m10 2) (singleMatching q (1 : Fin 4)))

             [] [termA, termB])) = 0 := by

    apply le_antisymm

    · exact Finset.sup_le (fun q _ => (depth_m10_2_child q).le)

    · exact Nat.zero_le _

  omega



private theorem depth_m10_3_child (q : Fin 4) :

    vmdtDepth

      (if ((m10 3) q).isSome = true then (.leaf false : VMDTree 4 4)

       else vwalkAux 1 (compose (m10 3) (singleMatching q (1 : Fin 4)))

         [] [termA, termB]) = 0 := by

  by_cases hq : ((m10 3) q).isSome = true

  · simp [hq, vmdtDepth_leaf]

  · simp only [hq, Bool.false_eq_true, ↓reduceIte]

    let mu' := compose (m10 3) (singleMatching q (1 : Fin 4))

    have hAf : termFalsifiedB mu' termA = true := by

      unfold termFalsifiedB termA pairFalsB

      have h0 : mu' (0 : Fin 4) = some (3 : Fin 4) := by

        simp [mu', compose, singleMatching, m10_app]

      simp [h0]

    rw [vwalk_skip_falsified 1 mu' termA [termB] termA_leg hAf]

    have hBf : termFalsifiedB mu' termB = true := by

      have hqfree : q = 2 ∨ q = 3 := by

        fin_cases q <;> simp [m10_app] at hq ⊢

      unfold termFalsifiedB termB pairFalsB

      rcases hqfree with rfl | rfl

      · have h2 : mu' (2 : Fin 4) = some (1 : Fin 4) := by

          simp [mu', compose, singleMatching, m10_app]

        simp [h2]

      · have h3 : mu' (3 : Fin 4) = some (1 : Fin 4) := by

          simp [mu', compose, singleMatching, m10_app]

        simp [h3]

    rw [vwalk_skip_falsified 1 mu' termB [] termB_leg hBf, vwalk_nil,

      vmdtDepth_leaf]



private theorem depth_m10_3 :

    vmdtDepth (vwalkAux 2 (m10 3) [Sum.inr (1 : Fin 4)] [termA, termB]) = 1 := by

  have h1 : holeUsed (m10 3) (1 : Fin 4) = false := by

    rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]

    rintro ⟨i, hi⟩; fin_cases i <;> simp [m10_app] at hi

  have hcov : vertexCoveredB (m10 3) (Sum.inr (1 : Fin 4)) = false := by

    simp [vertexCoveredB, h1]

  rw [vblock_query_hole (fuel' := 1) (m10 3) (1 : Fin 4) [] [termA, termB]

    hcov, vmdtDepth_hquery]

  have hsup :

      (Finset.univ.sup fun q =>

        vmdtDepth

          (if ((m10 3) q).isSome = true then (.leaf false : VMDTree 4 4)

           else vwalkAux 1 (compose (m10 3) (singleMatching q (1 : Fin 4)))

             [] [termA, termB])) = 0 := by

    apply le_antisymm

    · exact Finset.sup_le (fun q _ => (depth_m10_3_child q).le)

    · exact Nat.zero_le _

  omega



private theorem child10_le1 (a : Fin 4) :

    vmdtDepth

      (if holeUsed r10 a = true then (.leaf false : VMDTree 4 4)

       else vwalkAux 2 (m10 a) [Sum.inr (1 : Fin 4)] [termA, termB]) <= 1 := by

  revert a

  intro a

  fin_cases a

  · simp [hu10_0, vmdtDepth_leaf]

  · simp [hu10_1, depth_m10_1]

  · simp [hu10_2, depth_m10_2]

  · simp [hu10_3, depth_m10_3]



private theorem r10_depth_le2 :

    vmdtDepth (canonicalVMDT searchD4mp r10) <= 2 := by

  unfold canonicalVMDT

  have hell : (freePigeons r10).card = 3 := free3 1 0

  rw [hell, searchD4mp_eq]

  have hfals : termFalsifiedB r10 termA = false := by decide

  have hsat : termSatisfiedB r10 termA = false := by decide

  have hentry :=

    vwalk_entry_pigeon (fuel' := 2) r10 termA [termB] (0 : Fin 4)

      [Sum.inr (1 : Fin 4)] termA_leg hfals hsat tv10

  rw [hentry, vmdtDepth_pquery]

  have hsup :

      (Finset.univ.sup fun a =>

        vmdtDepth

          (if holeUsed r10 a = true then (.leaf false : VMDTree 4 4)

           else vwalkAux 2 (compose r10 (singleMatching (0 : Fin 4) a))

             [Sum.inr (1 : Fin 4)] [termA, termB])) <= 1 :=

    Finset.sup_le (fun a _ => by simpa [m10] using child10_le1 a)

  omega



private theorem not_ge3_r10 :

    Not (3 <= vmdtDepth (canonicalVMDT searchD4mp r10)) := by

  have h := r10_depth_le2; omega



/-- Public: depth barrier for singleMatching 1 0. -/

theorem not_depth_ge_three_singleMatching_1_0 :

    Not (3 <= vmdtDepth (canonicalVMDT searchD4mp (singleMatching (1 : Fin 4) 0))) :=

  not_ge3_r10



/-! ## Length ≠ 2 when one searchD4mp term is pre-falsified -/

private theorem pairUnresolvedB_eq_false_of_inl_covered
    {p h : Nat} (mu : MatchingMap p h) (e : Fin p × Fin h)
    (hc : vertexCoveredB mu (Sum.inl e.1) = true) :
    pairUnresolvedB mu e = false := by
  unfold pairUnresolvedB vertexCoveredB at *
  cases hmu : mu e.1 <;> simp_all

private theorem pair_sat_or_fals_of_not_unresolved
    {p h : Nat} (mu : MatchingMap p h) (e : Fin p × Fin h)
    (h : pairUnresolvedB mu e = false) :
    pairSatB mu e = true ∨ pairFalsB mu e = true := by
  have tri := pair_status_trichotomy mu e
  cases hs : pairSatB mu e <;> cases hf : pairFalsB mu e <;>
    cases hu : pairUnresolvedB mu e <;> simp_all

private theorem pair_sat_or_fals_of_frozen_covered
    {p h : Nat} {mu nu : MatchingMap p h} (t : MTerm p h) (e : Fin p × Fin h)
    (he : e ∈ t) (hag : MAgree mu nu) (hnu : IsMatching nu)
    (hcov : ∀ w ∈ termVertices mu t, vertexCoveredB nu w = true) :
    pairSatB nu e = true ∨ pairFalsB nu e = true := by
  by_cases hun : pairUnresolvedB mu e = true
  · have hinl : Sum.inl e.1 ∈ termVertices mu t := by
      unfold termVertices
      exact List.mem_bind.mpr ⟨e, List.mem_filter.mpr ⟨he, hun⟩,
        List.mem_cons_self _ _⟩
    exact pair_sat_or_fals_of_not_unresolved nu e
      (pairUnresolvedB_eq_false_of_inl_covered nu e (hcov _ hinl))
  · have hun' : pairUnresolvedB mu e = false := Bool.eq_false_iff.mpr hun
    rcases pair_sat_or_fals_of_not_unresolved mu e hun' with hs | hf
    · left
      unfold pairSatB at hs ⊢
      cases hmu : mu e.1 with
      | none => simp [hmu] at hs
      | some b =>
          have hb : (b == e.2) = true := by simpa [hmu] using hs
          have hbeq : b = e.2 := beq_iff_eq.mp hb
          have hnu' : nu e.1 = some e.2 := by
            simpa [hbeq] using hag e.1 b hmu
          simp [hnu']
    · exact Or.inr (pairFalsB_mono hag hnu e hf)

private theorem term_determined_of_frozen_covered
    {p h : Nat} {mu nu : MatchingMap p h} (t : MTerm p h)
    (hag : MAgree mu nu) (hnu : IsMatching nu)
    (hcov : ∀ w ∈ termVertices mu t, vertexCoveredB nu w = true) :
    termSatisfiedB nu t = true ∨ termFalsifiedB nu t = true := by
  by_cases hf : termFalsifiedB nu t = true
  · exact Or.inr hf
  · left
    have hnf : termFalsifiedB nu t = false := Bool.eq_false_iff.mpr hf
    unfold termSatisfiedB
    rw [List.all_eq_true]
    intro e he
    rcases pair_sat_or_fals_of_frozen_covered t e he hag hnu hcov with hs | hpf
    · exact hs
    · have hany : termFalsifiedB nu t = true := by
        unfold termFalsifiedB
        exact List.any_eq_true.mpr ⟨e, he, hpf⟩
      exact absurd hany (ne_of_eq_of_ne hnf Bool.false_ne_true)

private theorem first_term_determined_at_second_entry
    {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (feed : List (Vertex p h)) (hrho : IsMatching rho)
    (B₀ B₁ : VBlock p h) (rest : List (VBlock p h))
    (hblocks : blocksOf (vtrace rho D feed) = B₀ :: B₁ :: rest) :
    termSatisfiedB B₁.entry B₀.term = true ∨
      termFalsifiedB B₁.entry B₀.term = true := by
  have hpath :
      B₁.entry =
        compose B₀.entry (pairsToMatching (B₀.steps.map VStep.pair)) :=
    second_block_entry_eq_compose_first_steps rho D feed B₀ B₁ rest hblocks
  have hfrozen :=
    blocksOf_frozen_covered (freePigeons rho).card rho [] D feed
  have hcov :
      ∀ w ∈ termVertices B₀.entry B₀.term,
        vertexCoveredB
          (compose B₀.entry (pairsToMatching (B₀.steps.map VStep.pair)))
          w = true := by
    have hp : List.Pairwise
        (fun B _ => ∀ w ∈ termVertices B.entry B.term,
          vertexCoveredB
            (compose B.entry (pairsToMatching (B.steps.map VStep.pair)))
            w = true)
        (B₀ :: B₁ :: rest) := by
      change List.Pairwise _ (blocksOf (vtrace rho D feed)) at hfrozen
      rwa [hblocks] at hfrozen
    exact (List.pairwise_cons.mp hp).1 B₁ (List.mem_cons_self _ _)
  have hB₁mem : B₁ ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]
    exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
  have hmatch₁ : IsMatching B₁.entry :=
    blocksOf_entry_isMatching (freePigeons rho).card rho [] D feed hrho
      B₁.term B₁.entry (enter_mem_of_mem_blocksOf _ B₁ hB₁mem)
  have hag : MAgree B₀.entry B₁.entry := by
    rw [hpath]; exact mAgree_compose_left _ _
  exact term_determined_of_frozen_covered (mu := B₀.entry) (nu := B₁.entry)
    B₀.term hag hmatch₁ (by intro w hw; simpa [hpath] using hcov w hw)

private theorem firstNotFalsified_searchD4mp_of_termA_fals
    (mu : MatchingMap 4 4) (hA : termFalsifiedB mu termA = true) :
    firstNotFalsifiedTerm mu searchD4mp =
      (if termFalsifiedB mu termB = true then none else some termB) := by
  rw [show searchD4mp = [termA, termB] from searchD4mp_eq]
  -- Force the recursive definition open on the cons
  show (if termMatchingLegalB termA = false then
          firstNotFalsifiedTerm mu [termB]
        else if termFalsifiedB mu termA = true then
          firstNotFalsifiedTerm mu [termB]
        else some termA) =
    (if termFalsifiedB mu termB = true then none else some termB)
  rw [termA_leg, hA]
  -- both guards reduce: not illegal, is falsified -> recurse
  simp only [Bool.true_eq_false, ↓reduceIte]
  show (if termMatchingLegalB termB = false then
          firstNotFalsifiedTerm mu ([] : MDNF 4 4)
        else if termFalsifiedB mu termB = true then
          firstNotFalsifiedTerm mu ([] : MDNF 4 4)
        else some termB) =
    (if termFalsifiedB mu termB = true then none else some termB)
  rw [termB_leg]
  simp only [Bool.true_eq_false, ↓reduceIte]
  show (if termFalsifiedB mu termB = true then
          firstNotFalsifiedTerm mu ([] : MDNF 4 4)
        else some termB) =
    (if termFalsifiedB mu termB = true then none else some termB)
  have hnil : firstNotFalsifiedTerm mu ([] : MDNF 4 4) = none := rfl
  simp only [hnil]

private theorem firstNotFalsified_searchD4mp_both_fals
    (mu : MatchingMap 4 4)
    (hA : termFalsifiedB mu termA = true)
    (hB : termFalsifiedB mu termB = true) :
    firstNotFalsifiedTerm mu searchD4mp = none := by
  simp [firstNotFalsified_searchD4mp_of_termA_fals mu hA, hB]

private theorem firstNotFalsified_searchD4mp_termA_live
    (mu : MatchingMap 4 4) (hA : termFalsifiedB mu termA = false) :
    firstNotFalsifiedTerm mu searchD4mp = some termA := by
  change firstNotFalsifiedTerm mu [termA, termB] = some termA
  simp [firstNotFalsifiedTerm, termA_leg, hA]

private theorem mAgree_base_second_entry
    {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (feed : List (Vertex p h)) (B₀ B₁ : VBlock p h) (rest : List (VBlock p h))
    (hblocks : blocksOf (vtrace rho D feed) = B₀ :: B₁ :: rest) :
    MAgree rho B₁.entry := by
  have hentry₀ : B₀.entry = rho :=
    first_block_entry_eq_base rho D feed B₀ (B₁ :: rest) hblocks
  have hpath :=
    second_block_entry_eq_compose_first_steps rho D feed B₀ B₁ rest hblocks
  rw [← hentry₀, hpath]
  exact mAgree_compose_left _ _

private theorem mem_searchD4mp_iff (t : MTerm 4 4) :
    t ∈ searchD4mp ↔ t = termA ∨ t = termB := by
  simp [searchD4mp]

/-- Length ≠ 2 when `termA` is already falsified at the base. -/
theorem enteredTermsOf_length_ne_two_of_termA_fals
    (rho : MatchingMap 4 4) (hrho : IsMatching rho)
    (hA : termFalsifiedB rho termA = true)
    (_ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho)) :
    (enteredTermsOf rho searchD4mp 3).length ≠ 2 := by
  intro hlen
  let feed := leftmostLiveDeepFeed rho searchD4mp 3
  have hlenB : (blocksOf (vtrace rho searchD4mp feed)).length = 2 := by
    simpa [enteredTermsOf, feed, List.length_map] using hlen
  match hblocks : blocksOf (vtrace rho searchD4mp feed) with
  | [] => simp [hblocks] at hlenB
  | [_] => simp [hblocks] at hlenB
  | B₀ :: B₁ :: rest =>
      have hrest : rest = [] := by
        have : (B₀ :: B₁ :: rest).length = 2 := by simpa [hblocks] using hlenB
        simp only [List.length_cons] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hrest
      have hB₀mem : B₀ ∈ blocksOf (vtrace rho searchD4mp feed) := by
        rw [hblocks]; exact List.mem_cons_self _ _
      have hB₁mem : B₁ ∈ blocksOf (vtrace rho searchD4mp feed) := by
        rw [hblocks]
        exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      have hspec₀ :=
        blocksOf_entry_spec (freePigeons rho).card rho [] searchD4mp feed
          B₀ hB₀mem
      have hspec₁ :=
        blocksOf_entry_spec (freePigeons rho).card rho [] searchD4mp feed
          B₁ hB₁mem
      have hentry₀ : B₀.entry = rho :=
        first_block_entry_eq_base rho searchD4mp feed B₀ [B₁] hblocks
      have hmatch₁ : IsMatching B₁.entry :=
        blocksOf_entry_isMatching (freePigeons rho).card rho [] searchD4mp feed
          hrho B₁.term B₁.entry (enter_mem_of_mem_blocksOf _ B₁ hB₁mem)
      have hag := mAgree_base_second_entry rho searchD4mp feed B₀ B₁ [] hblocks
      have hA₁ : termFalsifiedB B₁.entry termA = true :=
        termFalsifiedB_mono hag hmatch₁ termA hA
      have hB₀nf : termFalsifiedB rho B₀.term = false := by
        simpa [hentry₀] using hspec₀.2.2.1
      have hB₀term : B₀.term = termB := by
        have hmem : B₀.term ∈ searchD4mp := by
          rcases blocksOf_entered_first (freePigeons rho).card rho []
              searchD4mp feed hrho B₀ hB₀mem with ⟨pre, suf, hD, _⟩
          rw [hD]; exact List.mem_append_right _ (List.mem_cons_self _ _)
        rcases (mem_searchD4mp_iff _).mp hmem with h | h
        · rw [h, hA] at hB₀nf; exact Bool.noConfusion hB₀nf
        · exact h
      have hdet :=
        first_term_determined_at_second_entry rho searchD4mp feed hrho
          B₀ B₁ [] hblocks
      have hfnf :
          firstNotFalsifiedTerm B₁.entry searchD4mp = some B₁.term :=
        block_term_eq_firstNotFalsified_entry rho searchD4mp feed hrho B₁
          hB₁mem
      rw [hB₀term] at hdet
      rcases hdet with hsat | hfals
      · have hBnf :=
          termFalsifiedB_eq_false_of_termSatisfiedB B₁.entry termB hsat
        have hfnf' :
            firstNotFalsifiedTerm B₁.entry searchD4mp = some termB := by
          rw [firstNotFalsified_searchD4mp_of_termA_fals B₁.entry hA₁, hBnf]
          rfl
        have hterms : B₁.term = termB :=
          Option.some.inj (hfnf.symm.trans hfnf')
        have hnsat : termSatisfiedB B₁.entry B₁.term = false := hspec₁.2.2.2
        rw [hterms, hsat] at hnsat
        exact Bool.noConfusion hnsat
      · have hfnf' :
            firstNotFalsifiedTerm B₁.entry searchD4mp = none :=
          firstNotFalsified_searchD4mp_both_fals B₁.entry hA₁ hfals
        rw [hfnf'] at hfnf
        exact Option.noConfusion hfnf

/-- Length ≠ 2 when `termB` is already falsified at the base. -/
theorem enteredTermsOf_length_ne_two_of_termB_fals
    (rho : MatchingMap 4 4) (hrho : IsMatching rho)
    (hB : termFalsifiedB rho termB = true)
    (_ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho)) :
    (enteredTermsOf rho searchD4mp 3).length ≠ 2 := by
  intro hlen
  let feed := leftmostLiveDeepFeed rho searchD4mp 3
  have hlenB : (blocksOf (vtrace rho searchD4mp feed)).length = 2 := by
    simpa [enteredTermsOf, feed, List.length_map] using hlen
  match hblocks : blocksOf (vtrace rho searchD4mp feed) with
  | [] => simp [hblocks] at hlenB
  | [_] => simp [hblocks] at hlenB
  | B₀ :: B₁ :: rest =>
      have hrest : rest = [] := by
        have : (B₀ :: B₁ :: rest).length = 2 := by simpa [hblocks] using hlenB
        simp only [List.length_cons] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hrest
      have hB₀mem : B₀ ∈ blocksOf (vtrace rho searchD4mp feed) := by
        rw [hblocks]; exact List.mem_cons_self _ _
      have hB₁mem : B₁ ∈ blocksOf (vtrace rho searchD4mp feed) := by
        rw [hblocks]
        exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      have hspec₀ :=
        blocksOf_entry_spec (freePigeons rho).card rho [] searchD4mp feed
          B₀ hB₀mem
      have hspec₁ :=
        blocksOf_entry_spec (freePigeons rho).card rho [] searchD4mp feed
          B₁ hB₁mem
      have hentry₀ : B₀.entry = rho :=
        first_block_entry_eq_base rho searchD4mp feed B₀ [B₁] hblocks
      have hmatch₁ : IsMatching B₁.entry :=
        blocksOf_entry_isMatching (freePigeons rho).card rho [] searchD4mp feed
          hrho B₁.term B₁.entry (enter_mem_of_mem_blocksOf _ B₁ hB₁mem)
      have hag := mAgree_base_second_entry rho searchD4mp feed B₀ B₁ [] hblocks
      have hB₁f : termFalsifiedB B₁.entry termB = true :=
        termFalsifiedB_mono hag hmatch₁ termB hB
      have hB₀nf : termFalsifiedB rho B₀.term = false := by
        simpa [hentry₀] using hspec₀.2.2.1
      have hB₀term : B₀.term = termA := by
        have hmem : B₀.term ∈ searchD4mp := by
          rcases blocksOf_entered_first (freePigeons rho).card rho []
              searchD4mp feed hrho B₀ hB₀mem with ⟨pre, suf, hD, _⟩
          rw [hD]; exact List.mem_append_right _ (List.mem_cons_self _ _)
        rcases (mem_searchD4mp_iff _).mp hmem with h | h
        · exact h
        · rw [h, hB] at hB₀nf; exact Bool.noConfusion hB₀nf
      have hdet :=
        first_term_determined_at_second_entry rho searchD4mp feed hrho
          B₀ B₁ [] hblocks
      have hfnf :
          firstNotFalsifiedTerm B₁.entry searchD4mp = some B₁.term :=
        block_term_eq_firstNotFalsified_entry rho searchD4mp feed hrho B₁
          hB₁mem
      rw [hB₀term] at hdet
      rcases hdet with hsat | hfals
      · -- termA sat at B₁.entry ⇒ firstNotFalsified = termA ⇒ B₁.term = termA
        have hAnf :=
          termFalsifiedB_eq_false_of_termSatisfiedB B₁.entry termA hsat
        have hfnf' :
            firstNotFalsifiedTerm B₁.entry searchD4mp = some termA :=
          firstNotFalsified_searchD4mp_termA_live B₁.entry hAnf
        have hterms : B₁.term = termA :=
          Option.some.inj (hfnf.symm.trans hfnf')
        have hnsat : termSatisfiedB B₁.entry B₁.term = false := hspec₁.2.2.2
        rw [hterms, hsat] at hnsat
        exact Bool.noConfusion hnsat
      · -- termA fals at B₁.entry, termB fals ⇒ firstNotFalsified = none
        have hfnf' :
            firstNotFalsifiedTerm B₁.entry searchD4mp = none :=
          firstNotFalsified_searchD4mp_both_fals B₁.entry hfals hB₁f
        rw [hfnf'] at hfnf
        exact Option.noConfusion hfnf

/-! ## Diagonal single-edge length barriers -/

theorem enteredTermsOf_length_ne_two_singleMatching_0_0
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp
      (singleMatching (0 : Fin 4) 0))) :
    (enteredTermsOf (singleMatching (0 : Fin 4) 0) searchD4mp 3).length ≠ 2 :=
  enteredTermsOf_length_ne_two_of_termA_fals _
    (isMatching_singleMatching _ _) (by decide) ht

theorem enteredTermsOf_length_ne_two_singleMatching_1_1
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp
      (singleMatching (1 : Fin 4) 1))) :
    (enteredTermsOf (singleMatching (1 : Fin 4) 1) searchD4mp 3).length ≠ 2 :=
  enteredTermsOf_length_ne_two_of_termA_fals _
    (isMatching_singleMatching _ _) (by decide) ht

theorem enteredTermsOf_length_ne_two_singleMatching_2_2
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp
      (singleMatching (2 : Fin 4) 2))) :
    (enteredTermsOf (singleMatching (2 : Fin 4) 2) searchD4mp 3).length ≠ 2 :=
  enteredTermsOf_length_ne_two_of_termB_fals _
    (isMatching_singleMatching _ _) (by decide) ht

theorem enteredTermsOf_length_ne_two_singleMatching_3_3
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp
      (singleMatching (3 : Fin 4) 3))) :
    (enteredTermsOf (singleMatching (3 : Fin 4) 3) searchD4mp 3).length ≠ 2 :=
  enteredTermsOf_length_ne_two_of_termB_fals _
    (isMatching_singleMatching _ _) (by decide) ht

/-! ## Free-count-3 length-2 classification -/

private theorem both_fals_of_single_edge_off_block (i a : Fin 4)
    (hA : termFalsifiedB (singleMatching i a) termA = true)
    (hB : termFalsifiedB (singleMatching i a) termB = true) :
    Not (3 ≤ vmdtDepth (canonicalVMDT searchD4mp (singleMatching i a))) :=
  not_ge3_both_fals (singleMatching i a) (free3 i a) hA hB

/-- Every free-count-3 depth-eligible length-2 base is `rhoA` or `rhoB`. -/
theorem length_two_free_count_three_eq_rhoA_or_rhoB
    (rho : MatchingMap 4 4) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = 3)
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho))
    (hlen : (enteredTermsOf rho searchD4mp 3).length = 2) :
    rho = rhoA ∨ rho = rhoB := by
  obtain ⟨i, a, rfl⟩ := eq_singleMatching_of_free_count_three rho hrho hell
  fin_cases i <;> fin_cases a
  · -- (0,0)
    exact (enteredTermsOf_length_ne_two_singleMatching_0_0 ht hlen).elim
  · -- (0,1)
    exact (not_depth_ge_three_singleMatching_0_1 ht).elim
  · -- (0,2) both fals
    exact (both_fals_of_single_edge_off_block 0 2 (by decide) (by decide) ht).elim
  · -- (0,3) both fals
    exact (both_fals_of_single_edge_off_block 0 3 (by decide) (by decide) ht).elim
  · -- (1,0)
    exact (not_depth_ge_three_singleMatching_1_0 ht).elim
  · -- (1,1)
    exact (enteredTermsOf_length_ne_two_singleMatching_1_1 ht hlen).elim
  · -- (1,2) both fals
    exact (both_fals_of_single_edge_off_block 1 2 (by decide) (by decide) ht).elim
  · -- (1,3) both fals
    exact (both_fals_of_single_edge_off_block 1 3 (by decide) (by decide) ht).elim
  · -- (2,0) both fals
    exact (both_fals_of_single_edge_off_block 2 0 (by decide) (by decide) ht).elim
  · -- (2,1) both fals
    exact (both_fals_of_single_edge_off_block 2 1 (by decide) (by decide) ht).elim
  · -- (2,2)
    exact (enteredTermsOf_length_ne_two_singleMatching_2_2 ht hlen).elim
  · -- (2,3) = rhoA
    left; rfl
  · -- (3,0) both fals
    exact (both_fals_of_single_edge_off_block 3 0 (by decide) (by decide) ht).elim
  · -- (3,1) both fals
    exact (both_fals_of_single_edge_off_block 3 1 (by decide) (by decide) ht).elim
  · -- (3,2) = rhoB
    right; rfl
  · -- (3,3)
    exact (enteredTermsOf_length_ne_two_singleMatching_3_3 ht hlen).elim

/-! ## Residual discharge at ell = 3 -/

/-- **S2206:** length-2 exit residual on Fin 4 / `searchD4mp` / `t = 3` /
`ell = 3`. Equal codes force equal second-block path entries: every length-2
depth-eligible free-count-3 base is `rhoA` or `rhoB`, whose codes differ. -/
theorem encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_ell_three :
    EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := 3) rfl searchD4mp searchD4mp_width := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode hlen
  have h1 := length_two_free_count_three_eq_rhoA_or_rhoB rho₁ hrho₁ hell₁ ht₁
    hlen
  have hlen₂ :
      (enteredTermsOf rho₂ searchD4mp 3).length = 2 := by
    have hlenG :=
      enteredTermsOf_length_eq_of_encodeMatch_eq (p := 4) (h := 4) (w := 2)
        (t := 3) (ell := 3) rfl rho₁ rho₂ searchD4mp hrho₁ hrho₂ hell₁ hell₂
        ht₁ ht₂ searchD4mp_width hcode
    exact hlenG.symm ▸ hlen
  have h2 := length_two_free_count_three_eq_rhoA_or_rhoB rho₂ hrho₂ hell₂ ht₂
    hlen₂
  -- Case analysis on {rhoA, rhoB}
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · -- both rhoA
    simp [h1, h2]
  · -- rhoA / rhoB: codes differ
    subst h1; subst h2
    exact absurd hcode (encodeMatch_rhoA_ne_rhoB ht₁ ht₂)
  · -- rhoB / rhoA: codes differ
    subst h1; subst h2
    exact absurd hcode (Ne.symm (encodeMatch_rhoA_ne_rhoB ht₂ ht₁))
  · -- both rhoB
    simp [h1, h2]

/-- Package residual for every free-count: combine S2205 `ell ≠ 3` with
S2206 `ell = 3`. -/
theorem encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three
    {ell : Nat} :
    EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl searchD4mp searchD4mp_width := by
  by_cases h : ell = 3
  · subst h
    exact encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_ell_three
  · exact encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_of_ell_ne_three h

/-! ## Summary -/

/-- **S2206 length-2 base classification summary** (Fin 4 / `searchD4mp` /
`t = 3`). -/
theorem length_two_class_fin4_t_three_summary :
    (∀ (rho : MatchingMap 4 4), IsMatching rho →
      (freePigeons rho).card = 3 →
      3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho) →
      (enteredTermsOf rho searchD4mp 3).length = 2 →
        rho = rhoA ∨ rho = rhoB) ∧
      EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
        (ell := 3) rfl searchD4mp searchD4mp_width ∧
      (∀ {ell : Nat},
        EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
          (ell := ell) rfl searchD4mp searchD4mp_width) ∧
      Not (3 ≤ vmdtDepth (canonicalVMDT searchD4mp
        (singleMatching (0 : Fin 4) 1))) ∧
      Not (3 ≤ vmdtDepth (canonicalVMDT searchD4mp
        (singleMatching (1 : Fin 4) 0))) :=
  ⟨fun rho hrho hell ht hlen =>
      length_two_free_count_three_eq_rhoA_or_rhoB rho hrho hell ht hlen,
    encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_ell_three,
    fun {_ell} => encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three,
    not_depth_ge_three_singleMatching_0_1,
    not_depth_ge_three_singleMatching_1_0⟩

end PHPMatchingEncodeLengthTwoClass
end PvNP

