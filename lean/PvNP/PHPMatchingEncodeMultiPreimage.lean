import PvNP.PHPMatchingEncodeInjectivity
import PvNP.PHPMatchingEncodeCollisionSearch
import Mathlib.Tactic.FinCases

/-!
# S2204: multi-preimage length-2 path-exit package

Board `Fin 4`, dual width-2 DNF `searchD4mp` with terms
`[(0,1),(1,0)]` and `[(2,3),(3,2)]`, depth `t = 3`, free-count `ell = 3`
(`t ≤ ell < p`, multi free-count-3 matchings).

Named multi-preimage witnesses (both depth-eligible, entered-term length 2):

* `rhoA = singleMatching 2 3` (pigeon 2 ↦ hole 3)
* `rhoB = singleMatching 3 2` (pigeon 3 ↦ hole 2)

Leftmost live depth-3 paths:

* both enter the first width-2 term and walk pairs `(0,0),(1,1)` (falsifying);
* then enter the second width-2 term on the unique remaining unresolved pair
  and take one satisfying step — different third queries / path exits.

Honest bounds:

* multi-preimage length-2 domain is non-empty (`rhoA ≠ rhoB`, both eligible);
* first-block path exits differ;
* `encodeMatch` codes differ on this named pair (via distinct second-block
  `G2` β-marks) — **no bank collision** on the named fiber;
* `EncodeMatchLengthTwoExitEqResidual` is **not** discharged by unique
  preimage on this package (many free-count-3 matchings); packet-only
  walked-pair recovery remains open in general.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
No v0.11.0 tag (subtype `InjOn` not landed).
-/

namespace PvNP
namespace PHPMatchingEncodeMultiPreimage

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open RestrictedPHPFloor

/-! ## Search family and named bases -/

/-- First width-2 term (anti-diagonal on pigeons 0,1). -/
def termA : MTerm 4 4 :=
  [((0 : Fin 4), (1 : Fin 4)), ((1 : Fin 4), (0 : Fin 4))]

/-- Second width-2 term (anti-diagonal on pigeons 2,3). -/
def termB : MTerm 4 4 :=
  [((2 : Fin 4), (3 : Fin 4)), ((3 : Fin 4), (2 : Fin 4))]

/-- Dual width-2 multi-preimage search DNF on Fin 4. -/
def searchD4mp : MDNF 4 4 := [termA, termB]

theorem searchD4mp_eq : searchD4mp = [termA, termB] := rfl

theorem termA_length : termA.length = 2 := rfl
theorem termB_length : termB.length = 2 := rfl

theorem searchD4mp_has_width_ge_two : ∃ term ∈ searchD4mp, 2 ≤ term.length :=
  ⟨termA, by simp [searchD4mp], by simp [termA_length]⟩

theorem searchD4mp_width : ∀ term ∈ searchD4mp, term.length ≤ 2 := by
  intro term ht
  have ht' : term = termA ∨ term = termB := by simpa [searchD4mp] using ht
  rcases ht' with h | h <;> subst h <;> decide

/-- Multi-preimage base A: pigeon 2 ↦ hole 3. -/
def rhoA : MatchingMap 4 4 := singleMatching (2 : Fin 4) 3

/-- Multi-preimage base B: pigeon 3 ↦ hole 2. -/
def rhoB : MatchingMap 4 4 := singleMatching (3 : Fin 4) 2

theorem isMatching_singleMatching {p h : Nat} (i : Fin p) (a : Fin h) :
    IsMatching (singleMatching i a) := by
  intro j k b hj hk
  unfold singleMatching at hj hk
  by_cases hji : j = i
  · by_cases hki : k = i
    · exact hji.trans hki.symm
    · simp [hki] at hk
  · simp [hji] at hj

theorem isMatching_rhoA : IsMatching rhoA := isMatching_singleMatching _ _
theorem isMatching_rhoB : IsMatching rhoB := isMatching_singleMatching _ _

theorem rhoA_apply :
    rhoA = fun i => if i = (2 : Fin 4) then some (3 : Fin 4) else none := rfl

theorem rhoB_apply :
    rhoB = fun i => if i = (3 : Fin 4) then some (2 : Fin 4) else none := rfl

theorem rhoA_ne_rhoB : rhoA ≠ rhoB := by
  intro h
  have h2 : rhoA (2 : Fin 4) = rhoB (2 : Fin 4) := by rw [h]
  simp [rhoA, rhoB, singleMatching] at h2

private theorem finList_4 : finList 4 = [(0 : Fin 4), 1, 2, 3] := by
  unfold finList
  simp [List.range_succ, List.range_zero]

/-! ## Free-count ell = 3 -/

theorem freePigeons_rhoA : (freePigeons rhoA).card = 3 := by
  have h : freePigeons rhoA = ({(0 : Fin 4), 1, 3} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [freePigeons, rhoA, singleMatching]
  rw [h]
  decide

theorem freePigeons_rhoB : (freePigeons rhoB).card = 3 := by
  have h : freePigeons rhoB = ({(0 : Fin 4), 1, 2} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [freePigeons, rhoB, singleMatching]
  rw [h]
  decide

/-! ## Path intermediate matchings -/

private def muA1 : MatchingMap 4 4 :=
  compose rhoA (singleMatching (0 : Fin 4) 0)

private def muA2 : MatchingMap 4 4 :=
  compose muA1 (singleMatching (1 : Fin 4) 1)

private def muB1 : MatchingMap 4 4 :=
  compose rhoB (singleMatching (0 : Fin 4) 0)

private def muB2 : MatchingMap 4 4 :=
  compose muB1 (singleMatching (1 : Fin 4) 1)

private theorem muA1_apply :
    muA1 = fun i =>
      if i = (2 : Fin 4) then some (3 : Fin 4)
      else if i = (0 : Fin 4) then some (0 : Fin 4) else none := by
  funext i
  simp [muA1, rhoA, compose, singleMatching]
  split_ifs <;> simp_all

private theorem muA2_apply :
    muA2 = fun i =>
      if i = (2 : Fin 4) then some (3 : Fin 4)
      else if i = (0 : Fin 4) then some (0 : Fin 4)
      else if i = (1 : Fin 4) then some (1 : Fin 4) else none := by
  funext i
  simp [muA2, muA1, rhoA, compose, singleMatching]
  split_ifs <;> simp_all

private theorem muB1_apply :
    muB1 = fun i =>
      if i = (3 : Fin 4) then some (2 : Fin 4)
      else if i = (0 : Fin 4) then some (0 : Fin 4) else none := by
  funext i
  simp [muB1, rhoB, compose, singleMatching]
  split_ifs <;> simp_all

private theorem muB2_apply :
    muB2 = fun i =>
      if i = (3 : Fin 4) then some (2 : Fin 4)
      else if i = (0 : Fin 4) then some (0 : Fin 4)
      else if i = (1 : Fin 4) then some (1 : Fin 4) else none := by
  funext i
  simp [muB2, muB1, rhoB, compose, singleMatching]
  split_ifs <;> simp_all

/-! ## Hole-used facts -/

private theorem holeUsed_rhoA_0 : holeUsed rhoA (0 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [rhoA, singleMatching] at hi

private theorem holeUsed_rhoA_1 : holeUsed rhoA (1 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [rhoA, singleMatching] at hi

private theorem holeUsed_rhoA_2 : holeUsed rhoA (2 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [rhoA, singleMatching] at hi

private theorem holeUsed_rhoA_3 : holeUsed rhoA (3 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨2, by simp [rhoA, singleMatching]⟩

private theorem holeUsed_rhoB_0 : holeUsed rhoB (0 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [rhoB, singleMatching] at hi

private theorem holeUsed_rhoB_1 : holeUsed rhoB (1 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [rhoB, singleMatching] at hi

private theorem holeUsed_rhoB_2 : holeUsed rhoB (2 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨3, by simp [rhoB, singleMatching]⟩

private theorem holeUsed_rhoB_3 : holeUsed rhoB (3 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [rhoB, singleMatching] at hi

private theorem holeUsed_muA1_0 : holeUsed muA1 (0 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨0, by simp [muA1_apply]⟩

private theorem holeUsed_muA1_1 : holeUsed muA1 (1 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [muA1_apply] at hi

private theorem holeUsed_muA1_2 : holeUsed muA1 (2 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [muA1_apply] at hi

private theorem holeUsed_muA1_3 : holeUsed muA1 (3 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨2, by simp [muA1_apply]⟩

private theorem holeUsed_muA2_0 : holeUsed muA2 (0 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨0, by simp [muA2_apply]⟩

private theorem holeUsed_muA2_1 : holeUsed muA2 (1 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨1, by simp [muA2_apply]⟩

private theorem holeUsed_muA2_2 : holeUsed muA2 (2 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [muA2_apply] at hi

private theorem holeUsed_muA2_3 : holeUsed muA2 (3 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨2, by simp [muA2_apply]⟩

private theorem holeUsed_muB1_0 : holeUsed muB1 (0 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨0, by simp [muB1_apply]⟩

private theorem holeUsed_muB1_1 : holeUsed muB1 (1 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [muB1_apply] at hi

private theorem holeUsed_muB1_2 : holeUsed muB1 (2 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨3, by simp [muB1_apply]⟩

private theorem holeUsed_muB1_3 : holeUsed muB1 (3 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [muB1_apply] at hi

private theorem holeUsed_muB2_0 : holeUsed muB2 (0 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨0, by simp [muB2_apply]⟩

private theorem holeUsed_muB2_1 : holeUsed muB2 (1 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨1, by simp [muB2_apply]⟩

private theorem holeUsed_muB2_2 : holeUsed muB2 (2 : Fin 4) = true := by
  rw [holeUsed_eq_true_iff]; exact ⟨3, by simp [muB2_apply]⟩

private theorem holeUsed_muB2_3 : holeUsed muB2 (3 : Fin 4) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩; fin_cases i <;> simp [muB2_apply] at hi

/-! ## Term legality / status -/

private theorem termA_legal : termMatchingLegalB termA = true := by
  unfold termA termMatchingLegalB hasDupB
  decide

private theorem termB_legal : termMatchingLegalB termB = true := by
  unfold termB termMatchingLegalB hasDupB
  decide

private theorem termA_not_fals_rhoA :
    termFalsifiedB rhoA termA = false := by
  unfold termFalsifiedB termA pairFalsB rhoA singleMatching
  simp [holeUsed, finList_4]

private theorem termA_not_sat_rhoA :
    termSatisfiedB rhoA termA = false := by
  unfold termSatisfiedB termA pairSatB rhoA singleMatching
  simp

private theorem termA_not_fals_rhoB :
    termFalsifiedB rhoB termA = false := by
  unfold termFalsifiedB termA pairFalsB rhoB singleMatching
  simp [holeUsed, finList_4]

private theorem termA_not_sat_rhoB :
    termSatisfiedB rhoB termA = false := by
  unfold termSatisfiedB termA pairSatB rhoB singleMatching
  simp

private theorem termVertices_rhoA_termA :
    termVertices rhoA termA =
      [Sum.inl (0 : Fin 4), Sum.inr (1 : Fin 4),
        Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] := by
  unfold termVertices termA pairUnresolvedB rhoA singleMatching
  simp [holeUsed, finList_4]

private theorem termVertices_rhoB_termA :
    termVertices rhoB termA =
      [Sum.inl (0 : Fin 4), Sum.inr (1 : Fin 4),
        Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] := by
  unfold termVertices termA pairUnresolvedB rhoB singleMatching
  simp [holeUsed, finList_4]

private theorem vertexCovered_muA1_inr1 :
    vertexCoveredB muA1 (Sum.inr (1 : Fin 4)) = false := by
  simp [vertexCoveredB, holeUsed_muA1_1]

private theorem vertexCovered_muA2_inl1 :
    vertexCoveredB muA2 (Sum.inl (1 : Fin 4)) = true := by
  simp [vertexCoveredB, muA2_apply]

private theorem vertexCovered_muA2_inr0 :
    vertexCoveredB muA2 (Sum.inr (0 : Fin 4)) = true := by
  simp [vertexCoveredB, holeUsed_muA2_0]

private theorem vertexCovered_muB1_inr1 :
    vertexCoveredB muB1 (Sum.inr (1 : Fin 4)) = false := by
  simp [vertexCoveredB, holeUsed_muB1_1]

private theorem vertexCovered_muB2_inl1 :
    vertexCoveredB muB2 (Sum.inl (1 : Fin 4)) = true := by
  simp [vertexCoveredB, muB2_apply]

private theorem vertexCovered_muB2_inr0 :
    vertexCoveredB muB2 (Sum.inr (0 : Fin 4)) = true := by
  simp [vertexCoveredB, holeUsed_muB2_0]

private theorem termA_fals_muA2 : termFalsifiedB muA2 termA = true := by
  unfold termFalsifiedB termA pairFalsB
  simp [muA2_apply]

private theorem termA_fals_muB2 : termFalsifiedB muB2 termA = true := by
  unfold termFalsifiedB termA pairFalsB
  simp [muB2_apply]

private theorem termB_not_fals_muA2 :
    termFalsifiedB muA2 termB = false := by
  unfold termFalsifiedB termB pairFalsB
  have h2 : muA2 (2 : Fin 4) = some (3 : Fin 4) := by simp [muA2_apply]
  have h3 : muA2 (3 : Fin 4) = none := by simp [muA2_apply]
  simp [h2, h3, holeUsed_muA2_2]

private theorem termB_not_sat_muA2 :
    termSatisfiedB muA2 termB = false := by
  unfold termSatisfiedB termB pairSatB
  have h3 : muA2 (3 : Fin 4) = none := by simp [muA2_apply]
  simp [h3]

private theorem termB_not_fals_muB2 :
    termFalsifiedB muB2 termB = false := by
  unfold termFalsifiedB termB pairFalsB
  have h2 : muB2 (2 : Fin 4) = none := by simp [muB2_apply]
  have h3 : muB2 (3 : Fin 4) = some (2 : Fin 4) := by simp [muB2_apply]
  simp [h2, h3, holeUsed_muB2_3]

private theorem termB_not_sat_muB2 :
    termSatisfiedB muB2 termB = false := by
  unfold termSatisfiedB termB pairSatB
  have h2 : muB2 (2 : Fin 4) = none := by simp [muB2_apply]
  simp [h2]

private theorem termVertices_muA2_termB :
    termVertices muA2 termB =
      [Sum.inl (3 : Fin 4), Sum.inr (2 : Fin 4)] := by
  unfold termVertices termB pairUnresolvedB
  have h2 : muA2 (2 : Fin 4) = some (3 : Fin 4) := by simp [muA2_apply]
  have h3 : muA2 (3 : Fin 4) = none := by simp [muA2_apply]
  -- pair (2,3) is sat (not unresolved); pair (3,2) unresolved
  simp [h2, h3, holeUsed_muA2_2]

private theorem termVertices_muB2_termB :
    termVertices muB2 termB =
      [Sum.inl (2 : Fin 4), Sum.inr (3 : Fin 4)] := by
  unfold termVertices termB pairUnresolvedB
  have h2 : muB2 (2 : Fin 4) = none := by simp [muB2_apply]
  have h3 : muB2 (3 : Fin 4) = some (2 : Fin 4) := by simp [muB2_apply]
  simp [h2, h3, holeUsed_muB2_3]

/-! ## Depth ≥ 3 for rhoA -/

private theorem vwalk_muA2_termB :
    vwalkAux 1 muA2 [] [termB] =
      .pquery (3 : Fin 4) (fun a =>
        if holeUsed muA2 a = true then .leaf false
        else vwalkAux 0 (compose muA2 (singleMatching (3 : Fin 4) a))
          [Sum.inr (2 : Fin 4)] [termB]) := by
  simpa [termVertices_muA2_termB] using
    (vwalk_entry_pigeon (fuel' := 0) muA2 termB [] (3 : Fin 4)
      [Sum.inr (2 : Fin 4)] termB_legal termB_not_fals_muA2
      termB_not_sat_muA2 termVertices_muA2_termB)

private theorem vwalk_muA2_search :
    vwalkAux 1 muA2 [] searchD4mp = vwalkAux 1 muA2 [] [termB] := by
  rw [searchD4mp_eq]
  exact vwalk_skip_falsified 1 muA2 termA [termB] termA_legal termA_fals_muA2

private theorem depth_muA2_search :
    1 ≤ vmdtDepth (vwalkAux 1 muA2 [] searchD4mp) := by
  rw [vwalk_muA2_search, vwalk_muA2_termB, vmdtDepth_pquery]
  exact Nat.le_add_right 1 _

private theorem vwalk_muA2_pending :
    vwalkAux 1 muA2
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp =
      vwalkAux 1 muA2 [] searchD4mp := by
  rw [vblock_skip_covered 1 muA2 (Sum.inl (1 : Fin 4))
    [Sum.inr (0 : Fin 4)] searchD4mp vertexCovered_muA2_inl1]
  exact vblock_skip_covered 1 muA2 (Sum.inr (0 : Fin 4)) [] searchD4mp
    vertexCovered_muA2_inr0

private theorem depth_muA2_pending :
    1 ≤ vmdtDepth
      (vwalkAux 1 muA2
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp) := by
  rw [vwalk_muA2_pending]
  exact depth_muA2_search

private theorem vwalk_muA1_pending :
    vwalkAux 2 muA1
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        searchD4mp =
      .hquery (1 : Fin 4) (fun q =>
        if (muA1 q).isSome = true then .leaf false
        else vwalkAux 1 (compose muA1 (singleMatching q (1 : Fin 4)))
          [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp) := by
  simpa using
    (vblock_query_hole (fuel' := 1) muA1 (1 : Fin 4)
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
      vertexCovered_muA1_inr1)

private theorem depth_muA1_pending :
    2 ≤ vmdtDepth
      (vwalkAux 2 muA1
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        searchD4mp) := by
  rw [vwalk_muA1_pending, vmdtDepth_hquery]
  let child : Fin 4 → VMDTree 4 4 := fun q =>
    if (muA1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose muA1 (singleMatching q (1 : Fin 4)))
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
  have hq : (muA1 (1 : Fin 4)).isSome = false := by simp [muA1_apply]
  have hchild : 1 ≤ vmdtDepth (child 1) := by
    simp only [child, hq]
    simpa [muA2] using depth_muA2_pending
  have hle :
      vmdtDepth (child 1) ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) :=
    Finset.le_sup (f := fun q => vmdtDepth (child q)) (Finset.mem_univ (1 : Fin 4))
  have : 1 ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) :=
    le_trans hchild hle
  simpa [child] using Nat.add_le_add_left this 1

private theorem vwalk_rhoA_search :
    vwalkAux 3 rhoA [] searchD4mp =
      .pquery (0 : Fin 4) (fun a =>
        if holeUsed rhoA a = true then .leaf false
        else vwalkAux 2
          (compose rhoA (singleMatching (0 : Fin 4) a))
          [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          searchD4mp) := by
  rw [searchD4mp_eq]
  simpa [termVertices_rhoA_termA] using
    (vwalk_entry_pigeon (fuel' := 2) rhoA termA [termB] (0 : Fin 4)
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      termA_legal termA_not_fals_rhoA termA_not_sat_rhoA
      termVertices_rhoA_termA)

/-- Canonical depth of `rhoA` / `searchD4mp` is at least 3. -/
theorem rhoA_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA) := by
  unfold canonicalVMDT
  rw [freePigeons_rhoA, vwalk_rhoA_search, vmdtDepth_pquery]
  let child : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed rhoA a = true then .leaf false
    else vwalkAux 2
      (compose rhoA (singleMatching (0 : Fin 4) a))
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      searchD4mp
  have hchild : 2 ≤ vmdtDepth (child 0) := by
    simp only [child, holeUsed_rhoA_0]
    simpa [muA1] using depth_muA1_pending
  have hle :
      vmdtDepth (child 0) ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) :=
    Finset.le_sup (f := fun a => vmdtDepth (child a)) (Finset.mem_univ (0 : Fin 4))
  have : 2 ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) :=
    le_trans hchild hle
  simpa [child] using Nat.add_le_add_left this 1

/-! ## Depth ≥ 3 for rhoB (symmetric) -/

private theorem vwalk_muB2_termB :
    vwalkAux 1 muB2 [] [termB] =
      .pquery (2 : Fin 4) (fun a =>
        if holeUsed muB2 a = true then .leaf false
        else vwalkAux 0 (compose muB2 (singleMatching (2 : Fin 4) a))
          [Sum.inr (3 : Fin 4)] [termB]) := by
  simpa [termVertices_muB2_termB] using
    (vwalk_entry_pigeon (fuel' := 0) muB2 termB [] (2 : Fin 4)
      [Sum.inr (3 : Fin 4)] termB_legal termB_not_fals_muB2
      termB_not_sat_muB2 termVertices_muB2_termB)

private theorem vwalk_muB2_search :
    vwalkAux 1 muB2 [] searchD4mp = vwalkAux 1 muB2 [] [termB] := by
  rw [searchD4mp_eq]
  exact vwalk_skip_falsified 1 muB2 termA [termB] termA_legal termA_fals_muB2

private theorem depth_muB2_search :
    1 ≤ vmdtDepth (vwalkAux 1 muB2 [] searchD4mp) := by
  rw [vwalk_muB2_search, vwalk_muB2_termB, vmdtDepth_pquery]
  exact Nat.le_add_right 1 _

private theorem vwalk_muB2_pending :
    vwalkAux 1 muB2
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp =
      vwalkAux 1 muB2 [] searchD4mp := by
  rw [vblock_skip_covered 1 muB2 (Sum.inl (1 : Fin 4))
    [Sum.inr (0 : Fin 4)] searchD4mp vertexCovered_muB2_inl1]
  exact vblock_skip_covered 1 muB2 (Sum.inr (0 : Fin 4)) [] searchD4mp
    vertexCovered_muB2_inr0

private theorem depth_muB2_pending :
    1 ≤ vmdtDepth
      (vwalkAux 1 muB2
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp) := by
  rw [vwalk_muB2_pending]
  exact depth_muB2_search

private theorem vwalk_muB1_pending :
    vwalkAux 2 muB1
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        searchD4mp =
      .hquery (1 : Fin 4) (fun q =>
        if (muB1 q).isSome = true then .leaf false
        else vwalkAux 1 (compose muB1 (singleMatching q (1 : Fin 4)))
          [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp) := by
  simpa using
    (vblock_query_hole (fuel' := 1) muB1 (1 : Fin 4)
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
      vertexCovered_muB1_inr1)

private theorem depth_muB1_pending :
    2 ≤ vmdtDepth
      (vwalkAux 2 muB1
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        searchD4mp) := by
  rw [vwalk_muB1_pending, vmdtDepth_hquery]
  let child : Fin 4 → VMDTree 4 4 := fun q =>
    if (muB1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose muB1 (singleMatching q (1 : Fin 4)))
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp
  have hq : (muB1 (1 : Fin 4)).isSome = false := by simp [muB1_apply]
  have hchild : 1 ≤ vmdtDepth (child 1) := by
    simp only [child, hq]
    simpa [muB2] using depth_muB2_pending
  have hle :
      vmdtDepth (child 1) ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) :=
    Finset.le_sup (f := fun q => vmdtDepth (child q)) (Finset.mem_univ (1 : Fin 4))
  have : 1 ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) :=
    le_trans hchild hle
  simpa [child] using Nat.add_le_add_left this 1

private theorem vwalk_rhoB_search :
    vwalkAux 3 rhoB [] searchD4mp =
      .pquery (0 : Fin 4) (fun a =>
        if holeUsed rhoB a = true then .leaf false
        else vwalkAux 2
          (compose rhoB (singleMatching (0 : Fin 4) a))
          [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          searchD4mp) := by
  rw [searchD4mp_eq]
  simpa [termVertices_rhoB_termA] using
    (vwalk_entry_pigeon (fuel' := 2) rhoB termA [termB] (0 : Fin 4)
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      termA_legal termA_not_fals_rhoB termA_not_sat_rhoB
      termVertices_rhoB_termA)

/-- Canonical depth of `rhoB` / `searchD4mp` is at least 3. -/
theorem rhoB_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB) := by
  unfold canonicalVMDT
  rw [freePigeons_rhoB, vwalk_rhoB_search, vmdtDepth_pquery]
  let child : Fin 4 → VMDTree 4 4 := fun a =>
    if holeUsed rhoB a = true then .leaf false
    else vwalkAux 2
      (compose rhoB (singleMatching (0 : Fin 4) a))
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      searchD4mp
  have hchild : 2 ≤ vmdtDepth (child 0) := by
    simp only [child, holeUsed_rhoB_0]
    simpa [muB1] using depth_muB1_pending
  have hle :
      vmdtDepth (child 0) ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) :=
    Finset.le_sup (f := fun a => vmdtDepth (child a)) (Finset.mem_univ (0 : Fin 4))
  have : 2 ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) :=
    le_trans hchild hle
  simpa [child] using Nat.add_le_add_left this 1

/-! ## Leftmost live feeds -/

private theorem liveHole_rhoA_s2_0 :
    liveHoleDepthB rhoA (0 : Fin 4) 2
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      searchD4mp 2 (0 : Fin 4) = true := by
  unfold liveHoleDepthB
  rw [if_pos holeUsed_rhoA_0]
  exact decide_eq_true (by simpa [muA1] using depth_muA1_pending)

private theorem leftmostLiveDepthHole_rhoA_s2 :
    leftmostLiveDepthHole? rhoA (0 : Fin 4) 2
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      searchD4mp 2 = some (0 : Fin 4) := by
  unfold leftmostLiveDepthHole?
  rw [finList_4]
  simp [List.find?_cons, liveHole_rhoA_s2_0]

private theorem livePigeon_muA1_s1_1 :
    livePigeonDepthB muA1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1
      (1 : Fin 4) = true := by
  unfold livePigeonDepthB
  have hq : (muA1 (1 : Fin 4)).isSome = false := by simp [muA1_apply]
  rw [if_pos hq]
  exact decide_eq_true (by simpa [muA2] using depth_muA2_pending)

private theorem livePigeon_muA1_s1_0 :
    livePigeonDepthB muA1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1
      (0 : Fin 4) = false := by
  unfold livePigeonDepthB
  have hq : (muA1 (0 : Fin 4)).isSome = true := by simp [muA1_apply]
  simp [hq]

private theorem livePigeon_muA1_s1_2 :
    livePigeonDepthB muA1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1
      (2 : Fin 4) = false := by
  unfold livePigeonDepthB
  have hq : (muA1 (2 : Fin 4)).isSome = true := by simp [muA1_apply]
  simp [hq]

private theorem leftmostLiveDepthPigeon_muA1_s1 :
    leftmostLiveDepthPigeon? muA1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1 =
      some (1 : Fin 4) := by
  unfold leftmostLiveDepthPigeon?
  rw [finList_4]
  simp [List.find?_cons, livePigeon_muA1_s1_0, livePigeon_muA1_s1_1]

private theorem liveHole_muA2_s0_2 :
    liveHoleDepthB muA2 (3 : Fin 4) 0
      [Sum.inr (2 : Fin 4)] [termB] 0 (2 : Fin 4) = true := by
  unfold liveHoleDepthB
  rw [if_pos holeUsed_muA2_2]
  exact decide_eq_true (Nat.zero_le _)

private theorem liveHole_muA2_s0_0 :
    liveHoleDepthB muA2 (3 : Fin 4) 0
      [Sum.inr (2 : Fin 4)] [termB] 0 (0 : Fin 4) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muA2_0]

private theorem liveHole_muA2_s0_1 :
    liveHoleDepthB muA2 (3 : Fin 4) 0
      [Sum.inr (2 : Fin 4)] [termB] 0 (1 : Fin 4) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muA2_1]

private theorem liveHole_muA2_s0_3 :
    liveHoleDepthB muA2 (3 : Fin 4) 0
      [Sum.inr (2 : Fin 4)] [termB] 0 (3 : Fin 4) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muA2_3]

private theorem leftmostLiveDepthHole_muA2_s0 :
    leftmostLiveDepthHole? muA2 (3 : Fin 4) 0
      [Sum.inr (2 : Fin 4)] [termB] 0 = some (2 : Fin 4) := by
  unfold leftmostLiveDepthHole?
  rw [finList_4]
  simp [List.find?_cons, liveHole_muA2_s0_0, liveHole_muA2_s0_1,
    liveHole_muA2_s0_2]

private theorem leftmostLiveFeedAux_muA2_termB :
    leftmostLiveFeedAux 1 muA2 [] [termB] 1 =
      [Sum.inr (2 : Fin 4)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp only [Nat.add_eq, Nat.add_zero]
  simp [termB_legal, termB_not_fals_muA2, termB_not_sat_muA2,
    termVertices_muA2_termB, leftmostLiveDepthHole_muA2_s0,
    leftmostLiveFeedAux]

private theorem leftmostLiveFeedAux_muA2_search :
    leftmostLiveFeedAux 1 muA2 [] searchD4mp 1 =
      [Sum.inr (2 : Fin 4)] := by
  rw [searchD4mp_eq, leftmostLiveFeedAux.eq_def]
  simp [termA_legal, termA_fals_muA2, leftmostLiveFeedAux_muA2_termB]

private theorem leftmostLiveFeedAux_muA2_pending :
    leftmostLiveFeedAux 1 muA2
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1 =
      [Sum.inr (2 : Fin 4)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muA2_inl1]
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muA2_inr0, leftmostLiveFeedAux_muA2_search]

private theorem leftmostLiveFeedAux_muA1_pending :
    leftmostLiveFeedAux 2 muA1
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        searchD4mp 2 =
      [Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muA1_inr1, leftmostLiveDepthPigeon_muA1_s1]
  exact leftmostLiveFeedAux_muA2_pending

private theorem leftmostLiveFeed_rhoA_three :
    leftmostLiveFeed rhoA searchD4mp 3 =
      [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)] := by
  unfold leftmostLiveFeed
  rw [freePigeons_rhoA]
  have hstep :
      leftmostLiveFeedAux 3 rhoA [] searchD4mp 3 =
        Sum.inr (0 : Fin 4) ::
          leftmostLiveFeedAux 2 muA1
            [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
            searchD4mp 2 := by
    rw [searchD4mp_eq, leftmostLiveFeedAux.eq_def]
    simp only [termA_legal, termA_not_fals_rhoA, termA_not_sat_rhoA,
      termVertices_rhoA_termA, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
    have hL :
        leftmostLiveDepthHole? rhoA (0 : Fin 4) 2
          [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          [termA, termB] 2 = some (0 : Fin 4) := by
      simpa [searchD4mp] using leftmostLiveDepthHole_rhoA_s2
    simp [hL, muA1]
  rw [hstep, leftmostLiveFeedAux_muA1_pending]

theorem leftmostLiveDeepFeed_rhoA_three :
    leftmostLiveDeepFeed rhoA searchD4mp 3 =
      [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)] := by
  unfold leftmostLiveDeepFeed
  exact leftmostLiveFeed_rhoA_three

/-! ### rhoB feed -/

private theorem liveHole_rhoB_s2_0 :
    liveHoleDepthB rhoB (0 : Fin 4) 2
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      searchD4mp 2 (0 : Fin 4) = true := by
  unfold liveHoleDepthB
  rw [if_pos holeUsed_rhoB_0]
  exact decide_eq_true (by simpa [muB1] using depth_muB1_pending)

private theorem leftmostLiveDepthHole_rhoB_s2 :
    leftmostLiveDepthHole? rhoB (0 : Fin 4) 2
      [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
      searchD4mp 2 = some (0 : Fin 4) := by
  unfold leftmostLiveDepthHole?
  rw [finList_4]
  simp [List.find?_cons, liveHole_rhoB_s2_0]

private theorem livePigeon_muB1_s1_1 :
    livePigeonDepthB muB1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1
      (1 : Fin 4) = true := by
  unfold livePigeonDepthB
  have hq : (muB1 (1 : Fin 4)).isSome = false := by simp [muB1_apply]
  rw [if_pos hq]
  exact decide_eq_true (by simpa [muB2] using depth_muB2_pending)

private theorem livePigeon_muB1_s1_0 :
    livePigeonDepthB muB1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1
      (0 : Fin 4) = false := by
  unfold livePigeonDepthB
  have hq : (muB1 (0 : Fin 4)).isSome = true := by simp [muB1_apply]
  simp [hq]

private theorem leftmostLiveDepthPigeon_muB1_s1 :
    leftmostLiveDepthPigeon? muB1 (1 : Fin 4) 1
      [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1 =
      some (1 : Fin 4) := by
  unfold leftmostLiveDepthPigeon?
  rw [finList_4]
  simp [List.find?_cons, livePigeon_muB1_s1_0, livePigeon_muB1_s1_1]

private theorem liveHole_muB2_s0_3 :
    liveHoleDepthB muB2 (2 : Fin 4) 0
      [Sum.inr (3 : Fin 4)] [termB] 0 (3 : Fin 4) = true := by
  unfold liveHoleDepthB
  rw [if_pos holeUsed_muB2_3]
  exact decide_eq_true (Nat.zero_le _)

private theorem liveHole_muB2_s0_0 :
    liveHoleDepthB muB2 (2 : Fin 4) 0
      [Sum.inr (3 : Fin 4)] [termB] 0 (0 : Fin 4) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muB2_0]

private theorem liveHole_muB2_s0_1 :
    liveHoleDepthB muB2 (2 : Fin 4) 0
      [Sum.inr (3 : Fin 4)] [termB] 0 (1 : Fin 4) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muB2_1]

private theorem liveHole_muB2_s0_2 :
    liveHoleDepthB muB2 (2 : Fin 4) 0
      [Sum.inr (3 : Fin 4)] [termB] 0 (2 : Fin 4) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muB2_2]

private theorem leftmostLiveDepthHole_muB2_s0 :
    leftmostLiveDepthHole? muB2 (2 : Fin 4) 0
      [Sum.inr (3 : Fin 4)] [termB] 0 = some (3 : Fin 4) := by
  unfold leftmostLiveDepthHole?
  rw [finList_4]
  simp [List.find?_cons, liveHole_muB2_s0_0, liveHole_muB2_s0_1,
    liveHole_muB2_s0_2, liveHole_muB2_s0_3]

private theorem leftmostLiveFeedAux_muB2_termB :
    leftmostLiveFeedAux 1 muB2 [] [termB] 1 =
      [Sum.inr (3 : Fin 4)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp only [Nat.add_eq, Nat.add_zero]
  simp [termB_legal, termB_not_fals_muB2, termB_not_sat_muB2,
    termVertices_muB2_termB, leftmostLiveDepthHole_muB2_s0,
    leftmostLiveFeedAux]

private theorem leftmostLiveFeedAux_muB2_search :
    leftmostLiveFeedAux 1 muB2 [] searchD4mp 1 =
      [Sum.inr (3 : Fin 4)] := by
  rw [searchD4mp_eq, leftmostLiveFeedAux.eq_def]
  simp [termA_legal, termA_fals_muB2, leftmostLiveFeedAux_muB2_termB]

private theorem leftmostLiveFeedAux_muB2_pending :
    leftmostLiveFeedAux 1 muB2
        [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] searchD4mp 1 =
      [Sum.inr (3 : Fin 4)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muB2_inl1]
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muB2_inr0, leftmostLiveFeedAux_muB2_search]

private theorem leftmostLiveFeedAux_muB1_pending :
    leftmostLiveFeedAux 2 muB1
        [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
        searchD4mp 2 =
      [Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muB1_inr1, leftmostLiveDepthPigeon_muB1_s1]
  exact leftmostLiveFeedAux_muB2_pending

private theorem leftmostLiveFeed_rhoB_three :
    leftmostLiveFeed rhoB searchD4mp 3 =
      [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)] := by
  unfold leftmostLiveFeed
  rw [freePigeons_rhoB]
  have hstep :
      leftmostLiveFeedAux 3 rhoB [] searchD4mp 3 =
        Sum.inr (0 : Fin 4) ::
          leftmostLiveFeedAux 2 muB1
            [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
            searchD4mp 2 := by
    rw [searchD4mp_eq, leftmostLiveFeedAux.eq_def]
    simp only [termA_legal, termA_not_fals_rhoB, termA_not_sat_rhoB,
      termVertices_rhoB_termA, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
    have hL :
        leftmostLiveDepthHole? rhoB (0 : Fin 4) 2
          [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          [termA, termB] 2 = some (0 : Fin 4) := by
      simpa [searchD4mp] using leftmostLiveDepthHole_rhoB_s2
    simp [hL, muB1]
  rw [hstep, leftmostLiveFeedAux_muB1_pending]

theorem leftmostLiveDeepFeed_rhoB_three :
    leftmostLiveDeepFeed rhoB searchD4mp 3 =
      [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)] := by
  unfold leftmostLiveDeepFeed
  exact leftmostLiveFeed_rhoB_three

/-! ## Traces / blocks / entered-term length 2 -/

private theorem vtrace_rhoA_three :
    vtrace rhoA searchD4mp
        [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)] =
      [.enter termA rhoA,
        .qstep ⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
        .qstep ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩,
        .enter termB muA2,
        .qstep ⟨Sum.inl (3 : Fin 4), ((3 : Fin 4), (2 : Fin 4))⟩] := by
  unfold vtrace
  rw [freePigeons_rhoA, searchD4mp_eq]
  have htv := termVertices_rhoA_termA
  rw [vevents_entry_pigeon_live (fuel' := 2) rhoA termA [termB]
    (0 : Fin 4)
    [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
    (0 : Fin 4) [Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)]
    termA_legal termA_not_fals_rhoA termA_not_sat_rhoA htv holeUsed_rhoA_0]
  change
      _ :: _ ::
        vevents 2 muA1
          [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          [termA, termB] [Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)] =
        _
  rw [vevents_block_hole_live (fuel' := 1) muA1 (1 : Fin 4)
    [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] [termA, termB]
    (1 : Fin 4) [Sum.inr (2 : Fin 4)] vertexCovered_muA1_inr1
    (by simp [muA1_apply])]
  change
      _ :: _ :: _ ::
        vevents 1 muA2 [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          [termA, termB] [Sum.inr (2 : Fin 4)] =
        _
  rw [vevents_block_skip_covered 1 muA2 (Sum.inl (1 : Fin 4))
    [Sum.inr (0 : Fin 4)] [termA, termB] [Sum.inr (2 : Fin 4)]
    vertexCovered_muA2_inl1]
  rw [vevents_block_skip_covered 1 muA2 (Sum.inr (0 : Fin 4)) []
    [termA, termB] [Sum.inr (2 : Fin 4)] vertexCovered_muA2_inr0]
  rw [vevents_skip_falsified 1 muA2 termA [termB] [Sum.inr (2 : Fin 4)]
    termA_legal termA_fals_muA2]
  rw [vevents_entry_pigeon_live (fuel' := 0) muA2 termB []
    (3 : Fin 4) [Sum.inr (2 : Fin 4)] (2 : Fin 4) []
    termB_legal termB_not_fals_muA2 termB_not_sat_muA2
    termVertices_muA2_termB holeUsed_muA2_2]
  have hcov :
      vertexCoveredB
        (compose muA2 (singleMatching (3 : Fin 4) 2))
        (Sum.inr (2 : Fin 4)) = true := by
    simp [vertexCoveredB, holeUsed, finList_4, compose, singleMatching,
      muA2_apply]
  rw [vevents_block_skip_covered 0 _ _ _ _ _ hcov]
  have hsat :
      termSatisfiedB
        (compose muA2 (singleMatching (3 : Fin 4) 2)) termB = true := by
    unfold termSatisfiedB termB pairSatB
    simp [compose, singleMatching, muA2_apply]
  have hfals' :
      termFalsifiedB
        (compose muA2 (singleMatching (3 : Fin 4) 2)) termB = false := by
    unfold termFalsifiedB termB pairFalsB
    simp [compose, singleMatching, muA2_apply, holeUsed, finList_4]
  rw [vevents_stop_satisfied 0 _ _ _ _ termB_legal hfals' hsat]

private theorem vtrace_rhoB_three :
    vtrace rhoB searchD4mp
        [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)] =
      [.enter termA rhoB,
        .qstep ⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
        .qstep ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩,
        .enter termB muB2,
        .qstep ⟨Sum.inl (2 : Fin 4), ((2 : Fin 4), (3 : Fin 4))⟩] := by
  unfold vtrace
  rw [freePigeons_rhoB, searchD4mp_eq]
  have htv := termVertices_rhoB_termA
  rw [vevents_entry_pigeon_live (fuel' := 2) rhoB termA [termB]
    (0 : Fin 4)
    [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
    (0 : Fin 4) [Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)]
    termA_legal termA_not_fals_rhoB termA_not_sat_rhoB htv holeUsed_rhoB_0]
  change
      _ :: _ ::
        vevents 2 muB1
          [Sum.inr (1 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          [termA, termB] [Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)] =
        _
  rw [vevents_block_hole_live (fuel' := 1) muB1 (1 : Fin 4)
    [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)] [termA, termB]
    (1 : Fin 4) [Sum.inr (3 : Fin 4)] vertexCovered_muB1_inr1
    (by simp [muB1_apply])]
  change
      _ :: _ :: _ ::
        vevents 1 muB2 [Sum.inl (1 : Fin 4), Sum.inr (0 : Fin 4)]
          [termA, termB] [Sum.inr (3 : Fin 4)] =
        _
  rw [vevents_block_skip_covered 1 muB2 (Sum.inl (1 : Fin 4))
    [Sum.inr (0 : Fin 4)] [termA, termB] [Sum.inr (3 : Fin 4)]
    vertexCovered_muB2_inl1]
  rw [vevents_block_skip_covered 1 muB2 (Sum.inr (0 : Fin 4)) []
    [termA, termB] [Sum.inr (3 : Fin 4)] vertexCovered_muB2_inr0]
  rw [vevents_skip_falsified 1 muB2 termA [termB] [Sum.inr (3 : Fin 4)]
    termA_legal termA_fals_muB2]
  rw [vevents_entry_pigeon_live (fuel' := 0) muB2 termB []
    (2 : Fin 4) [Sum.inr (3 : Fin 4)] (3 : Fin 4) []
    termB_legal termB_not_fals_muB2 termB_not_sat_muB2
    termVertices_muB2_termB holeUsed_muB2_3]
  have hcov :
      vertexCoveredB
        (compose muB2 (singleMatching (2 : Fin 4) 3))
        (Sum.inr (3 : Fin 4)) = true := by
    simp [vertexCoveredB, holeUsed, finList_4, compose, singleMatching,
      muB2_apply]
  rw [vevents_block_skip_covered 0 _ _ _ _ _ hcov]
  have hsat :
      termSatisfiedB
        (compose muB2 (singleMatching (2 : Fin 4) 3)) termB = true := by
    unfold termSatisfiedB termB pairSatB
    simp [compose, singleMatching, muB2_apply]
  have hfals' :
      termFalsifiedB
        (compose muB2 (singleMatching (2 : Fin 4) 3)) termB = false := by
    unfold termFalsifiedB termB pairFalsB
    simp [compose, singleMatching, muB2_apply, holeUsed, finList_4]
  rw [vevents_stop_satisfied 0 _ _ _ _ termB_legal hfals' hsat]

private theorem blocksOf_rhoA_three :
    blocksOf
        (vtrace rhoA searchD4mp
          [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (2 : Fin 4)]) =
      [⟨termA, rhoA,
          [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
            ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩,
        ⟨termB, muA2,
          [⟨Sum.inl (3 : Fin 4), ((3 : Fin 4), (2 : Fin 4))⟩]⟩] := by
  rw [vtrace_rhoA_three]
  simp [blocksOf, stepsPrefix, afterSteps]

private theorem blocksOf_rhoB_three :
    blocksOf
        (vtrace rhoB searchD4mp
          [Sum.inr (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inr (3 : Fin 4)]) =
      [⟨termA, rhoB,
          [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
            ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩,
        ⟨termB, muB2,
          [⟨Sum.inl (2 : Fin 4), ((2 : Fin 4), (3 : Fin 4))⟩]⟩] := by
  rw [vtrace_rhoB_three]
  simp [blocksOf, stepsPrefix, afterSteps]

private theorem enteredTermsOf_rhoA_three :
    enteredTermsOf rhoA searchD4mp 3 = [termA, termB] := by
  simp only [enteredTermsOf, leftmostLiveDeepFeed_rhoA_three]
  rw [blocksOf_rhoA_three]
  rfl

private theorem enteredTermsOf_rhoB_three :
    enteredTermsOf rhoB searchD4mp 3 = [termA, termB] := by
  simp only [enteredTermsOf, leftmostLiveDeepFeed_rhoB_three]
  rw [blocksOf_rhoB_three]
  rfl

theorem enteredTermsOf_rhoA_three_length :
    (enteredTermsOf rhoA searchD4mp 3).length = 2 := by
  rw [enteredTermsOf_rhoA_three]; decide

theorem enteredTermsOf_rhoB_three_length :
    (enteredTermsOf rhoB searchD4mp 3).length = 2 := by
  rw [enteredTermsOf_rhoB_three]; decide

/-! ## Path exits differ -/

private theorem firstBlockPathExitMatching_rhoA_three :
    firstBlockPathExitMatching rhoA searchD4mp 3 = muA2 := by
  have hblocks :
      blocksOf (vtrace rhoA searchD4mp
        (leftmostLiveDeepFeed rhoA searchD4mp 3)) =
        [⟨termA, rhoA,
            [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
              ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩,
          ⟨termB, muA2,
            [⟨Sum.inl (3 : Fin 4), ((3 : Fin 4), (2 : Fin 4))⟩]⟩] := by
    simpa [leftmostLiveDeepFeed_rhoA_three] using blocksOf_rhoA_three
  rw [firstBlockPathExitMatching_cons rhoA searchD4mp 3 _ _
    (by simpa using hblocks)]
  funext i
  simp only [muA2_apply, pairsToMatching, compose, singleMatching, rhoA,
    emptyMatching]
  fin_cases i <;> simp

private theorem firstBlockPathExitMatching_rhoB_three :
    firstBlockPathExitMatching rhoB searchD4mp 3 = muB2 := by
  have hblocks :
      blocksOf (vtrace rhoB searchD4mp
        (leftmostLiveDeepFeed rhoB searchD4mp 3)) =
        [⟨termA, rhoB,
            [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
              ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩,
          ⟨termB, muB2,
            [⟨Sum.inl (2 : Fin 4), ((2 : Fin 4), (3 : Fin 4))⟩]⟩] := by
    simpa [leftmostLiveDeepFeed_rhoB_three] using blocksOf_rhoB_three
  rw [firstBlockPathExitMatching_cons rhoB searchD4mp 3 _ _
    (by simpa using hblocks)]
  funext i
  simp only [muB2_apply, pairsToMatching, compose, singleMatching, rhoB,
    emptyMatching]
  fin_cases i <;> simp

theorem path_exits_rhoA_ne_rhoB :
    firstBlockPathExitMatching rhoA searchD4mp 3 ≠
      firstBlockPathExitMatching rhoB searchD4mp 3 := by
  rw [firstBlockPathExitMatching_rhoA_three,
    firstBlockPathExitMatching_rhoB_three]
  intro h
  have h2 : muA2 (2 : Fin 4) = muB2 (2 : Fin 4) := by rw [h]
  simp [muA2_apply, muB2_apply] at h2

/-! ## Multi-preimage length-2 package -/

/-- **S2204 multi-preimage length-2 witnesses.**  Two distinct free-count-3
depth-eligible bases on Fin 4 / `searchD4mp` / `t = 3` with entered-term
length 2 and distinct first-block path exits. -/
theorem exists_multi_preimage_length_two :
    ∃ (rho₁ rho₂ : MatchingMap 4 4),
      IsMatching rho₁ ∧ IsMatching rho₂ ∧
        rho₁ ≠ rho₂ ∧
        (freePigeons rho₁).card = 3 ∧
        (freePigeons rho₂).card = 3 ∧
        3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho₁) ∧
        3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho₂) ∧
        (enteredTermsOf rho₁ searchD4mp 3).length = 2 ∧
        (enteredTermsOf rho₂ searchD4mp 3).length = 2 ∧
        firstBlockPathExitMatching rho₁ searchD4mp 3 ≠
          firstBlockPathExitMatching rho₂ searchD4mp 3 :=
  ⟨rhoA, rhoB, isMatching_rhoA, isMatching_rhoB, rhoA_ne_rhoB,
    freePigeons_rhoA, freePigeons_rhoB, rhoA_depth_ge_three,
    rhoB_depth_ge_three, enteredTermsOf_rhoA_three_length,
    enteredTermsOf_rhoB_three_length, path_exits_rhoA_ne_rhoB⟩

/-! ## Named encode codes differ (no bank collision on this fiber) -/

private theorem blocksOf_rhoA_deep :
    blocksOf (vtrace rhoA searchD4mp (leftmostLiveDeepFeed rhoA searchD4mp 3)) =
      [⟨termA, rhoA,
          [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
            ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩,
        ⟨termB, muA2,
          [⟨Sum.inl (3 : Fin 4), ((3 : Fin 4), (2 : Fin 4))⟩]⟩] := by
  simpa [leftmostLiveDeepFeed_rhoA_three] using blocksOf_rhoA_three

private theorem blocksOf_rhoB_deep :
    blocksOf (vtrace rhoB searchD4mp (leftmostLiveDeepFeed rhoB searchD4mp 3)) =
      [⟨termA, rhoB,
          [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
            ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩,
        ⟨termB, muB2,
          [⟨Sum.inl (2 : Fin 4), ((2 : Fin 4), (3 : Fin 4))⟩]⟩] := by
  simpa [leftmostLiveDeepFeed_rhoB_three] using blocksOf_rhoB_three

private theorem sigmaFull_termA_rhoA :
    sigmaFull
        (⟨termA, rhoA,
            [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
              ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩ :
          VBlock 4 4) =
      [((0 : Fin 4), (1 : Fin 4)), ((1 : Fin 4), (0 : Fin 4))] := by
  unfold sigmaFull termA pairUnresolvedB rhoA singleMatching
  simp [holeUsed, finList_4]

private theorem sigmaFull_termA_rhoB :
    sigmaFull
        (⟨termA, rhoB,
            [⟨Sum.inl (0 : Fin 4), ((0 : Fin 4), (0 : Fin 4))⟩,
              ⟨Sum.inr (1 : Fin 4), ((1 : Fin 4), (1 : Fin 4))⟩]⟩ :
          VBlock 4 4) =
      [((0 : Fin 4), (1 : Fin 4)), ((1 : Fin 4), (0 : Fin 4))] := by
  unfold sigmaFull termA pairUnresolvedB rhoB singleMatching
  simp [holeUsed, finList_4]

private theorem sigmaFull_termB_muA2 :
    sigmaFull
        (⟨termB, muA2,
            [⟨Sum.inl (3 : Fin 4), ((3 : Fin 4), (2 : Fin 4))⟩]⟩ :
          VBlock 4 4) =
      [((3 : Fin 4), (2 : Fin 4))] := by
  unfold sigmaFull termB pairUnresolvedB
  simp [muA2_apply, holeUsed, finList_4]

private theorem sigmaFull_termB_muB2 :
    sigmaFull
        (⟨termB, muB2,
            [⟨Sum.inl (2 : Fin 4), ((2 : Fin 4), (3 : Fin 4))⟩]⟩ :
          VBlock 4 4) =
      [((2 : Fin 4), (3 : Fin 4))] := by
  unfold sigmaFull termB pairUnresolvedB
  simp [muB2_apply, holeUsed, finList_4]

private theorem pairQueried_inl3_32 :
    pairQueriedB (p := 4) (h := 4)
      ([Sum.inl (3 : Fin 4)] : List (Vertex 4 4))
      ((3 : Fin 4), (2 : Fin 4)) = true := by
  unfold pairQueriedB
  decide

private theorem pairQueried_inl2_23 :
    pairQueriedB (p := 4) (h := 4)
      ([Sum.inl (2 : Fin 4)] : List (Vertex 4 4))
      ((2 : Fin 4), (3 : Fin 4)) = true := by
  unfold pairQueriedB
  decide

private theorem sigmaTrunc_termB_muA2 :
    sigmaTrunc
        (⟨termB, muA2,
            [⟨Sum.inl (3 : Fin 4), ((3 : Fin 4), (2 : Fin 4))⟩]⟩ :
          VBlock 4 4) =
      [((3 : Fin 4), (2 : Fin 4))] := by
  unfold sigmaTrunc
  rw [sigmaFull_termB_muA2]
  simp only [blockQueried, List.map_cons, List.map_nil]
  have hp := pairQueried_inl3_32
  simp [List.filter_cons, List.filter_nil, hp]

private theorem sigmaTrunc_termB_muB2 :
    sigmaTrunc
        (⟨termB, muB2,
            [⟨Sum.inl (2 : Fin 4), ((2 : Fin 4), (3 : Fin 4))⟩]⟩ :
          VBlock 4 4) =
      [((2 : Fin 4), (3 : Fin 4))] := by
  unfold sigmaTrunc
  rw [sigmaFull_termB_muB2]
  simp only [blockQueried, List.map_cons, List.map_nil]
  have hp := pairQueried_inl2_23
  simp [List.filter_cons, List.filter_nil, hp]

private theorem termIdx_termA_01 :
    termIdx termA ((0 : Fin 4), (1 : Fin 4)) = 0 := by
  unfold termIdx termA; rfl

private theorem termIdx_termA_10 :
    termIdx termA ((1 : Fin 4), (0 : Fin 4)) = 1 := by
  unfold termIdx termA
  have hne : ¬ ((0 : Fin 4), (1 : Fin 4)) = ((1 : Fin 4), (0 : Fin 4)) := by
    decide
  simp only [hne, ↓reduceIte]
  rfl

private theorem termIdx_termB_23 :
    termIdx termB ((2 : Fin 4), (3 : Fin 4)) = 0 := by
  unfold termIdx termB; rfl

private theorem termIdx_termB_32 :
    termIdx termB ((3 : Fin 4), (2 : Fin 4)) = 1 := by
  unfold termIdx termB
  have hne : ¬ ((2 : Fin 4), (3 : Fin 4)) = ((3 : Fin 4), (2 : Fin 4)) := by
    decide
  simp only [hne, ↓reduceIte]
  rfl

private theorem termMarkPos_termA_01 :
    termMarkPos (w := 2) termA ((0 : Fin 4), (1 : Fin 4)) =
      some (⟨0, by decide⟩ : Fin 2) := by
  unfold termMarkPos
  have hmem : ((0 : Fin 4), (1 : Fin 4)) ∈ termA := by simp [termA]
  simp only [hmem, ↓reduceDIte, termIdx_termA_01]
  rfl

private theorem termMarkPos_termA_10 :
    termMarkPos (w := 2) termA ((1 : Fin 4), (0 : Fin 4)) =
      some (⟨1, by decide⟩ : Fin 2) := by
  unfold termMarkPos
  have hmem : ((1 : Fin 4), (0 : Fin 4)) ∈ termA := by simp [termA]
  simp only [hmem, ↓reduceDIte, termIdx_termA_10]
  rfl

private theorem termMarkPos_termB_32 :
    termMarkPos (w := 2) termB ((3 : Fin 4), (2 : Fin 4)) =
      some (⟨1, by decide⟩ : Fin 2) := by
  unfold termMarkPos
  have hmem : ((3 : Fin 4), (2 : Fin 4)) ∈ termB := by simp [termB]
  simp only [hmem, ↓reduceDIte, termIdx_termB_32]
  rfl

private theorem termMarkPos_termB_23 :
    termMarkPos (w := 2) termB ((2 : Fin 4), (3 : Fin 4)) =
      some (⟨0, by decide⟩ : Fin 2) := by
  unfold termMarkPos
  have hmem : ((2 : Fin 4), (3 : Fin 4)) ∈ termB := by simp [termB]
  simp only [hmem, ↓reduceDIte, termIdx_termB_23]
  rfl

private theorem sigmaMarks_termA_both :
    sigmaMarks (w := 2) termA
        [((0 : Fin 4), (1 : Fin 4)), ((1 : Fin 4), (0 : Fin 4))] =
      ({(0 : Fin 2), 1} : Finset (Fin 2)) := by
  unfold sigmaMarks
  rw [List.filterMap_cons, termMarkPos_termA_01, List.filterMap_cons,
    termMarkPos_termA_10, List.filterMap_nil]
  decide

private theorem sigmaMarks_termB_pos1 :
    sigmaMarks (w := 2) termB [((3 : Fin 4), (2 : Fin 4))] =
      ({(1 : Fin 2)} : Finset (Fin 2)) := by
  unfold sigmaMarks
  rw [List.filterMap_cons, termMarkPos_termB_32, List.filterMap_nil]
  rfl

private theorem sigmaMarks_termB_pos0 :
    sigmaMarks (w := 2) termB [((2 : Fin 4), (3 : Fin 4))] =
      ({(0 : Fin 2)} : Finset (Fin 2)) := by
  unfold sigmaMarks
  rw [List.filterMap_cons, termMarkPos_termB_23, List.filterMap_nil]
  rfl

private theorem traceBetaDeep_rhoA_three :
    traceBetaDeep (w := 2) rhoA searchD4mp 3 =
      [({(0 : Fin 2), 1} : Finset (Fin 2)),
        ({(1 : Fin 2)} : Finset (Fin 2))] := by
  unfold traceBetaDeep traceBeta
  rw [blocksOf_rhoA_deep]
  simp only [blockSigmasBeta, sigmaFull_termA_rhoA, sigmaTrunc_termB_muA2,
    sigmaMarks_termA_both, sigmaMarks_termB_pos1]

private theorem traceBetaDeep_rhoB_three :
    traceBetaDeep (w := 2) rhoB searchD4mp 3 =
      [({(0 : Fin 2), 1} : Finset (Fin 2)),
        ({(0 : Fin 2)} : Finset (Fin 2))] := by
  unfold traceBetaDeep traceBeta
  rw [blocksOf_rhoB_deep]
  simp only [blockSigmasBeta, sigmaFull_termA_rhoB, sigmaTrunc_termB_muB2,
    sigmaMarks_termA_both, sigmaMarks_termB_pos0]

/-- The named multi-preimage pair is already separated by the `G2`
β-mark trace. -/
theorem encodeMatch_G2_rhoA_ne_rhoB
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)) :
    (encodeMatch rfl rhoA searchD4mp isMatching_rhoA freePigeons_rhoA ht₁
      searchD4mp_width).G2 ≠
    (encodeMatch rfl rhoB searchD4mp isMatching_rhoB freePigeons_rhoB ht₂
      searchD4mp_width).G2 := by
  intro hG2
  change traceBetaDeep (w := 2) rhoA searchD4mp 3 =
    traceBetaDeep (w := 2) rhoB searchD4mp 3 at hG2
  rw [traceBetaDeep_rhoA_three, traceBetaDeep_rhoB_three] at hG2
  have hne :
      ({(1 : Fin 2)} : Finset (Fin 2)) ≠ ({(0 : Fin 2)} : Finset (Fin 2)) := by
    intro h
    have : (1 : Fin 2) ∈ ({(0 : Fin 2)} : Finset (Fin 2)) := by
      rw [← h]; exact Finset.mem_singleton_self _
    exact absurd this (by decide)
  exact hne (List.cons.inj (List.cons.inj hG2).2).1

/-- Named multi-preimage pair has unequal `encodeMatch` codes (distinct
second-block `G2` β-marks). No bank collision on this fiber. -/
theorem encodeMatch_rhoA_ne_rhoB
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)) :
    encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoA searchD4mp isMatching_rhoA freePigeons_rhoA ht₁ searchD4mp_width ≠
      encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoB searchD4mp isMatching_rhoB freePigeons_rhoB ht₂ searchD4mp_width := by
  intro hcode
  exact encodeMatch_G2_rhoA_ne_rhoB ht₁ ht₂ (congrArg MatchEncode.G2 hcode)

/-! ## Collision predicate on the named multi-preimage pair -/

/-- Path-exit collision predicate (Fin 4 / `searchD4mp`). -/
def isPathExitCollision4 {ell t : Nat}
    (rho₁ rho₂ : MatchingMap 4 4)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD4mp rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD4mp rho₂)) : Prop :=
  encodeMatch (p := 4) (h := 4) (w := 2) (t := t) (ell := ell) rfl
      rho₁ searchD4mp hrho₁ hell₁ ht₁ searchD4mp_width =
    encodeMatch (p := 4) (h := 4) (w := 2) (t := t) (ell := ell) rfl
      rho₂ searchD4mp hrho₂ hell₂ ht₂ searchD4mp_width ∧
    firstBlockPathExitMatching rho₁ searchD4mp t ≠
      firstBlockPathExitMatching rho₂ searchD4mp t

/-- Named multi-preimage pair is **not** a path-exit encode collision
(codes differ, exits differ). -/
theorem no_path_exit_collision_rhoA_rhoB
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)) :
    ¬ isPathExitCollision4 (t := 3) (ell := 3)
      rhoA rhoB isMatching_rhoA isMatching_rhoB
      freePigeons_rhoA freePigeons_rhoB ht₁ ht₂ := by
  intro ⟨hcode, _⟩
  exact encodeMatch_rhoA_ne_rhoB ht₁ ht₂ hcode

/-! ## Summary -/

/-- **S2204 multi-preimage length-2 path-exit package summary.**

* Board `Fin 4`, dual width-2 DNF, `t = 3`, `ell = 3` (`ell < p`).
* Named witnesses `rhoA`, `rhoB`: distinct, free-count 3, depth ≥ 3,
  entered-term length 2, distinct path exits.
* Named equal-code fiber: **no** — codes differ (`encodeMatch_rhoA_ne_rhoB`).
* No bank stop-loss on this fiber.
* `EncodeMatchLengthTwoExitEqResidual` **not** discharged by unique-preimage
  (multi free-count-3 domain); packet-only walked-pair recovery remains open.
-/
theorem multi_preimage_length_two_summary :
    (∃ term ∈ searchD4mp, 2 ≤ term.length) ∧
      (∃ (rho₁ rho₂ : MatchingMap 4 4),
        IsMatching rho₁ ∧ IsMatching rho₂ ∧
          rho₁ ≠ rho₂ ∧
          (freePigeons rho₁).card = 3 ∧
          (freePigeons rho₂).card = 3 ∧
          3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho₁) ∧
          3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho₂) ∧
          (enteredTermsOf rho₁ searchD4mp 3).length = 2 ∧
          (enteredTermsOf rho₂ searchD4mp 3).length = 2 ∧
          firstBlockPathExitMatching rho₁ searchD4mp 3 ≠
            firstBlockPathExitMatching rho₂ searchD4mp 3) ∧
      (∀ (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
        (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)),
        encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
            rhoA searchD4mp isMatching_rhoA freePigeons_rhoA ht₁
            searchD4mp_width ≠
          encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
            rhoB searchD4mp isMatching_rhoB freePigeons_rhoB ht₂
            searchD4mp_width) ∧
      (∀ (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
        (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)),
        ¬ isPathExitCollision4 (t := 3) (ell := 3)
          rhoA rhoB isMatching_rhoA isMatching_rhoB
          freePigeons_rhoA freePigeons_rhoB ht₁ ht₂) :=
  ⟨searchD4mp_has_width_ge_two,
    exists_multi_preimage_length_two,
    fun ht₁ ht₂ => encodeMatch_rhoA_ne_rhoB ht₁ ht₂,
    fun ht₁ ht₂ => no_path_exit_collision_rhoA_rhoB ht₁ ht₂⟩

end PHPMatchingEncodeMultiPreimage
end PvNP
