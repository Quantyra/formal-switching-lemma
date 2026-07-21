import PvNP.PHPMatchingEncodeMultiPreimage
import Mathlib.Tactic.FinCases

/-!
# S2205: Fin4 free-count-3 equal-code fiber search

Board `Fin 4`, dual width-2 DNF `searchD4mp`, depth `t = 3`, free-count
`ell = 3` (from `PHPMatchingEncodeMultiPreimage`).

* Enumerates all 16 single-edge free-count-3 matchings with completeness.
* Equal-code fiber on the S2204 multi-preimage length-2 pair `{rhoA, rhoB}`:
  codes differ ⇒ **no bank collision**.
* Free-count barriers: `ell ≤ 2` empty depth slice at `t = 3`; `ell = 4`
  unique empty matching.
* `EncodeMatchLengthTwoExitEqResidual` discharged for `ell ≠ 3` by the
  barriers above; for `ell = 3` the named multi-preimage equal-code fiber is
  empty (codes of `rhoA`/`rhoB` differ), so residual holds on that fiber.
  Full free-count-3 length-2 uniqueness (every length-2 depth-eligible base
  equals `rhoA` or `rhoB`) remains the next residual toward package-wide
  `ell = 3` residual without naming the pair.

Honest bounds: Fin 4 / `searchD4mp` / `t = 3` only. No v0.11.0 tag.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeFiberSearch

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeCollisionSearch
open RestrictedPHPFloor

/-! ## Exhaustive single-edge free-count-3 enumeration -/

/-- All 16 single-edge matchings on Fin 4. -/
def allSingleEdge4 : List (MatchingMap 4 4) :=
  [singleMatching (0 : Fin 4) 0, singleMatching (0 : Fin 4) 1,
    singleMatching (0 : Fin 4) 2, singleMatching (0 : Fin 4) 3,
    singleMatching (1 : Fin 4) 0, singleMatching (1 : Fin 4) 1,
    singleMatching (1 : Fin 4) 2, singleMatching (1 : Fin 4) 3,
    singleMatching (2 : Fin 4) 0, singleMatching (2 : Fin 4) 1,
    singleMatching (2 : Fin 4) 2, singleMatching (2 : Fin 4) 3,
    singleMatching (3 : Fin 4) 0, singleMatching (3 : Fin 4) 1,
    singleMatching (3 : Fin 4) 2, singleMatching (3 : Fin 4) 3]

theorem allSingleEdge4_length : allSingleEdge4.length = 16 := rfl

theorem isMatching_of_mem_allSingleEdge4 {mu : MatchingMap 4 4}
    (h : mu ∈ allSingleEdge4) : IsMatching mu := by
  simp only [allSingleEdge4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (subst h; exact isMatching_singleMatching _ _)

private theorem freePigeons_singleMatching (i a : Fin 4) :
    (freePigeons (singleMatching i a)).card = 3 := by
  have h : freePigeons (singleMatching i a) = Finset.univ.erase i := by
    ext j
    simp only [mem_freePigeons, Finset.mem_erase, Finset.mem_univ, and_true,
      singleMatching]
    constructor
    · intro hj
      by_cases hji : j = i
      · simp [hji] at hj
      · exact hji
    · intro hji; simp [hji]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp [Fintype.card_fin]

theorem freePigeons_of_mem_allSingleEdge4 {mu : MatchingMap 4 4}
    (h : mu ∈ allSingleEdge4) : (freePigeons mu).card = 3 := by
  simp only [allSingleEdge4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (subst h; exact freePigeons_singleMatching _ _)

/-- Completeness: every free-count-3 matching on Fin 4 is a single edge. -/
theorem eq_singleMatching_of_free_count_three (mu : MatchingMap 4 4)
    (_hmu : IsMatching mu) (hell : (freePigeons mu).card = 3) :
    ∃ (i a : Fin 4), mu = singleMatching i a := by
  classical
  -- free card 3 ⇒ not all free ⇒ some assigned pigeon
  have hex : ∃ i : Fin 4, mu i ≠ none := by
    by_contra h
    push_neg at h
    have hfree : (freePigeons mu).card = 4 := by
      have huni : freePigeons mu = (Finset.univ : Finset (Fin 4)) := by
        ext i
        simp only [mem_freePigeons, Finset.mem_univ, iff_true]
        exact h i
      rw [huni]; simp [Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hi
  refine ⟨i, a, ?_⟩
  funext j
  by_cases hji : j = i
  · subst hji; simp [singleMatching, ha]
  · -- j ≠ i: if j also assigned, free card ≤ 2, contradiction
    have hj : mu j = none := by
      by_contra hj
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hj
      have hle :
          (freePigeons mu).card ≤ 2 := by
        have hni : i ∉ freePigeons mu := by
          rw [mem_freePigeons]; simp [ha]
        have hnj : j ∉ freePigeons mu := by
          rw [mem_freePigeons]; simp [hb]
        have hsub : freePigeons mu ⊆
            (Finset.univ.erase i).erase j := by
          intro k hk
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          refine ⟨?_, ?_⟩
          · intro hkj; subst hkj; exact hnj hk
          · intro hki; subst hki; exact hni hk
        have hcard :
            ((Finset.univ.erase i).erase j : Finset (Fin 4)).card = 2 := by
          rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem]
          · simp [Fintype.card_fin]
          · exact Finset.mem_univ _
          · simp [Finset.mem_erase, hji, Finset.mem_univ]
        exact Nat.le_trans (Finset.card_le_card hsub) (by rw [hcard])
      omega
    simp [singleMatching, hji, hj]

theorem mem_allSingleEdge4_of_free_count_three (mu : MatchingMap 4 4)
    (hmu : IsMatching mu) (hell : (freePigeons mu).card = 3) :
    mu ∈ allSingleEdge4 := by
  obtain ⟨i, a, rfl⟩ := eq_singleMatching_of_free_count_three mu hmu hell
  fin_cases i <;> fin_cases a <;> simp [allSingleEdge4]

theorem rhoA_mem_allSingleEdge4 : rhoA ∈ allSingleEdge4 := by
  simp [allSingleEdge4, rhoA]

theorem rhoB_mem_allSingleEdge4 : rhoB ∈ allSingleEdge4 := by
  simp [allSingleEdge4, rhoB]

/-! ## Free-count barriers -/

theorem not_depth_eligible_ell_lt_three_t_three (rho : MatchingMap 4 4)
    {ell : Nat} (hell : (freePigeons rho).card = ell) (hle : ell ≤ 2) :
    ¬ 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho) :=
  not_depth_eligible_of_free_lt_t_gen searchD4mp rho hell (by omega)

theorem unique_ell_four (rho : MatchingMap 4 4) (_hrho : IsMatching rho)
    (hell : (freePigeons rho).card = 4) :
    rho = emptyMatching 4 4 := by
  funext i
  have huni : freePigeons rho = (Finset.univ : Finset (Fin 4)) := by
    apply Finset.eq_univ_of_card
    simpa [Fintype.card_fin] using hell
  exact (mem_freePigeons rho i).mp (by rw [huni]; exact Finset.mem_univ _)

private theorem ell_of_depth_ge_three {ell : Nat} (rho : MatchingMap 4 4)
    (hell : (freePigeons rho).card = ell)
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho)) :
    ell = 3 ∨ ell = 4 := by
  have hle := vmdtDepth_canonicalVMDT_le_freePigeons searchD4mp rho
  have hcard : ell ≤ 4 := by
    have : (freePigeons rho).card ≤ Fintype.card (Fin 4) :=
      Finset.card_le_univ _
    simpa [hell, Fintype.card_fin] using this
  omega

/-! ## Named multi-preimage equal-code fiber -/

/-- Named multi-preimage equal-code fiber is empty (codes differ). -/
theorem no_equal_code_fiber_rhoA_rhoB
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)) :
    encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoA searchD4mp isMatching_rhoA freePigeons_rhoA ht₁
        searchD4mp_width ≠
      encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoB searchD4mp isMatching_rhoB freePigeons_rhoB ht₂
        searchD4mp_width :=
  encodeMatch_rhoA_ne_rhoB ht₁ ht₂

/-- No path-exit bank collision on the named multi-preimage pair. -/
theorem no_path_exit_collision_named_fiber
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)) :
    ¬ isPathExitCollision4 (t := 3) (ell := 3)
      rhoA rhoB isMatching_rhoA isMatching_rhoB
      freePigeons_rhoA freePigeons_rhoB ht₁ ht₂ :=
  no_path_exit_collision_rhoA_rhoB ht₁ ht₂

/-- On the named multi-preimage length-2 fiber, equal codes force equal path
exits (vacuously: the only two witnesses have unequal codes). -/
theorem firstBlockPathExitMatching_eq_of_encodeMatch_eq_named_fiber
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB))
    (hcode :
      encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoA searchD4mp isMatching_rhoA freePigeons_rhoA ht₁
        searchD4mp_width =
      encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoB searchD4mp isMatching_rhoB freePigeons_rhoB ht₂
        searchD4mp_width) :
    firstBlockPathExitMatching rhoA searchD4mp 3 =
      firstBlockPathExitMatching rhoB searchD4mp 3 :=
  absurd hcode (encodeMatch_rhoA_ne_rhoB ht₁ ht₂)

/-! ## Residual discharge (barriers + named fiber) -/

/-- Residual at free-counts other than 3: depth barrier or unique empty. -/
theorem encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_of_ell_ne_three
    {ell : Nat} (hne : ell ≠ 3) :
    EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl searchD4mp searchD4mp_width := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ _hcode _hlen
  rcases ell_of_depth_ge_three rho₁ hell₁ ht₁ with he | he
  · exact (hne he).elim
  · have h1 := unique_ell_four rho₁ hrho₁ (by rw [hell₁, he])
    have h2 := unique_ell_four rho₂ hrho₂ (by rw [hell₂, he])
    simp [h1, h2]

/-- Residual at `ell = 4` (unique empty matching). -/
theorem encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_ell_four :
    EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := 4) rfl searchD4mp searchD4mp_width :=
  encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_of_ell_ne_three
    (by decide)

/-- Residual at `ell ≤ 2` (empty depth-eligible slice). -/
theorem encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_ell_le_two
    {ell : Nat} (hle : ell ≤ 2) :
    EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl searchD4mp searchD4mp_width := by
  intro rho₁ _rho₂ hrho₁ _hrho₂ hell₁ _hell₂ ht₁ _ht₂ _hcode _hlen
  exact (not_depth_eligible_ell_lt_three_t_three rho₁ hell₁ hle ht₁).elim

/-- **S2205 named-fiber residual:** on the multi-preimage length-2 pair,
equal codes force equal second-block entries (vacuous — codes differ). -/
theorem encodeMatchLengthTwoExitEqResidual_named_fiber
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoA))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rhoB)) :
    encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoA searchD4mp isMatching_rhoA freePigeons_rhoA ht₁
        searchD4mp_width =
      encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := 3) rfl
        rhoB searchD4mp isMatching_rhoB freePigeons_rhoB ht₂
        searchD4mp_width →
      secondBlockEntry? rhoA searchD4mp 3 =
        secondBlockEntry? rhoB searchD4mp 3 :=
  fun hcode => absurd hcode (encodeMatch_rhoA_ne_rhoB ht₁ ht₂)

/-! ## Summary -/

/-- **S2205 fiber-search summary (Fin 4 / `searchD4mp` / `t = 3`).**

* 16 single-edge free-count-3 matchings; complete for free-count 3.
* Named multi-preimage pair `{rhoA, rhoB}`: unequal `encodeMatch` codes;
  no path-exit bank collision on that equal-code fiber (fiber empty).
* `ell ≤ 2`: empty depth-eligible slice; `ell = 4`: unique empty matching;
  residual discharged on those free-counts.
* `ell = 3` package-wide residual (every free-count-3 length-2 base equals
  `rhoA` or `rhoB`) remains open beyond the named fiber; the named fiber
  residual holds vacuously by unequal codes.
-/
theorem fiber_search_fin4_t_three_summary :
    allSingleEdge4.length = 16 ∧
      (∀ mu, IsMatching mu → (freePigeons mu).card = 3 →
        mu ∈ allSingleEdge4) ∧
      rhoA ∈ allSingleEdge4 ∧ rhoB ∈ allSingleEdge4 ∧
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
          freePigeons_rhoA freePigeons_rhoB ht₁ ht₂) ∧
      (∀ (rho : MatchingMap 4 4) (ell : Nat),
        (freePigeons rho).card = ell → ell ≤ 2 →
          ¬ 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho)) ∧
      (∀ (rho : MatchingMap 4 4) (hrho : IsMatching rho),
        (freePigeons rho).card = 4 → rho = emptyMatching 4 4) ∧
      (∀ {ell : Nat}, ell ≠ 3 →
        EncodeMatchLengthTwoExitEqResidual (p := 4) (h := 4) (w := 2)
          (t := 3) (ell := ell) rfl searchD4mp searchD4mp_width) :=
  ⟨allSingleEdge4_length,
    fun mu hmu hell => mem_allSingleEdge4_of_free_count_three mu hmu hell,
    rhoA_mem_allSingleEdge4, rhoB_mem_allSingleEdge4,
    fun ht₁ ht₂ => no_equal_code_fiber_rhoA_rhoB ht₁ ht₂,
    fun ht₁ ht₂ => no_path_exit_collision_named_fiber ht₁ ht₂,
    fun rho _ell hell hle =>
      not_depth_eligible_ell_lt_three_t_three rho hell hle,
    fun rho hrho hell => unique_ell_four rho hrho hell,
    fun {_ell} hne =>
      encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three_of_ell_ne_three hne⟩

end PHPMatchingEncodeFiberSearch
end PvNP
