import PvNP.PHPMatchingEncodeSideBitCarrier
import PvNP.PHPMatchingEncodeConditionalFiber
import PvNP.PHPMatchingEncodeAnswerRedesign

/-!
# S2218: encode images in the side-bit carrier

This module constructs the side-bit image and proves its grade bound.  The
image bound is unconditional; the corresponding source bound explicitly
requires injectivity on the selected grade.  This is not general GA-4, a
switching lemma, a lower bound, or a release result.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeSideBitImage

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingAnswerTransport
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeAnswerRedesign
open PHPMatchingEncodeSideBitCarrier

/-- Query-side bits of the synchronized deep trace. -/
def traceSideBitsDeep {p h t : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) : Fin t → Bool :=
  fun i => stepSideBit
    ((eventsSteps (vtrace rho D (leftmostLiveDeepFeed rho D t))).get
      ⟨i.1, by
        rw [leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht]
        exact i.2⟩)

/-- A trace pair and its recorded side bit recover that step's far endpoint. -/
theorem farEndpointFromSide_traceSideBitsDeep {p h t : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) (i : Fin t) :
    let steps := eventsSteps (vtrace rho D (leftmostLiveDeepFeed rho D t))
    let hi : i.1 < steps.length := by
      rw [leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht]
      exact i.2
    farEndpointFromSide (steps.get ⟨i.1, hi⟩).pair
        (traceSideBitsDeep hsq rho D hrho ht i) =
      stepAnswer (steps.get ⟨i.1, hi⟩) := by
  simp only [traceSideBitsDeep]
  exact farEndpointFromSide_stepSideBit _

/-- The deterministic bad encode with its answer names replaced by query-side
bits from the same synchronized deep trace. -/
def sideBitEncode {h w t ell : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) :
    MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool) :=
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  ((badEncode hw rho).G1, (badEncode hw rho).G2,
    traceSideBitsDeep rfl rho.1 D hmem.1.1 ht)

/-- A fixed-grade slice of the bad encode domain. -/
def sideBitBadGrade {h w : Nat} (t ell : Nat) (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho => (badEncode hw rho).j = j

/-- Every inhabited side-bit grade lies in the deterministic encode range. -/
theorem sideBitBadGrade_mem_j_range {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    {rho : BadEncodeDomain h t ell D}
    (hrho : rho ∈ sideBitBadGrade t ell D hw j) : j ≤ t ∧ t ≤ 2 * j := by
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  have hrange := encodeMatch_j_le_t rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
  have hj : (badEncode hw rho).j = j := (Finset.mem_filter.mp hrho).2
  have hrange' : (badEncode hw rho).j ≤ t ∧ t ≤ 2 * (badEncode hw rho).j := by
    simpa [badEncode, hmem, ht] using hrange
  rwa [hj] at hrange'

/-- Image of a fixed bad grade in the side-bit carrier. -/
def sideBitBadGradeImage {h w : Nat} (t ell : Nat) (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool)) :=
  (sideBitBadGrade t ell D hw j).image (sideBitEncode hw)

/-- The side-bit image has the redesigned `4^j` carrier bound, without an
injectivity assumption on the source. -/
theorem sideBitBadGradeImage_card_le {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) :
    (sideBitBadGradeImage t ell D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j * 4 ^ j := by
  let S := sideBitBadGradeImage t ell D hw j
  by_cases hne : (sideBitBadGrade t ell D hw j).Nonempty
  · obtain ⟨rho₀, hrho₀⟩ := hne
    have htj : t ≤ 2 * j := (sideBitBadGrade_mem_j_range D hw hrho₀).2
    apply mcode_sidebit_grade_card_le htj S
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
      exact badEncode_G1_mem_honest hw rho (Finset.mem_filter.mp hrho).2
    · intro p hp b hb
      rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
      let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
      let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
      have hgrade := encodeMatch_mem_gradedCode rho.1 D hmem.1.1 hmem.1.2 rfl ht hw
      exact (by simpa [sideBitEncode, hmem, ht, badEncode] using hgrade.1 b hb)
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
      let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
      let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
      have hgrade := encodeMatch_mem_gradedCode rho.1 D hmem.1.1 hmem.1.2 rfl ht hw
      have hj := (Finset.mem_filter.mp hrho).2
      have hgrade' : codeSize (badEncode hw rho).G2 = (badEncode hw rho).j := by
        simpa [badEncode, hmem, ht] using hgrade.2
      simpa [sideBitEncode, hmem, ht] using hgrade'.trans hj
    · intro _ _ _ _ hp
      exact hp
  · have hempty : sideBitBadGrade t ell D hw j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [S, sideBitBadGradeImage, hempty]

/-- The source grade inherits the image bound whenever the side-bit encode is
injective on that grade. -/
theorem sideBitBadGrade_card_le_of_injOn {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hinj : Set.InjOn (sideBitEncode hw)
      (↑(sideBitBadGrade t ell D hw j) : Set (BadEncodeDomain h t ell D))) :
    (sideBitBadGrade t ell D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j * 4 ^ j := by
  rw [← Finset.card_image_of_injOn hinj]
  exact sideBitBadGradeImage_card_le D hw

/-- S2218 general summary: unconditional image counting and conditional source
counting remain explicitly separated. -/
theorem sidebit_image_s2218_summary :
    (∀ {h w t ell j : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w),
      (sideBitBadGradeImage t ell D hw j).card ≤
        (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j * 4 ^ j) ∧
    (∀ {h w t ell j : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w),
      Set.InjOn (sideBitEncode hw)
          (↑(sideBitBadGrade t ell D hw j) : Set (BadEncodeDomain h t ell D)) →
        (sideBitBadGrade t ell D hw j).card ≤
          (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j * 4 ^ j) :=
  ⟨sideBitBadGradeImage_card_le, sideBitBadGrade_card_le_of_injOn⟩

end PHPMatchingEncodeSideBitImage
end PvNP
