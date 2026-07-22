import PvNP.PHPMatchingEncodePathGeometryConcrete
import PvNP.PHPMatchingEncodeAnswerRedesign

/-!
# S2223: path-geometry image/carrier bound (Gate A)

This module counts the fixed-grade image of the packet-native path-geometry
encode in the carrier `(G1, β)` only.  It deliberately does not walk answers as
a free stream, does not add a side-bit product, does not grind residual
preimage injectivity, and does not assert a new force gate, GA-4, switching,
P-vs-NP, or `v0.11.0`.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodePathGeometryImage

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodePackageCount
open PHPMatchingEncodeAnswerRedesign
open PHPMatchingEncodePathGeometryTarget
open PHPMatchingEncodePathGeometryConcrete

/-- Path-geometry bad encode into the image carrier: only `(G1, β)`.  The
walked-pair list stays coupled in the packet but is not counted as a free
stream coordinate. -/
def pathGeometryBadEncode {h w t ell : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) :
    MatchingMap h h × List (Finset (Fin w)) :=
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  let pkt := pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
    (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
  (pkt.G1, pkt.pathCode.beta)

/-- A fixed-grade slice of the bad encode domain, graded by the coupled
path-geometry packet's `j`. -/
def pathGeometryBadGrade {h w : Nat} (t ell : Nat) (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho =>
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    (pathGeometryEncode (p := h) (h := h) (w := w) (t := t) (ell := ell)
      rfl rho.1 D hmem.1.1 hmem.1.2 ht hw).pathCode.j = j

/-- Image of a fixed path-geometry grade in the `(G1, β)` carrier. -/
def pathGeometryBadGradeImage {h w : Nat} (t ell : Nat) (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (MatchingMap h h × List (Finset (Fin w))) :=
  (pathGeometryBadGrade t ell D hw j).image (pathGeometryBadEncode hw)

/-- Bad-domain wrapper: β is well-formed and its `codeSize` is the packet `j`. -/
theorem pathGeometryBadEncode_beta_wf {h w t ell : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w) (rho : BadEncodeDomain h t ell D) :
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    let pkt := pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
    (∀ b ∈ (pathGeometryBadEncode hw rho).2, Finset.Nonempty b) ∧
      codeSize (pathGeometryBadEncode hw rho).2 = pkt.pathCode.j := by
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  simpa [pathGeometryBadEncode, hmem, ht] using
    pathGeometryEncode_beta_wf (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw

/-- Bad-domain wrapper: `G1` lands in the honest matching carrier at the
packet's grade. -/
theorem pathGeometryBadEncode_G1_mem_honest {h w t ell : Nat}
    {D : MDNF h h} (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) :
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    let pkt := pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
    (pathGeometryBadEncode hw rho).1 ∈
      honestMatchingSpace h h (ell - pkt.pathCode.j) := by
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  simpa [pathGeometryBadEncode, hmem, ht] using
    pathGeometryEncode_G1_mem_honest (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw

/-- Bad-domain wrapper: the coupled walked-pair list has length `t`. -/
theorem pathGeometryBadEncode_walked_length {h w t ell : Nat}
    {D : MDNF h h} (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) :
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    let pkt := pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
    pkt.pathCode.walked.length = t := by
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  simpa [pathGeometryBadEncode, hmem, ht] using
    pathGeometryEncode_walked_length (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw

/-- The path-geometry `(G1, β)` image has the mcode-only carrier bound, with no
side-bit or answer-stream product. -/
theorem pathGeometryBadGradeImage_card_le {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) :
    (pathGeometryBadGradeImage t ell D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  let S := pathGeometryBadGradeImage t ell D hw j
  apply mcode_only_grade_card_le_of_g1g2_inj S
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    have hj : (pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
        (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw).pathCode.j = j :=
      (Finset.mem_filter.mp hrho).2
    have hG1 := pathGeometryEncode_G1_mem_honest (p := h) (h := h) (w := w)
      (t := t) (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
    simpa [pathGeometryBadEncode, hmem, ht, hj] using hG1
  · intro p hp b hb
    rcases Finset.mem_image.mp hp with ⟨rho, _hrho, rfl⟩
    exact (pathGeometryBadEncode_beta_wf hw rho).1 b hb
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    have hj : (pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
        (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw).pathCode.j = j :=
      (Finset.mem_filter.mp hrho).2
    have hβ := pathGeometryEncode_beta_wf (p := h) (h := h) (w := w) (t := t)
      (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
    simpa [pathGeometryBadEncode, hmem, ht, hj] using hβ.2
  · intro x _ y _ hxy
    exact hxy

/-- The image-cardinality bound as an abstract path-geometry target. -/
theorem pathGeometryBadGradeImage_grade_target {h w t ell j : Nat}
    (D : MDNF h h) (hw : ∀ term ∈ D, term.length ≤ w) :
    PathGeometryGradeTarget (honestMatchingSpace h h (ell - j)).card (2 * w) j
      (pathGeometryBadGradeImage t ell D hw j).card := by
  simpa [PathGeometryGradeTarget] using pathGeometryBadGradeImage_card_le D hw

/-- Fixed `searchD4mp`, `w = 2`, `t = 3` image package. -/
def packagePathGeometryBadGradeImage (ell j : Nat) :
    Finset (MatchingMap 4 4 × List (Finset (Fin 2))) :=
  pathGeometryBadGradeImage (h := 4) (w := 2) 3 ell searchD4mp
    searchD4mp_width j

/-- Fixed-package path-geometry image bound with carrier base `C = 4`. -/
theorem packagePathGeometryBadGradeImage_card_le (ell j : Nat) :
    (packagePathGeometryBadGradeImage ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * 4 ^ j := by
  simpa [packagePathGeometryBadGradeImage, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using
    pathGeometryBadGradeImage_card_le (h := 4) (w := 2) (t := 3)
      (ell := ell) (j := j) searchD4mp searchD4mp_width

/-- Fixed-package path-geometry image target with carrier base `C = 4`. -/
theorem packagePathGeometryBadGradeImage_grade_target (ell j : Nat) :
    PathGeometryGradeTarget (honestMatchingSpace 4 4 (ell - j)).card 4 j
      (packagePathGeometryBadGradeImage ell j).card := by
  simpa [PathGeometryGradeTarget] using
    packagePathGeometryBadGradeImage_card_le ell j

/-- S2223 summary pin: image counting is only over `(G1, β)`, with structural
coupling available separately on the bad-domain wrapper. -/
theorem path_geometry_image_s2223_summary :
    (∀ {h w t ell j : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w),
      (pathGeometryBadGradeImage t ell D hw j).card ≤
        (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j) ∧
    (∀ ell j,
      (packagePathGeometryBadGradeImage ell j).card ≤
        (honestMatchingSpace 4 4 (ell - j)).card * 4 ^ j) ∧
    (∀ {h w t ell : Nat} {D : MDNF h h}
      (hw : ∀ term ∈ D, term.length ≤ w)
      (rho : BadEncodeDomain h t ell D),
      (∀ b ∈ (pathGeometryBadEncode hw rho).2, Finset.Nonempty b) ∧
        ∃ pkt : PathGeometryPacket h h (PathPairCode h h w t ell),
          pkt =
            (let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
             let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
               Nat.le_of_pred_lt hmem.2
             pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
               (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw) ∧
          (pathGeometryBadEncode hw rho).1 ∈
            honestMatchingSpace h h (ell - pkt.pathCode.j) ∧
          pkt.pathCode.walked.length = t) := by
  refine ⟨pathGeometryBadGradeImage_card_le,
    packagePathGeometryBadGradeImage_card_le, ?_⟩
  intro h w t ell D hw rho
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  let pkt := pathGeometryEncode (p := h) (h := h) (w := w) (t := t)
    (ell := ell) rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
  exact ⟨(pathGeometryBadEncode_beta_wf hw rho).1, pkt, rfl,
    pathGeometryBadEncode_G1_mem_honest hw rho,
    pathGeometryBadEncode_walked_length hw rho⟩

end PHPMatchingEncodePathGeometryImage
end PvNP
