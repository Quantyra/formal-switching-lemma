import PvNP.PHPMatchingEncodePathGeometryImage
import PvNP.PHPMatchingEncodePackageDenomCompare
import PvNP.PHPMatchingEncodeParametricRatio
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# S2224: path-geometry force-bridge STOP-LOSS package

This module bridges fixed path-geometry source grades to their `(G1, β)` image
only under an explicit named fiber bound.  The image bound alone is a STOP-LOSS
for force: the fixed-package image sum is still bounded by `3072`, which is not
strict against the honest denominator `16`.  The only force gate re-pinned here
is the existing exact package-encode `6/16` regression.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodePathGeometryForceBridge

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodePackageCount
open PHPMatchingEncodePackageDenomCompare
open PHPMatchingEncodeParametricRatio
open PHPMatchingEncodePathGeometryTarget
open PHPMatchingEncodePathGeometryImage

set_option maxRecDepth 4096

/-- Named fiber hypothesis for transferring a path-geometry image bound back to
the fixed source grade.  This is deliberately conditional: S2224 does not prove
such a fiber bound from the path-geometry image bound alone. -/
def PathGeometryImageFiberBound {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (K : Nat) : Prop :=
  ∀ y ∈ pathGeometryBadGradeImage t ell D hw j,
    ((pathGeometryBadGrade t ell D hw j).filter fun rho =>
      pathGeometryBadEncode hw rho = y).card ≤ K

/-- General finite source-to-image counting under a uniform fiber cap. -/
theorem card_le_image_mul_of_fiberBound {α β : Type*} [DecidableEq α]
    [DecidableEq β] (grade : Finset α) (encode : α → β) (K : Nat)
    (hfiber : ∀ y ∈ grade.image encode,
      (grade.filter fun x => encode x = y).card ≤ K) :
    grade.card ≤ K * (grade.image encode).card := by
  classical
  have hsubset : grade ⊆ (grade.image encode).biUnion fun y =>
      grade.filter fun x => encode x = y := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨encode x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      by simp [hx]⟩
  calc
    grade.card ≤ ((grade.image encode).biUnion fun y =>
        grade.filter fun x => encode x = y).card := Finset.card_le_card hsubset
    _ ≤ (grade.image encode).card * K := by
      exact Finset.card_biUnion_le_card_mul _ _ _ hfiber
    _ = K * (grade.image encode).card := Nat.mul_comm _ _

/-- Source path-geometry grade bound by image cardinality, assuming the named
uniform image-fiber cap. -/
theorem pathGeometryBadGrade_card_le_image_mul_of_fiberBound
    {h w t ell j K : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hfiber : PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K) :
    (pathGeometryBadGrade t ell D hw j).card ≤
      K * (pathGeometryBadGradeImage t ell D hw j).card := by
  simpa [pathGeometryBadGradeImage] using
    card_le_image_mul_of_fiberBound (pathGeometryBadGrade t ell D hw j)
      (pathGeometryBadEncode hw) K hfiber

/-- Conditional source grade bound by the S2223 `H·C^j` image bound and the
explicit fiber cap `K`. -/
theorem pathGeometryBadGrade_card_le_K_H_C_pow
    {h w t ell j K : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hfiber : PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K) :
    (pathGeometryBadGrade t ell D hw j).card ≤
      K * ((honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j) := by
  exact (pathGeometryBadGrade_card_le_image_mul_of_fiberBound D hw hfiber).trans
    (Nat.mul_le_mul_left K (pathGeometryBadGradeImage_card_le D hw))

/-- The named fiber cap specializes to every fiber over the path-geometry
image. -/
theorem pathGeometryBadGradeFiber_card_le_of_fiberBound
    {h w t ell j K : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hfiber : PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K)
    {y : MatchingMap h h × List (Finset (Fin w))}
    (hy : y ∈ pathGeometryBadGradeImage t ell D hw j) :
    ((pathGeometryBadGrade t ell D hw j).filter fun rho =>
      pathGeometryBadEncode hw rho = y).card ≤ K := by
  exact hfiber y hy

/-- Injectivity on the fixed grade is the special `K = 1` fiber condition. -/
theorem pathGeometryImageFiberBound_one_of_injOn
    {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hinj : Set.InjOn (pathGeometryBadEncode hw)
      (↑(pathGeometryBadGrade t ell D hw j) : Set (BadEncodeDomain h t ell D))) :
    PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw 1 := by
  intro y hy
  rw [Finset.card_le_one]
  intro a ha b hb
  have haGrade : a ∈ pathGeometryBadGrade t ell D hw j := (Finset.mem_filter.mp ha).1
  have hbGrade : b ∈ pathGeometryBadGrade t ell D hw j := (Finset.mem_filter.mp hb).1
  have haya : pathGeometryBadEncode hw a = y := (Finset.mem_filter.mp ha).2
  have hbyb : pathGeometryBadEncode hw b = y := (Finset.mem_filter.mp hb).2
  exact hinj haGrade hbGrade (haya.trans hbyb.symm)

/-- Optional injective source-to-image bridge, matching the side-bit image
pattern: injectivity converts image counting directly into source counting. -/
theorem pathGeometryBadGrade_card_le_of_injOn {h w t ell j : Nat}
    (D : MDNF h h) (hw : ∀ term ∈ D, term.length ≤ w)
    (hinj : Set.InjOn (pathGeometryBadEncode hw)
      (↑(pathGeometryBadGrade t ell D hw j) : Set (BadEncodeDomain h t ell D))) :
    (pathGeometryBadGrade t ell D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  rw [← Finset.card_image_of_injOn hinj]
  exact pathGeometryBadGradeImage_card_le D hw

/-- Fixed-package path-geometry image grade sum at `ell = 3`: still `3072`. -/
theorem packagePathGeometryBadGradeImage_two_three_card_le_3072 :
    (packagePathGeometryBadGradeImage 3 2).card +
      (packagePathGeometryBadGradeImage 3 3).card ≤ 3072 := by
  have h2 := packagePathGeometryBadGradeImage_card_le 3 2
  have h3 := packagePathGeometryBadGradeImage_card_le 3 3
  rw [honestMatchingSpace_four_four_one_card] at h2
  rw [honestMatchingSpace_four_four_zero_card] at h3
  norm_num at h2 h3 ⊢
  omega

/-- The STOP-LOSS image/package bound is larger than the honest denominator. -/
theorem packagePathGeometryBadGradeImage_bound_exceeds_denominator :
    (honestMatchingSpace 4 4 3).card < 3072 :=
  searchD4mp_ell_free_bound_exceeds_denominator

/-- Hence the path-geometry image package bound is not a strict force bound. -/
theorem packagePathGeometryBadGradeImage_bound_not_strict :
    ¬ (3072 < (honestMatchingSpace 4 4 3).card) :=
  searchD4mp_ell_free_bound_not_strict

/-- Existing exact package classification: the force outcome remains exactly
the replayed `6/16` regression, not a new path-geometry image force theorem. -/
theorem packageEncode_exact_six_strict :
    (vbadMatchings searchD4mp 2 3).card = 6 ∧
      6 < (honestMatchingSpace 4 4 3).card ∧
      PathGeometryForceGate (Finset.univ : Finset (SearchD4mpBad 3))
        packageEncode (honestMatchingSpace 4 4 3) 6 16 := by
  exact ⟨searchD4mp_exact_card_eq_six,
    (by simpa [searchD4mp_exact_card_eq_six] using
      searchD4mp_exact_card_strict_denominator),
    path_geometry_force_gate_exact_six_sixteen⟩

/-- S2224 STOP-LOSS summary: conditional fiber infrastructure is present, the
path-geometry image/package upper bound remains TRIVIAL (`3072` versus `16`),
and the only force gate is the existing exact package-encode `6/16` replay. -/
theorem path_geometry_force_bridge_s2224_stop_loss_summary :
    (∀ {h w t ell j K : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w),
      PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K →
        (pathGeometryBadGrade t ell D hw j).card ≤
          K * (pathGeometryBadGradeImage t ell D hw j).card) ∧
    (∀ {h w t ell j K : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w),
      PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K →
        (pathGeometryBadGrade t ell D hw j).card ≤
          K * ((honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j)) ∧
    (packagePathGeometryBadGradeImage 3 2).card +
      (packagePathGeometryBadGradeImage 3 3).card ≤ 3072 ∧
    (honestMatchingSpace 4 4 3).card < 3072 ∧
    ¬ (3072 < (honestMatchingSpace 4 4 3).card) ∧
    (vbadMatchings searchD4mp 2 3).card = 6 ∧
    6 < (honestMatchingSpace 4 4 3).card ∧
    PathGeometryForceGate (Finset.univ : Finset (SearchD4mpBad 3))
      packageEncode (honestMatchingSpace 4 4 3) 6 16 := by
  refine ⟨pathGeometryBadGrade_card_le_image_mul_of_fiberBound,
    pathGeometryBadGrade_card_le_K_H_C_pow,
    packagePathGeometryBadGradeImage_two_three_card_le_3072,
    packagePathGeometryBadGradeImage_bound_exceeds_denominator,
    packagePathGeometryBadGradeImage_bound_not_strict, ?_, ?_, ?_⟩
  · exact packageEncode_exact_six_strict.1
  · exact packageEncode_exact_six_strict.2.1
  · exact packageEncode_exact_six_strict.2.2

end PHPMatchingEncodePathGeometryForceBridge
end PvNP
