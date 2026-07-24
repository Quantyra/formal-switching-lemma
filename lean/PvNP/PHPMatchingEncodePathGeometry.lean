import PvNP.PHPMatchingEncodePathGeometryTarget
import PvNP.PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
import PvNP.PHPMatchingEncodePackageCount
import PvNP.PHPMatchingEncodeConditionalFiber
import PvNP.PHPMatchingEncodeAnswerRedesign

/-!
# S2222: packet-native path-geometry walked-pair encode

Instantiate `PathGeometryPacket` with a concrete path certificate:
`G2` together with the first-block walked pairs from the deep feed.
This puts path geometry in the packet (no free `Fin t → _` stream, no
side-bit `4^j` tax).  Package injectivity and the S2214-shaped grade bound
`H · (2w)^j` are inherited from existing `G1`/`G2` package force; walked
pairs are included for residual discharge-by-construction, not as a new
counting alphabet.

Not general GA-4, switching, P-vs-NP, or `v0.11.0`.  Fin4 `6/16` remains
regression-only via the S2221 force gate on `packageEncode`.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodePathGeometry

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeAnswerAlphabetLengthTwo
open PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
open PHPMatchingEncodePackageInj
open PHPMatchingEncodePackageCount
open PHPMatchingEncodeAnswerRedesign
open PHPMatchingEncodePathGeometryTarget
open PHPMatchingCodeBound

/-- Concrete path-geometry certificate: graded β-code plus first-block walked
pairs (packet-native; no free answer stream). -/
abbrev PathGeometryPairCode (p h w : Nat) :=
  List (Finset (Fin w)) × List (Fin p × Fin h)

/-- First-block walked pairs on the synchronized deep feed. -/
def firstBlockWalkedPairs {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (t : Nat) : List (Fin p × Fin h) :=
  match blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) with
  | [] => []
  | B :: _ => B.steps.map VStep.pair

theorem firstBlockWalkedPairs_cons {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (t : Nat) (B : VBlock p h) (Bs : List (VBlock p h))
    (hblocks :
      blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) = B :: Bs) :
    firstBlockWalkedPairs rho D t = B.steps.map VStep.pair := by
  simp only [firstBlockWalkedPairs, hblocks]

/-- Path exit is exactly base composed with the packet walked pairs. -/
theorem firstBlockPathExitMatching_eq_compose_walked {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (t : Nat) :
    firstBlockPathExitMatching rho D t =
      compose rho (pairsToMatching (firstBlockWalkedPairs rho D t)) := by
  match hblocks : blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) with
  | [] =>
      simp only [firstBlockPathExitMatching, firstBlockWalkedPairs, hblocks,
        pairsToMatching]
      exact (compose_empty_right rho).symm
  | B :: Bs =>
      simp only [firstBlockPathExitMatching, firstBlockWalkedPairs, hblocks]

/-- Bad-domain path-geometry encode: G1 from deterministic encode, pathCode =
`(G2, first-block walked pairs)`. -/
def pathGeometryEncode {h w t ell : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) :
    PathGeometryPacket h h (PathGeometryPairCode h h w) where
  G1 := (badEncode hw rho).G1
  pathCode := ((badEncode hw rho).G2, firstBlockWalkedPairs rho.1 D t)

/-- Fixed-grade slice for the path-geometry encode. -/
def pathGeometryBadGrade {h w : Nat} (t ell : Nat) (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho => (badEncode hw rho).j = j

theorem pathGeometryBadGrade_mem_j_range {h w t ell j : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    {rho : BadEncodeDomain h t ell D}
    (hrho : rho ∈ pathGeometryBadGrade t ell D hw j) :
    j ≤ t ∧ t ≤ 2 * j := by
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  have hrange := encodeMatch_j_le_t rfl rho.1 D hmem.1.1 hmem.1.2 ht hw
  have hj : (badEncode hw rho).j = j := (Finset.mem_filter.mp hrho).2
  have hrange' : (badEncode hw rho).j ≤ t ∧ t ≤ 2 * (badEncode hw rho).j := by
    simpa [badEncode, hmem, ht] using hrange
  rwa [hj] at hrange'

/-- Project path-geometry encode to the classical `(G1,G2)` mcode surface. -/
def pathGeometryEncodeG1G2 {h w t ell : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) :
    MatchingMap h h × List (Finset (Fin w)) :=
  ((badEncode hw rho).G1, (badEncode hw rho).G2)

/-- Image of a fixed bad grade under the `(G1,G2)` projection. -/
def pathGeometryBadGradeG1G2Image {h w : Nat} (t ell : Nat) (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (MatchingMap h h × List (Finset (Fin w))) :=
  (pathGeometryBadGrade t ell D hw j).image (pathGeometryEncodeG1G2 hw)

/-- Unconditional projected-image bound: S2214 shape `H · (2w)^j`, no side-bit
`4^j`. -/
theorem pathGeometryBadGradeG1G2Image_card_le {h w t ell j : Nat}
    (D : MDNF h h) (hw : ∀ term ∈ D, term.length ≤ w) :
    (pathGeometryBadGradeG1G2Image t ell D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  let S := pathGeometryBadGradeG1G2Image t ell D hw j
  apply mcode_only_grade_card_le_of_g1g2_inj (h := h) (w := w) (j := j) S
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    exact badEncode_G1_mem_honest hw rho (Finset.mem_filter.mp hrho).2
  · intro p hp b hb
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    have hgrade := encodeMatch_mem_gradedCode rho.1 D hmem.1.1 hmem.1.2 rfl ht hw
    exact (by simpa [pathGeometryEncodeG1G2, badEncode, hmem, ht] using
      hgrade.1 b hb)
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    have hgrade := encodeMatch_mem_gradedCode rho.1 D hmem.1.1 hmem.1.2 rfl ht hw
    have hj := (Finset.mem_filter.mp hrho).2
    have hgrade' : codeSize (badEncode hw rho).G2 = (badEncode hw rho).j := by
      simpa [badEncode, hmem, ht] using hgrade.2
    simpa [pathGeometryEncodeG1G2, badEncode, hmem, ht] using hgrade'.trans hj
  · intro _ _ _ _ hp
    exact hp

/-- Source grade bound under `(G1,G2)` injectivity on the grade. -/
theorem pathGeometryBadGrade_card_le_of_g1g2_injOn {h w t ell j : Nat}
    (D : MDNF h h) (hw : ∀ term ∈ D, term.length ≤ w)
    (hinj : Set.InjOn (pathGeometryEncodeG1G2 hw)
      (↑(pathGeometryBadGrade t ell D hw j) :
        Set (BadEncodeDomain h t ell D))) :
    (pathGeometryBadGrade t ell D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  rw [← Finset.card_image_of_injOn hinj]
  exact pathGeometryBadGradeG1G2Image_card_le D hw

/-- Package grade identity. -/
theorem badGrade_eq_pathGeometryBadGrade (ell j : Nat) :
    (show Finset (BadEncodeDomain 4 3 ell searchD4mp) from badGrade ell j) =
      pathGeometryBadGrade (h := 4) (w := 2) 3 ell searchD4mp
        searchD4mp_width j := by
  ext rho
  simp only [badGrade, pathGeometryBadGrade, Finset.mem_filter, Finset.mem_univ,
    true_and]
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  have hcode : packageEncode rho = badEncode searchD4mp_width rho := by
    simp [packageEncode, badEncode, hmem, ht]
  rw [hcode]

/-- Package `G1`/`G2` injectivity on each path-geometry grade. -/
theorem pathGeometryEncodeG1G2_injOn_searchD4mp_badGrade (ell j : Nat) :
    Set.InjOn
      (pathGeometryEncodeG1G2 (h := 4) (w := 2) (t := 3) (ell := ell)
        (D := searchD4mp) searchD4mp_width)
      (↑(pathGeometryBadGrade (h := 4) (w := 2) 3 ell searchD4mp
          searchD4mp_width j) :
        Set (BadEncodeDomain 4 3 ell searchD4mp)) := by
  have hinjG := badEncode_G1G2_injOn_atMostTwoBlockGrade
    (t := 3) (ell := ell) searchD4mp searchD4mp_width j
    encodeMatchG1G2LengthTwoPathExitEqResidual_searchD4mp_t_three
  intro rho hrho rho' hrho' heq
  apply hinjG
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hrho).2⟩
    let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
    let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
      Nat.le_of_pred_lt hmem.2
    exact enteredTermsOf_length_le_two_searchD4mp_t_three
      rho.1 hmem.1.1 hmem.1.2 ht
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, (Finset.mem_filter.mp hrho').2⟩
    let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho'.1).mp rho'.2
    let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho'.1) :=
      Nat.le_of_pred_lt hmem.2
    exact enteredTermsOf_length_le_two_searchD4mp_t_three
      rho'.1 hmem.1.1 hmem.1.2 ht
  · exact heq

/-- Full path-geometry packet injectivity on each package grade (walked pairs
unused for uniqueness; inherited from `G1`/`G2`). -/
theorem pathGeometryEncode_injOn_searchD4mp_badGrade (ell j : Nat) :
    Set.InjOn
      (pathGeometryEncode (h := 4) (w := 2) (t := 3) (ell := ell)
        (D := searchD4mp) searchD4mp_width)
      (↑(pathGeometryBadGrade (h := 4) (w := 2) 3 ell searchD4mp
          searchD4mp_width j) :
        Set (BadEncodeDomain 4 3 ell searchD4mp)) := by
  intro rho hrho rho' hrho' heq
  apply pathGeometryEncodeG1G2_injOn_searchD4mp_badGrade ell j hrho hrho'
  have hG1 : (pathGeometryEncode searchD4mp_width rho).G1 =
      (pathGeometryEncode searchD4mp_width rho').G1 :=
    congrArg PathGeometryPacket.G1 heq
  have hG2 : (pathGeometryEncode searchD4mp_width rho).pathCode.1 =
      (pathGeometryEncode searchD4mp_width rho').pathCode.1 :=
    congrArg (fun p : PathGeometryPacket 4 4 (PathGeometryPairCode 4 4 2) =>
      p.pathCode.1) heq
  exact Prod.ext (by simpa [pathGeometryEncode, pathGeometryEncodeG1G2] using hG1)
    (by simpa [pathGeometryEncode, pathGeometryEncodeG1G2] using hG2)

/-- Package source bound: S2214 shape `H · 4^j` (`4 = 2w` at `w = 2`), no
side-bit tax. -/
theorem badGrade_searchD4mp_pathGeometry_card_le (ell j : Nat) :
    (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j := by
  calc
    (badGrade ell j).card =
        (pathGeometryBadGrade (h := 4) (w := 2) 3 ell searchD4mp
          searchD4mp_width j).card :=
      congrArg Finset.card (badGrade_eq_pathGeometryBadGrade ell j)
    _ ≤ (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j :=
      pathGeometryBadGrade_card_le_of_g1g2_injOn searchD4mp searchD4mp_width
        (pathGeometryEncodeG1G2_injOn_searchD4mp_badGrade ell j)

/-- Grade target shape on the package path-geometry bound (`C = 4 = 2w`). -/
theorem pathGeometry_package_grade_target (ell j : Nat) :
    PathGeometryGradeTarget
      (honestMatchingSpace 4 4 (ell - j)).card 4 j
      (badGrade ell j).card := by
  have h := badGrade_searchD4mp_pathGeometry_card_le ell j
  simpa [PathGeometryGradeTarget, show (2 * 2 : Nat) = 4 from rfl] using h

/-- Package path exit recovered from the walked-pair component. -/
theorem packagePathGeometryEncode_pathExit (ell : Nat)
    (rho : BadEncodeDomain 4 3 ell searchD4mp) :
    firstBlockPathExitMatching rho.1 searchD4mp 3 =
      compose rho.1
        (pairsToMatching
          (pathGeometryEncode searchD4mp_width rho).pathCode.2) := by
  simpa [pathGeometryEncode] using
    firstBlockPathExitMatching_eq_compose_walked rho.1 searchD4mp 3

/-- S2222 summary: walked-pair packet, package injectivity, S2214-shaped grade
bound / grade target, and regression force gate retained. -/
theorem path_geometry_encode_s2222_summary :
    (∀ ell j : Nat,
      (show Finset (BadEncodeDomain 4 3 ell searchD4mp) from badGrade ell j) =
        pathGeometryBadGrade (h := 4) (w := 2) 3 ell searchD4mp
          searchD4mp_width j) ∧
    (∀ ell j : Nat,
      Set.InjOn
        (pathGeometryEncode (h := 4) (w := 2) (t := 3) (ell := ell)
          (D := searchD4mp) searchD4mp_width)
        (↑(pathGeometryBadGrade (h := 4) (w := 2) 3 ell searchD4mp
            searchD4mp_width j) :
          Set (BadEncodeDomain 4 3 ell searchD4mp))) ∧
    (∀ ell j : Nat,
      (badGrade ell j).card ≤
        (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) ∧
    (∀ ell j : Nat,
      PathGeometryGradeTarget
        (honestMatchingSpace 4 4 (ell - j)).card 4 j
        (badGrade ell j).card) ∧
    PathGeometryForceGate (Finset.univ : Finset (SearchD4mpBad 3))
      packageEncode (honestMatchingSpace 4 4 3) 6 16 ∧
    (∀ ell : Nat, ∀ rho : BadEncodeDomain 4 3 ell searchD4mp,
      firstBlockPathExitMatching rho.1 searchD4mp 3 =
        compose rho.1
          (pairsToMatching
            (pathGeometryEncode searchD4mp_width rho).pathCode.2)) :=
  ⟨badGrade_eq_pathGeometryBadGrade,
    pathGeometryEncode_injOn_searchD4mp_badGrade,
    badGrade_searchD4mp_pathGeometry_card_le,
    pathGeometry_package_grade_target,
    path_geometry_force_gate_exact_six_sixteen,
    packagePathGeometryEncode_pathExit⟩

end PHPMatchingEncodePathGeometry
end PvNP
