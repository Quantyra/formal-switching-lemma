import PvNP.PHPMatchingEncodePathGeometryTarget

/-!
# S2222: concrete path-geometry PairCode encode step (Gate A)

This module instantiates the S2221 packet-native path-geometry target with the
existing deterministic `encodeExt` and the coupled β / walked-pair trace data.
It proves only first structural landing facts for the concrete packet: β
well-formedness, G1 honest-space landing, and walked-pair length.

This does not reopen residual unique-preimage work, does not add a side-bit or
free answer-stream product tax, does not claim a new path-geometry force, and
does not assert GA-4, switching, P-vs-NP, or `v0.11.0`.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodePathGeometryConcrete

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodePackageCount
open PHPMatchingEncodePathGeometryTarget

/-- Concrete path-geometry code paired with the S2221 packet target: β-blocks,
walked query pairs, and the star/block code size `j`. -/
structure PathPairCode (p h w t ell : Nat) where
  beta : List (Finset (Fin w))
  walked : List (Fin p × Fin h)
  j : Nat
deriving DecidableEq

/-- Walked query pairs from the deterministic deep path. -/
def walkedPairsDeep {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (t : Nat) :
    List (Fin p × Fin h) :=
  (eventsSteps (vtrace rho D (leftmostLiveDeepFeed rho D t))).map VStep.pair

/-- Concrete packet-native path-geometry encode: the G1 extension coupled with
β-blocks and the walked-pair list from the same deterministic trace. -/
def pathGeometryEncode {p h w t ell : Nat} (_hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (_hrho : IsMatching rho)
    (_hell : (freePigeons rho).card = ell)
    (_ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (_hw : ∀ term ∈ D, term.length ≤ w) :
    PathGeometryPacket p h (PathPairCode p h w t ell) where
  G1 := encodeExt rho D (leftmostLiveDeepFeed rho D t)
  pathCode :=
    { beta := traceBetaDeep (w := w) rho D t
      walked := walkedPairsDeep rho D t
      j := codeSize (traceBetaDeep (w := w) rho D t) }

/-- The concrete path packet carries well-formed nonempty β-blocks and stores
the matching `codeSize` as its `j`. -/
theorem pathGeometryEncode_beta_wf {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let pkt := pathGeometryEncode hsq rho D hrho hell ht hw
    (∀ b ∈ pkt.pathCode.beta, Finset.Nonempty b) ∧
      codeSize pkt.pathCode.beta = pkt.pathCode.j := by
  intro pkt
  have hβ := traceBetaDeep_wellFormed_codeSize rho D hrho ht hw
  exact ⟨hβ.1, rfl⟩

/-- The G1 component of the concrete path packet lands in the honest matching
space at grade `ell - j`. -/
theorem pathGeometryEncode_G1_mem_honest {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let pkt := pathGeometryEncode hsq rho D hrho hell ht hw
    pkt.G1 ∈ honestMatchingSpace p h (ell - pkt.pathCode.j) := by
  intro pkt
  rw [mem_honestMatchingSpace]
  constructor
  · simpa [pathGeometryEncode] using
      encodeExt_isMatching rho D (leftmostLiveDeepFeed rho D t) hrho
  · have hβ := traceBetaDeep_wellFormed_codeSize rho D hrho ht hw
    have hfree := encodeExt_freePigeons_card rho D
      (leftmostLiveDeepFeed rho D t) hell hβ.2.symm
    change (freePigeons (encodeExt rho D (leftmostLiveDeepFeed rho D t))).card =
      ell - codeSize (traceBetaDeep (w := w) rho D t)
    exact hfree

/-- The walked-pair list has exactly the requested deep-path length. -/
theorem walkedPairsDeep_length {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (walkedPairsDeep rho D t).length = t := by
  unfold walkedPairsDeep
  rw [List.length_map]
  exact leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht

/-- Packet-level walked-pair length. -/
theorem pathGeometryEncode_walked_length {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let pkt := pathGeometryEncode hsq rho D hrho hell ht hw
    pkt.pathCode.walked.length = t := by
  intro _pkt
  simpa [pathGeometryEncode] using walkedPairsDeep_length hsq rho D hrho ht

/-- SearchD4mp convenience wrapper reusing the existing fixed-package bad
domain and deterministic feed.  Regression only; no new force claim. -/
def packagePathGeometryEncode {ell : Nat} (rho : SearchD4mpBad ell) :
    PathGeometryPacket 4 4 (PathPairCode 4 4 2 3 ell) :=
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  pathGeometryEncode (p := 4) (h := 4) (w := 2) (t := 3) (ell := ell) rfl
    rho.1 searchD4mp hmem.1.1 hmem.1.2 ht searchD4mp_width

/-- Fixed `SearchD4mpBad` wrapper: β well-formedness and `j` landing. -/
theorem packagePathGeometryEncode_beta_wf {ell : Nat}
    (rho : SearchD4mpBad ell) :
    (∀ b ∈ (packagePathGeometryEncode rho).pathCode.beta,
        Finset.Nonempty b) ∧
      codeSize (packagePathGeometryEncode rho).pathCode.beta =
        (packagePathGeometryEncode rho).pathCode.j := by
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  simpa [packagePathGeometryEncode, hmem, ht] using
    pathGeometryEncode_beta_wf (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl rho.1 searchD4mp hmem.1.1 hmem.1.2 ht
      searchD4mp_width

/-- Fixed `SearchD4mpBad` wrapper: G1 lands in the matching honest space at
the packet's concrete `j`. -/
theorem packagePathGeometryEncode_G1_mem_honest {ell : Nat}
    (rho : SearchD4mpBad ell) :
    (packagePathGeometryEncode rho).G1 ∈
      honestMatchingSpace 4 4 (ell - (packagePathGeometryEncode rho).pathCode.j) := by
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  simpa [packagePathGeometryEncode, hmem, ht] using
    pathGeometryEncode_G1_mem_honest (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl rho.1 searchD4mp hmem.1.1 hmem.1.2 ht
      searchD4mp_width

/-- Fixed `SearchD4mpBad` wrapper: the walked-pair list has length three. -/
theorem packagePathGeometryEncode_walked_length {ell : Nat}
    (rho : SearchD4mpBad ell) :
    (packagePathGeometryEncode rho).pathCode.walked.length = 3 := by
  let hmem := (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
  let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
    Nat.le_of_pred_lt hmem.2
  simpa [packagePathGeometryEncode, hmem, ht] using
    pathGeometryEncode_walked_length (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl rho.1 searchD4mp hmem.1.1 hmem.1.2 ht
      searchD4mp_width

/-- S2222 summary pin: concrete path-geometry packets carry well-formed β,
honest G1 landing, and exactly `t` walked pairs. -/
theorem path_geometry_concrete_s2222_summary {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let pkt := pathGeometryEncode hsq rho D hrho hell ht hw
    (∀ b ∈ pkt.pathCode.beta, Finset.Nonempty b) ∧
      codeSize pkt.pathCode.beta = pkt.pathCode.j ∧
      pkt.G1 ∈ honestMatchingSpace p h (ell - pkt.pathCode.j) ∧
      pkt.pathCode.walked.length = t := by
  intro pkt
  exact ⟨(pathGeometryEncode_beta_wf hsq rho D hrho hell ht hw).1,
    (pathGeometryEncode_beta_wf hsq rho D hrho hell ht hw).2,
    pathGeometryEncode_G1_mem_honest hsq rho D hrho hell ht hw,
    pathGeometryEncode_walked_length hsq rho D hrho hell ht hw⟩

end PHPMatchingEncodePathGeometryConcrete
end PvNP
