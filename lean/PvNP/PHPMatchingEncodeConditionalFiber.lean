import PvNP.PHPMatchingEncodeInjectivity

/-!
# S2210: uniform conditional fibers (weak, honest)

This module proves only uniform structural fiber bounds for the deterministic
matching encode.  The entered-payload bound conditions on the entered terms;
the payload-only bound additionally assumes the existing entered-term
residual.

The S2209 `Fin 4` cardinality `6` is oracle only; this lemma does not scale
that `6`.  In particular, this is not a proof of the general entered residual,
general GA-4 injectivity, asymptotic switching, or a useful bound on `|vbad|`.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeConditionalFiber

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity

abbrev BadEncodeDomain (h t ell : Nat) (D : MDNF h h) :=
  {rho : MatchingMap h h // rho ∈ vbadMatchings D (t - 1) ell}

def badEncode {h w t ell : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D) : MatchEncode h h w t ell :=
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  encodeMatch (p := h) (h := h) (w := w) (t := t) (ell := ell) rfl
    rho.1 D hmem.1.1 hmem.1.2 ht hw

theorem badEncode_G1_mem_honest {h w t ell j : Nat} {D : MDNF h h}
    (hw : ∀ term ∈ D, term.length ≤ w)
    (rho : BadEncodeDomain h t ell D)
    (hj : (badEncode hw rho).j = j) :
    (badEncode hw rho).G1 ∈ honestMatchingSpace h h (ell - j) := by
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  rw [mem_honestMatchingSpace]
  constructor
  · simpa [badEncode, hmem, ht, encodeMatch] using
      encodeExt_isMatching rho.1 D (leftmostLiveDeepFeed rho.1 D t) hmem.1.1
  · have hfree := encodeMatch_freePigeons_card (w := w) (t := t) rfl rho.1
      D hmem.1.1 hmem.1.2 ht hw
    have hfree' : (freePigeons (badEncode hw rho).G1).card =
        ell - (badEncode hw rho).j := by
      simpa [badEncode] using hfree
    rw [hj] at hfree'
    exact hfree'

def enteredPayloadFiber {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (terms : List (MTerm h h)) (G2 : List (Finset (Fin w)))
    (G3 : Fin t → Fin (2 * ell)) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho =>
    enteredTermsOf rho.1 D t = terms ∧
      (badEncode hw rho).G2 = G2 ∧
      (badEncode hw rho).G3 = G3 ∧
      (badEncode hw rho).j = j

theorem enteredPayloadFiber_card_le {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (terms : List (MTerm h h)) (G2 : List (Finset (Fin w)))
    (G3 : Fin t → Fin (2 * ell)) (j : Nat) :
    (enteredPayloadFiber D hw terms G2 G3 j).card ≤
      (honestMatchingSpace h h (ell - j)).card := by
  let f : BadEncodeDomain h t ell D → MatchingMap h h :=
    fun rho => (badEncode hw rho).G1
  have hmap : ∀ rho ∈ enteredPayloadFiber D hw terms G2 G3 j,
      f rho ∈ honestMatchingSpace h h (ell - j) := by
    intro rho hrho
    exact badEncode_G1_mem_honest hw rho
      (Finset.mem_filter.mp hrho).2.2.2.2
  have hinj : Set.InjOn f
      (↑(enteredPayloadFiber D hw terms G2 G3 j) :
        Set (BadEncodeDomain h t ell D)) := by
    intro rho hrho rho' hrho' heq
    have hdata := (Finset.mem_filter.mp hrho).2
    have hdata' := (Finset.mem_filter.mp hrho').2
    apply Subtype.ext
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let hmem' := (mem_vbadMatchings D (t - 1) ell rho'.1).mp rho'.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    let ht' : t ≤ vmdtDepth (canonicalVMDT D rho'.1) := Nat.le_of_pred_lt hmem'.2
    dsimp only [f] at heq
    have hcode : badEncode hw rho = badEncode hw rho' := by
      cases hcode : badEncode hw rho with
      | mk G1 G2' G3' k =>
        cases hcode' : badEncode hw rho' with
        | mk G1' G2'' G3'' k' =>
          simp only [hcode, hcode'] at heq hdata hdata' ⊢
          simp_all
    apply encodeMatch_eq_of_code_eq_of_entered_terms_eq rfl rho.1 rho'.1 D
      hmem.1.1 hmem'.1.1 hmem.1.2 hmem'.1.2 ht ht' hw
    · simpa [badEncode, hmem, hmem', ht, ht'] using hcode
    · exact hdata.1.trans hdata'.1.symm
  exact Finset.card_le_card_of_injOn f hmap hinj

def payloadFiber {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (G2 : List (Finset (Fin w))) (G3 : Fin t → Fin (2 * ell)) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho =>
    (badEncode hw rho).G2 = G2 ∧
      (badEncode hw rho).G3 = G3 ∧
      (badEncode hw rho).j = j

theorem payloadFiber_card_le_of_enteredTermsEqResidual
    {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (G2 : List (Finset (Fin w))) (G3 : Fin t → Fin (2 * ell)) (j : Nat)
    (hres : EncodeMatchEnteredTermsEqResidual (t := t) (ell := ell) (w := w)
      rfl D hw) :
    (payloadFiber D hw G2 G3 j).card ≤
      (honestMatchingSpace h h (ell - j)).card := by
  let f : BadEncodeDomain h t ell D → MatchingMap h h :=
    fun rho => (badEncode hw rho).G1
  have hmap : ∀ rho ∈ payloadFiber D hw G2 G3 j,
      f rho ∈ honestMatchingSpace h h (ell - j) := by
    intro rho hrho
    exact badEncode_G1_mem_honest hw rho
      (Finset.mem_filter.mp hrho).2.2.2
  have hinj : Set.InjOn f
      (↑(payloadFiber D hw G2 G3 j) : Set (BadEncodeDomain h t ell D)) := by
    intro rho hrho rho' hrho' heq
    have hdata := (Finset.mem_filter.mp hrho).2
    have hdata' := (Finset.mem_filter.mp hrho').2
    dsimp only [f] at heq
    have hcode : badEncode hw rho = badEncode hw rho' := by
      cases hcode : badEncode hw rho with
      | mk G1 G2' G3' k =>
        cases hcode' : badEncode hw rho' with
        | mk G1' G2'' G3'' k' =>
          simp only [hcode, hcode'] at heq hdata hdata' ⊢
          simp_all
    apply encodeMatch_subtype_injective_of_enteredTermsEqResidual rfl D hw hres
    exact hcode
  exact Finset.card_le_card_of_injOn f hmap hinj

theorem conditional_fiber_uniform_summary
    {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (terms : List (MTerm h h))
    (G2 : List (Finset (Fin w)))
    (G3 : Fin t → Fin (2 * ell))
    (j : Nat) :
    (enteredPayloadFiber D hw terms G2 G3 j).card ≤
      (honestMatchingSpace h h (ell - j)).card :=
  enteredPayloadFiber_card_le D hw terms G2 G3 j

end PHPMatchingEncodeConditionalFiber
end PvNP
