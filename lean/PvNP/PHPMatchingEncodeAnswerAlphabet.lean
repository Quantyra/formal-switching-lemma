import PvNP.PHPMatchingEncodeAnswerRedesign

/-!
# S2212: ell-free answer alphabet on the at-most-one entered-block slice

This module proves that `G1` and `G2` already determine the old `G3` on
encode images with at most one entered block, and derives the corresponding
honest-times-mcode grade bound.

The Fin4 cardinality `6` is oracle only; this slice does not scale that `6`.
This is not general GA-4, not general `G3` elimination, and not v0.11.0.  The
package stop-loss remains in force outside this slice.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeAnswerAlphabet

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingCodeBound
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeAnswerRedesign

/-- The base-recovery part of conditional injectivity uses only `G1`, `G2`,
and equality of the entered-term lists; `G3` is irrelevant. -/
theorem base_eq_of_G1_G2_eq_of_enteredTerms_eq
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
    (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
    (hterms : enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t) :
    rho₁ = rho₂ := by
  funext i
  have hr₁ := encodeMatch_decodeBasePoint_from_terms hsq rho₁ D hrho₁
    hell₁ ht₁ hw i
  have hr₂ := encodeMatch_decodeBasePoint_from_terms hsq rho₂ D hrho₂
    hell₂ ht₂ hw i
  calc
    rho₁ i = decodeBasePoint
        (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1
        (decodeSigmaOverlay (enteredTermsOf rho₁ D t)
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2) i := by
      simpa [enteredTermsOf] using hr₁.symm
    _ = decodeBasePoint
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1
        (decodeSigmaOverlay (enteredTermsOf rho₂ D t)
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2) i := by
      rw [hG1, hG2, hterms]
    _ = rho₂ i := by simpa [enteredTermsOf] using hr₂

/-- On the at-most-one-block slice, the common `G1` supplies the only possible
head and the common `G2` supplies the list length. -/
theorem enteredTermsOf_eq_of_G1_G2_eq_of_length_le_one
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
    (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
    (hlen : (enteredTermsOf rho₁ D t).length ≤ 1) :
    enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
  have hlenEq : (enteredTermsOf rho₁ D t).length =
      (enteredTermsOf rho₂ D t).length := by
    calc
      (enteredTermsOf rho₁ D t).length =
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2.length :=
        enteredTermsOf_length_eq_G2 hsq rho₁ D hrho₁ hell₁ ht₁ hw
      _ = (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2.length := by rw [hG2]
      _ = (enteredTermsOf rho₂ D t).length :=
        (enteredTermsOf_length_eq_G2 hsq rho₂ D hrho₂ hell₂ ht₂ hw).symm
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hlen with hzero | hone
  · exact (List.eq_nil_of_length_eq_zero hzero).trans
      (List.eq_nil_of_length_eq_zero (hlenEq ▸ hzero)).symm
  · have hne₁ : enteredTermsOf rho₁ D t ≠ [] := by
      intro hnil
      rw [hnil] at hone
      cases hone
    rcases List.exists_cons_of_ne_nil hne₁ with ⟨T₁, r₁, hc₁⟩
    have hone₂ : (enteredTermsOf rho₂ D t).length = 1 := hlenEq.symm.trans hone
    have hne₂ : enteredTermsOf rho₂ D t ≠ [] := by
      intro hnil
      rw [hnil] at hone₂
      cases hone₂
    rcases List.exists_cons_of_ne_nil hne₂ with ⟨T₂, r₂, hc₂⟩
    have hscan₁ := enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq
      rho₁ D hrho₁ hell₁ ht₁ hw T₁ r₁ hc₁
    have hscan₂ := enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq
      rho₂ D hrho₂ hell₂ ht₂ hw T₂ r₂ hc₂
    have hT : T₁ = T₂ := by
      apply Option.some.inj
      calc
        some T₁ = firstNotFalsifiedTerm
            (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 D := hscan₁.symm
        _ = firstNotFalsifiedTerm
            (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 D := by rw [hG1]
        _ = some T₂ := hscan₂
    have hr₁ : r₁ = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlencons : (T₁ :: r₁).length = 1 := by rw [← hc₁]; exact hone
      simp only [List.length_cons] at hlencons
      omega
    have hr₂ : r₂ = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hlencons : (T₂ :: r₂).length = 1 := by rw [← hc₂]; exact hone₂
      simp only [List.length_cons] at hlencons
      omega
    rw [hc₁, hc₂, hr₁, hr₂, hT]

/-- The old answer component is redundant on at-most-one-block encode images:
equal `G1` and `G2` force equal bases and hence equal `G3`. -/
theorem encodeMatch_G3_eq_of_G1_G2_eq_of_length_le_one
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
    (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
    (hlen : (enteredTermsOf rho₁ D t).length ≤ 1) :
    (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G3 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G3 := by
  have hterms := enteredTermsOf_eq_of_G1_G2_eq_of_length_le_one hsq
    rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 hlen
  have hrho := base_eq_of_G1_G2_eq_of_enteredTerms_eq hsq rho₁ rho₂ D
    hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 hterms
  subst rho₂
  rfl

def atMostOneBlockGradeDomain {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho =>
    (enteredTermsOf rho.1 D t).length ≤ 1 ∧ (badEncode hw rho).j = j

/-- `(G1,G2)` is injective on each at-most-one-block grade. -/
theorem badEncode_G1G2_injOn_atMostOneBlockGrade
    {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Set.InjOn (fun rho : BadEncodeDomain h t ell D =>
      ((badEncode hw rho).G1, (badEncode hw rho).G2))
      (↑(atMostOneBlockGradeDomain (t := t) (ell := ell) D hw j) :
        Set (BadEncodeDomain h t ell D)) := by
  intro rho hrho rho' hrho' heq
  apply Subtype.ext
  let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
  let hmem' := (mem_vbadMatchings D (t - 1) ell rho'.1).mp rho'.2
  let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
  let ht' : t ≤ vmdtDepth (canonicalVMDT D rho'.1) := Nat.le_of_pred_lt hmem'.2
  have hdata := (Finset.mem_filter.mp hrho).2
  have hG1 : (badEncode hw rho).G1 = (badEncode hw rho').G1 := congrArg Prod.fst heq
  have hG2 : (badEncode hw rho).G2 = (badEncode hw rho').G2 := congrArg Prod.snd heq
  apply base_eq_of_G1_G2_eq_of_enteredTerms_eq rfl rho.1 rho'.1 D
    hmem.1.1 hmem'.1.1 hmem.1.2 hmem'.1.2 ht ht' hw
  · simpa [badEncode, hmem, hmem', ht, ht'] using hG1
  · simpa [badEncode, hmem, hmem', ht, ht'] using hG2
  · apply enteredTermsOf_eq_of_G1_G2_eq_of_length_le_one rfl rho.1 rho'.1 D
      hmem.1.1 hmem'.1.1 hmem.1.2 hmem'.1.2 ht ht' hw
    · simpa [badEncode, hmem, hmem', ht, ht'] using hG1
    · simpa [badEncode, hmem, hmem', ht, ht'] using hG2
    · exact hdata.1

/-- Honest-times-mcode count for the at-most-one entered-block grade. -/
theorem atMostOneBlockGradeDomain_card_le
    {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    (atMostOneBlockGradeDomain (t := t) (ell := ell) D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  let A := atMostOneBlockGradeDomain (t := t) (ell := ell) D hw j
  let f : BadEncodeDomain h t ell D → MatchingMap h h × List (Finset (Fin w)) :=
    fun rho => ((badEncode hw rho).G1, (badEncode hw rho).G2)
  let S := A.image f
  have hinj : Set.InjOn f (↑A : Set (BadEncodeDomain h t ell D)) := by
    simpa [A, f] using badEncode_G1G2_injOn_atMostOneBlockGrade D hw j
  have hG1 : ∀ p ∈ S, p.1 ∈ honestMatchingSpace h h (ell - j) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    exact badEncode_G1_mem_honest hw rho (Finset.mem_filter.mp hrho).2.2
  have hgraded : ∀ p ∈ S,
      (∀ b ∈ p.2, Finset.Nonempty b) ∧ codeSize p.2 = j := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨rho, hrho, rfl⟩
    let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) := Nat.le_of_pred_lt hmem.2
    have hgrade := encodeMatch_mem_gradedCode rho.1 D hmem.1.1 hmem.1.2 rfl ht hw
    have hj := (Finset.mem_filter.mp hrho).2.2
    have hgrade' :
        (∀ b ∈ (badEncode hw rho).G2, Finset.Nonempty b) ∧
          codeSize (badEncode hw rho).G2 = (badEncode hw rho).j := by
      simpa [badEncode, hmem, ht] using hgrade
    exact ⟨hgrade'.1, hgrade'.2.trans hj⟩
  calc
    A.card = S.card := by
      symm
      exact Finset.card_image_of_injOn hinj
    _ ≤ (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j :=
      mcode_only_grade_card_le_of_g1g2_inj S hG1
        (fun p hp => (hgraded p hp).1) (fun p hp => (hgraded p hp).2)
        (fun _ _ _ _ h => h)

/-- S2212 summary: `G3` redundancy and the resulting grade bound, both only
on the at-most-one entered-block slice. -/
theorem answer_alphabet_s2212_summary :
    (∀ {h w t ell : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat),
      (atMostOneBlockGradeDomain (t := t) (ell := ell) D hw j).card ≤
        (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j) ∧
    (∀ {p h w t ell : Nat} (hsq : p = h)
      (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
      (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
      (hell₁ : (freePigeons rho₁).card = ell)
      (hell₂ : (freePigeons rho₂).card = ell)
      (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
      (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
      (hw : ∀ term ∈ D, term.length ≤ w)
      (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
      (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
      (hlen : (enteredTermsOf rho₁ D t).length ≤ 1),
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G3 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G3) :=
  ⟨atMostOneBlockGradeDomain_card_le,
    fun hsq rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 hlen =>
      encodeMatch_G3_eq_of_G1_G2_eq_of_length_le_one hsq rho₁ rho₂ D
        hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 hlen⟩

end PHPMatchingEncodeAnswerAlphabet
end PvNP
