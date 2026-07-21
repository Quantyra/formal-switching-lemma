import PvNP.PHPMatchingEncodeAnswerAlphabet

/-!
# S2213: conditional ell-free answer alphabet on the length-at-most-two slice

The new residual asks only that equal `G1` and `G2` determine the first-block
path exit when the entered-term list has length two.  Under that residual,
`G3` is redundant and the honest-times-mcode grade bound extends from one to
two entered blocks.

This is conditional, not general GA-4 or unconditional length-two recovery.
It does not treat more than two blocks, and the package stop-loss remains in
force.  INTEGRITY: no `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeAnswerAlphabetLengthTwo

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingCodeBound
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeConditionalFiber
open PHPMatchingEncodeAnswerRedesign
open PHPMatchingEncodeAnswerAlphabet

/-- The precise new S2213 residual: on a genuine length-two encode image,
`G1` and `G2` alone determine the first-block walked-pair path exit. -/
def EncodeMatchG1G2LengthTwoPathExitEqResidual
    {p h w t ell : Nat} (hsq : p = h)
    (D : MDNF p h) (hw : ∀ term ∈ D, term.length ≤ w) : Prop :=
  ∀ (rho₁ rho₂ : MatchingMap p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂)),
    (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 →
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 →
        (enteredTermsOf rho₁ D t).length = 2 →
          firstBlockPathExitMatching rho₁ D t =
            firstBlockPathExitMatching rho₂ D t

/-- Equal `G1`, `G2`, and path exits recover both entries of a length-two
entered-term list.  This proof does not use equality of the full code. -/
theorem enteredTermsOf_eq_of_G1_G2_eq_of_length_two_of_pathExit_eq
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
    (hlen : (enteredTermsOf rho₁ D t).length = 2)
    (hexit : firstBlockPathExitMatching rho₁ D t =
      firstBlockPathExitMatching rho₂ D t) :
    enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
  have hlen₂ : (enteredTermsOf rho₂ D t).length = 2 := by
    calc
      (enteredTermsOf rho₂ D t).length =
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2.length :=
        enteredTermsOf_length_eq_G2 hsq rho₂ D hrho₂ hell₂ ht₂ hw
      _ = (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2.length := by rw [hG2]
      _ = (enteredTermsOf rho₁ D t).length :=
        (enteredTermsOf_length_eq_G2 hsq rho₁ D hrho₁ hell₁ ht₁ hw).symm
      _ = 2 := hlen
  have hne₁ : enteredTermsOf rho₁ D t ≠ [] := by
    intro h; rw [h] at hlen; cases hlen
  have hne₂ : enteredTermsOf rho₂ D t ≠ [] := by
    intro h; rw [h] at hlen₂; cases hlen₂
  rcases List.exists_cons_of_ne_nil hne₁ with ⟨T₁, r₁, hc₁⟩
  rcases List.exists_cons_of_ne_nil hne₂ with ⟨T₂, r₂, hc₂⟩
  have hr₁_ne : r₁ ≠ [] := by
    intro hr
    have : (T₁ :: r₁).length = 2 := by simpa [hc₁] using hlen
    simp only [hr, List.length_cons, List.length_nil] at this
    cases this
  have hr₂_ne : r₂ ≠ [] := by
    intro hr
    have : (T₂ :: r₂).length = 2 := by simpa [hc₂] using hlen₂
    simp only [hr, List.length_cons, List.length_nil] at this
    cases this
  rcases List.exists_cons_of_ne_nil hr₁_ne with ⟨U₁, s₁, hr₁⟩
  rcases List.exists_cons_of_ne_nil hr₂_ne with ⟨U₂, s₂, hr₂⟩
  have hs₁ : s₁ = [] := by
    apply List.eq_nil_of_length_eq_zero
    have : (T₁ :: U₁ :: s₁).length = 2 := by
      simpa [hc₁, hr₁] using hlen
    simp only [List.length_cons] at this
    omega
  have hs₂ : s₂ = [] := by
    apply List.eq_nil_of_length_eq_zero
    have : (T₂ :: U₂ :: s₂).length = 2 := by
      simpa [hc₂, hr₂] using hlen₂
    simp only [List.length_cons] at this
    omega
  have hscan₁ := enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq
    rho₁ D hrho₁ hell₁ ht₁ hw T₁ (U₁ :: s₁) (by simpa [hr₁] using hc₁)
  have hscan₂ := enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq
    rho₂ D hrho₂ hell₂ ht₂ hw T₂ (U₂ :: s₂) (by simpa [hr₂] using hc₂)
  have hT : T₁ = T₂ := by
    apply Option.some.inj
    calc
      some T₁ = firstNotFalsifiedTerm
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 D := hscan₁.symm
      _ = firstNotFalsifiedTerm
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 D := by rw [hG1]
      _ = some T₂ := hscan₂
  have hsecond₁ := enteredTermsOf_second_eq_firstNotFalsified_pathExit hsq
    rho₁ D hrho₁ hell₁ ht₁ hw T₁ U₁ s₁ (by simpa [hr₁, hs₁] using hc₁)
  have hsecond₂ := enteredTermsOf_second_eq_firstNotFalsified_pathExit hsq
    rho₂ D hrho₂ hell₂ ht₂ hw T₂ U₂ s₂ (by simpa [hr₂, hs₂] using hc₂)
  have hU : U₁ = U₂ := by
    apply Option.some.inj
    calc
      some U₁ = firstNotFalsifiedTerm (firstBlockPathExitMatching rho₁ D t) D :=
        hsecond₁.symm
      _ = firstNotFalsifiedTerm (firstBlockPathExitMatching rho₂ D t) D := by
        rw [hexit]
      _ = some U₂ := hsecond₂
  rw [hc₁, hc₂, hr₁, hr₂, hs₁, hs₂, hT, hU]

/-- The S2213 residual extends entered-term recovery from length at most one
to length at most two. -/
theorem enteredTermsOf_eq_of_G1_G2_eq_of_length_le_two_of_pathExitResidual
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hexit : EncodeMatchG1G2LengthTwoPathExitEqResidual (t := t) (ell := ell) hsq D hw)
    (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
    (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
    (hlen : (enteredTermsOf rho₁ D t).length ≤ 2) :
    enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
  by_cases hle : (enteredTermsOf rho₁ D t).length ≤ 1
  · exact enteredTermsOf_eq_of_G1_G2_eq_of_length_le_one hsq rho₁ rho₂ D
      hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 hle
  · have htwo : (enteredTermsOf rho₁ D t).length = 2 := by omega
    exact enteredTermsOf_eq_of_G1_G2_eq_of_length_two_of_pathExit_eq hsq
      rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 htwo
      (hexit rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hG1 hG2 htwo)

/-- Under the path-exit residual, `G3` is redundant on length-at-most-two
encode images. -/
theorem encodeMatch_G3_eq_of_G1_G2_eq_of_length_le_two_of_pathExitResidual
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hexit : EncodeMatchG1G2LengthTwoPathExitEqResidual (t := t) (ell := ell) hsq D hw)
    (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
    (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
    (hlen : (enteredTermsOf rho₁ D t).length ≤ 2) :
    (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G3 =
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G3 := by
  have hterms :=
    enteredTermsOf_eq_of_G1_G2_eq_of_length_le_two_of_pathExitResidual hsq
      rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hexit hG1 hG2 hlen
  have hrho := base_eq_of_G1_G2_eq_of_enteredTerms_eq hsq rho₁ rho₂ D
    hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hG1 hG2 hterms
  subst rho₂
  rfl

def atMostTwoBlockGradeDomain {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat) :
    Finset (BadEncodeDomain h t ell D) :=
  Finset.univ.filter fun rho =>
    (enteredTermsOf rho.1 D t).length ≤ 2 ∧ (badEncode hw rho).j = j

/-- Conditional `(G1,G2)` injectivity on each at-most-two-block grade. -/
theorem badEncode_G1G2_injOn_atMostTwoBlockGrade
    {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat)
    (hexit : EncodeMatchG1G2LengthTwoPathExitEqResidual (t := t) (ell := ell) rfl D hw) :
    Set.InjOn (fun rho : BadEncodeDomain h t ell D =>
      ((badEncode hw rho).G1, (badEncode hw rho).G2))
      (↑(atMostTwoBlockGradeDomain (t := t) (ell := ell) D hw j) :
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
  · apply enteredTermsOf_eq_of_G1_G2_eq_of_length_le_two_of_pathExitResidual
      rfl rho.1 rho'.1 D hmem.1.1 hmem'.1.1 hmem.1.2 hmem'.1.2 ht ht' hw hexit
    · simpa [badEncode, hmem, hmem', ht, ht'] using hG1
    · simpa [badEncode, hmem, hmem', ht, ht'] using hG2
    · exact hdata.1

/-- Honest-times-mcode count for an at-most-two entered-block grade,
conditional only on the S2213 path-exit residual. -/
theorem atMostTwoBlockGradeDomain_card_le
    {h w t ell : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat)
    (hexit : EncodeMatchG1G2LengthTwoPathExitEqResidual (t := t) (ell := ell) rfl D hw) :
    (atMostTwoBlockGradeDomain (t := t) (ell := ell) D hw j).card ≤
      (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  let A := atMostTwoBlockGradeDomain (t := t) (ell := ell) D hw j
  let f : BadEncodeDomain h t ell D → MatchingMap h h × List (Finset (Fin w)) :=
    fun rho => ((badEncode hw rho).G1, (badEncode hw rho).G2)
  let S := A.image f
  have hinj : Set.InjOn f (↑A : Set (BadEncodeDomain h t ell D)) := by
    simpa [A, f] using badEncode_G1G2_injOn_atMostTwoBlockGrade D hw j hexit
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

/-- S2213 summary: the at-most-two grade bound and `G3` redundancy are both
conditional on the new `G1`/`G2` length-two path-exit residual. -/
theorem answer_alphabet_s2213_summary :
    (∀ {h w t ell : Nat} (D : MDNF h h)
      (hw : ∀ term ∈ D, term.length ≤ w) (j : Nat),
      EncodeMatchG1G2LengthTwoPathExitEqResidual (t := t) (ell := ell) rfl D hw →
        (atMostTwoBlockGradeDomain (t := t) (ell := ell) D hw j).card ≤
          (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j) ∧
    (∀ {p h w t ell : Nat} (hsq : p = h)
      (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
      (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
      (hell₁ : (freePigeons rho₁).card = ell)
      (hell₂ : (freePigeons rho₂).card = ell)
      (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
      (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
      (hw : ∀ term ∈ D, term.length ≤ w)
      (hexit : EncodeMatchG1G2LengthTwoPathExitEqResidual (t := t) (ell := ell) hsq D hw)
      (hG1 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1)
      (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2)
      (hlen : (enteredTermsOf rho₁ D t).length ≤ 2),
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G3 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G3) :=
  ⟨fun D hw j hexit => atMostTwoBlockGradeDomain_card_le D hw j hexit,
    fun hsq rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hexit hG1 hG2 hlen =>
      encodeMatch_G3_eq_of_G1_G2_eq_of_length_le_two_of_pathExitResidual hsq
        rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hexit hG1 hG2 hlen⟩

end PHPMatchingEncodeAnswerAlphabetLengthTwo
end PvNP
