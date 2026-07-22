import PvNP.PHPMatchingEncodePackageDenomCompare

/-!
# S2217: parametric encoded-bad ratio interface

This is a cardinal-ratio interface, not GA-4 injectivity into the side-bit
carrier.  It proves no switching lemma, Frege lower bound, P-vs-NP statement,
or `v0.11.0` result, and performs no residual-package grinding.  The concrete
`Fin 4` value `6/16` below is a **regression only**; the separate side-bit
factor-`4` bound is the ell-independent redesign target.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeParametricRatio

open Classical
open PHPMatchingCanonicalMDT
open PHPMatchingEncodePackageCount
open PHPMatchingEncodePackageDenomCompare

/-- Cross-multiplied ratio statement for an encoded bad image and an honest
finite reference space. -/
def EncodedBadRatioStatement {α β γ : Type*} [DecidableEq β]
    (bad : Finset α) (encode : α → β) (honest : Finset γ)
    (num den : Nat) : Prop :=
  den * (bad.image encode).card = num * honest.card

/-- Injectivity on the selected bad set transports an exact cardinal ratio to
the encoded image. -/
theorem encodedBadRatioStatement_of_injOn_card
    {α β γ : Type*} [DecidableEq β]
    (bad : Finset α) (encode : α → β) (honest : Finset γ)
    (num den : Nat) (hinj : Set.InjOn encode ↑bad)
    (hcard : den * bad.card = num * honest.card) :
    EncodedBadRatioStatement bad encode honest num den := by
  unfold EncodedBadRatioStatement
  rw [Finset.card_image_of_injOn hinj]
  exact hcard

/-- Fixed-package regression: the encoded bad image has ratio `6/16` against
the honest `Fin 4`, free-count-three space. -/
theorem searchD4mp_packageEncode_exact_ratio_six_sixteen :
    EncodedBadRatioStatement (Finset.univ : Finset (SearchD4mpBad 3))
      packageEncode (honestMatchingSpace 4 4 3) 6 16 := by
  apply encodedBadRatioStatement_of_injOn_card
  · exact packageEncode_injective.injOn
  · rw [show (Finset.univ : Finset (SearchD4mpBad 3)).card = 6 by
      simpa [SearchD4mpBad] using searchD4mp_exact_card_eq_six,
      honestMatchingSpace_four_four_three_card]

end PHPMatchingEncodeParametricRatio
end PvNP
