/-
# Beame/Håstad counting-form depth-2 switching alignment shell for v0

This module is a route pin / Beame alignment shell, not a re-proof. It names the
already-landed simple-DNF term-canonical counting theorem from the existing
switching stack:

* `SwitchingLemmaStatement` supplies the general DNF counting framework and the
  isolated `SwitchingLemma : Nat → Prop` residual.
* `SwitchingEncodeConstruct` supplies `SwitchingLemmaTermSimple`, the simple-DNF
  term-canonical counting form.
* `SwitchingClose2.switchingLemmaTermSimple_proved` is the landed theorem reused
  here verbatim.

NON-CLAIMS: this is not an AC0 lower bound, not the general Håstad multi-layer
switching lemma, not a Frege/PHP result, not `P ≠ NP`, and not a `v0.11.0`
release closure. The general DNF residual is named below only as a `Prop`; it is
not inhabited here.
-/
import PvNP.SwitchingLemmaStatement
import PvNP.SwitchingEncodeConstruct
import PvNP.SwitchingClose2

namespace PvNP
namespace SwitchingCoreV0Shell

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingEncodeConstruct

/--
Beame/Håstad-style counting form for simple depth-2 DNFs, in the already-proved
term-canonical formulation:

`# badSetTerm(D, s, ℓ) ≤ # restrictionsWithStars(ℓ - s) * (8w)^s`, assuming
`SimpleDNF D` and `widthDNF D ≤ w`.

This is definitionally the existing `SwitchingLemmaTermSimple`; no new theorem is
being asserted by the abbreviation.
-/
abbrev BeameHastadCountingSwitchingForm (n : Nat) : Prop :=
  SwitchingLemmaTermSimple n

/-- The Beame/Håstad-style simple-DNF counting form is landed by the existing
`SwitchingClose2.switchingLemmaTermSimple_proved` theorem. -/
theorem beame_hastad_counting_form_landed (n : Nat) :
    BeameHastadCountingSwitchingForm n :=
  SwitchingClose2.switchingLemmaTermSimple_proved (n := n)

/--
Name for the general DNF switching residual. This is the existing general
`SwitchingLemma` statement from `SwitchingLemmaStatement`, not restricted to
`SimpleDNF`. It remains an unproved residual `Prop` here: this module does not
produce a term of `GeneralDNFSwitchingLemmaResidual n`.
-/
abbrev GeneralDNFSwitchingLemmaResidual (n : Nat) : Prop :=
  SwitchingLemma n

/--
S2230 route summary: the simple-DNF Beame/Håstad-style counting form has landed.
The general residual is documented by the name
`GeneralDNFSwitchingLemmaResidual`; it is not inhabited by this summary.
-/
theorem switching_core_v0_s2230_summary (n : Nat) :
    BeameHastadCountingSwitchingForm n ∧ True :=
  ⟨beame_hastad_counting_form_landed n, True.intro⟩

end SwitchingCoreV0Shell
end PvNP
