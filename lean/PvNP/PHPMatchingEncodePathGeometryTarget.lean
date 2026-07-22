import PvNP.PHPMatchingEncodeSideBitForceFreeze
import PvNP.PHPMatchingEncodeParametricRatio

/-!
# S2221: packet-native path-geometry force pivot target

After S2220 stop-lossed side-bit product counting for force, the next force
lane is a **packet-native path-geometry / coupled walked-pair** encode:

- path geometry lives in the packet (no free `Fin t → _` stream tax)
- no side-bit `Bool^t` / extra `4^j` product tax (S2220 freeze)
- no residual unique-preimage grind (S2216 freeze)
- Fin4 exact `6/16` remains regression-only force oracle
- S2214 `H·4^j` remains best package product upper bound (still TRIVIAL)

This module pins the **target shape and force gate** only.  It does not
recover walked pairs, prove a new counting bound, claim general GA-4,
switching, P-vs-NP, or `v0.11.0`.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
-/

namespace PvNP
namespace PHPMatchingEncodePathGeometryTarget

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodePackageCount
open PHPMatchingEncodePackageDenomCompare
open PHPMatchingEncodeAnswerAlphabetLengthTwoPackage
open PHPMatchingEncodeParametricRatio
open PHPMatchingEncodeSideBitForceFreeze
open PHPMatchingEncodeSideBitPackage

/-- Target packet shape after the side-bit stop-loss: G1 extension together
with a walked-pair / path-geometry certificate.  The certificate type is
parametric so later stories can instantiate a concrete code without
reopening a free answer stream. -/
structure PathGeometryPacket (p h : Nat) (PairCode : Type*) where
  G1 : MatchingMap p h
  pathCode : PairCode

/-- Abstract grade target without side-bit tax and without `(2 * ell) ^ t`.
A later force proof must beat honest denom under a bound of this shape for
some fixed base `C` independent of `ell` and `t`. -/
def PathGeometryGradeTarget (H C j bound : Nat) : Prop :=
  bound ≤ H * C ^ j

/-- Force gate: encoded-bad ratio is force-grade only when the realized
numerator is strictly below the honest denominator. -/
def PathGeometryForceGate {α β γ : Type*} [DecidableEq β]
    (bad : Finset α) (encode : α → β) (honest : Finset γ)
    (num den : Nat) : Prop :=
  EncodedBadRatioStatement bad encode honest num den ∧ num < den

/-- Fixed-package regression: exact package encode already meets the force
gate at ratio `6/16`.  This is oracle infrastructure only. -/
theorem path_geometry_force_gate_exact_six_sixteen :
    PathGeometryForceGate (Finset.univ : Finset (SearchD4mpBad 3))
      packageEncode (honestMatchingSpace 4 4 3) 6 16 := by
  refine ⟨searchD4mp_packageEncode_exact_ratio_six_sixteen, ?_⟩
  decide

/-- Abstract target shape is inhabited at the trivial parameters. -/
theorem path_geometry_grade_target_unit :
    PathGeometryGradeTarget 1 1 0 1 := by
  simp [PathGeometryGradeTarget]

/-- S2221 pivot pin: side-bit freeze still holds; product bound is TRIVIAL;
exact card is STRICT and meets the path-geometry force gate; abstract grade
target shape is available without side-bit tax. -/
theorem path_geometry_pivot_s2221_summary :
    (∀ ell j, (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) ∧
    (∀ ell j, (badGrade ell j).card ≤
      (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j) ∧
    (vbadMatchings searchD4mp 2 3).card ≤ 3072 ∧
    (honestMatchingSpace 4 4 3).card < 3072 ∧
    (vbadMatchings searchD4mp 2 3).card = 6 ∧
    6 < (honestMatchingSpace 4 4 3).card ∧
    PathGeometryForceGate (Finset.univ : Finset (SearchD4mpBad 3))
      packageEncode (honestMatchingSpace 4 4 3) 6 16 ∧
    PathGeometryGradeTarget 1 1 0 1 := by
  exact ⟨badGrade_searchD4mp_G1G2_card_le,
    badGrade_searchD4mp_sidebit_card_le,
    vbadMatchings_searchD4mp_two_three_card_le_ell_free,
    searchD4mp_ell_free_bound_exceeds_denominator,
    searchD4mp_exact_card_eq_six,
    (by simpa [searchD4mp_exact_card_eq_six] using
      searchD4mp_exact_card_strict_denominator),
    path_geometry_force_gate_exact_six_sixteen,
    path_geometry_grade_target_unit⟩

end PHPMatchingEncodePathGeometryTarget
end PvNP
