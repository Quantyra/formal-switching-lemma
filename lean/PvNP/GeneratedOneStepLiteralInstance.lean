import PvNP.GeneratedOneStepDepthReduction
import PvNP.RestrictionComposition

/-!
# S2231 Path B: concrete non-empty generated one-step consumer

This module gives a small non-empty, nontrivial consumer instance for the
existing `GeneratedOneStepInput` / `generatedOneStepDepthReduction_exists`
infrastructure: a singleton positive-literal DNF gate under an `or` parent.

It uses only the already-proved factor-4 generated one-step route and the
closed-form `restrictionsWithStars_card` count to discharge the strict beat at a
fixed ambient size.  It is not a general switching lemma and makes no
Frege/PHP/P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace GeneratedOneStepLiteralInstance

open BoundedDepthFrege
open BoundedDepthCanonicalDT
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open RestrictionComposition
open SwitchingLemmaStatement

/-- A concrete singleton positive-literal DNF layer under an `or` parent.  The
ambient size is fixed at ten variables so the closed-form star-space count gives
the strict factor-4 beat for `w = 1`, `s = 1`, `ℓ = 1`:
`4 * |R(10,0)| < |R(10,1)|`. -/
def singletonOneLitDNFOrInput : GeneratedOneStepInput 10 where
  layer := {
    parent := ParentKind.or
    gates := [GateSpec.dnf
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF 9))
      (oneLitDNFView 9)]
  }
  w := 1
  s := 1
  ℓ := 1
  width := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [GateSpec.theDNF, oneLitDNF, firstPosLit, widthDNF, termWidth]
  beat := by
    rw [restrictionsWithStars_card 10 0, restrictionsWithStars_card 10 1]
    norm_num

/-- Path-B non-empty, nontrivial generated one-step consumer instance: the
singleton one-literal DNF layer has a generated one-step certificate from the
existing `GeneratedOneStepInput` infrastructure and the closed-form
`restrictionsWithStars_card` beat. -/
theorem singletonOneLitDNFOr_nonvacuous :
    ∃ C : GeneratedOneStepCertificate singletonOneLitDNFOrInput,
      C.ρ ∈ restrictionsWithStars 10 1 ∧
      C.reducedChildren.length = 1 ∧
      depth C.reducedFormula ≤ 1 + (2 * (1 - 1) + 1) := by
  obtain ⟨C, hρ, _hsem, hcount, hdepth⟩ :=
    generatedOneStepDepthReduction_exists singletonOneLitDNFOrInput
  exact ⟨C, hρ, by simpa [singletonOneLitDNFOrInput] using hcount, hdepth⟩

/-- Summary pin for S2231 Path B: a concrete non-empty one-literal bottom gate
consumes the generated one-step depth-reduction theorem.  This is only a
one-step infrastructure instance, not a general switching lemma or lower-bound
claim. -/
theorem S2231_pathB_singletonOneLit_oneStepCertificate :
    ∃ C : GeneratedOneStepCertificate singletonOneLitDNFOrInput,
      C.ρ ∈ restrictionsWithStars 10 1 := by
  obtain ⟨C, hρ, _hcount, _hdepth⟩ := singletonOneLitDNFOr_nonvacuous
  exact ⟨C, hρ⟩

end GeneratedOneStepLiteralInstance
end PvNP
