import PvNP.GeneratedOneStepDepthReduction
import PvNP.RestrictionSpaceCard

/-!
# S2232-B2: two-gate generated one-step consumer instance

This module gives a small richer generated one-step infrastructure consumer:
two distinct one-literal positive DNF gates, on variables `0` and `1`, under an
`or` parent at ambient size `17`.

It uses only the already-proved factor-4 generated one-step route and the
closed-form `restrictionsWithStars_card` count to discharge the strict beat
`2 * |R(17,0)| * 4^1 < |R(17,1)|`.  It is not a general switching lemma, not a
Frege/PHP/P-vs-NP claim, not `v0.11.0`, and not Gate A.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace GeneratedOneStepTwoGateInstance

open CNFModel
open BoundedDepthFrege
open BoundedDepthCanonicalDT
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open RestrictionSpaceCard
open SwitchingLemmaStatement

private theorem oneLitDNF_width_16 : widthDNF (oneLitDNF 16) ≤ 1 := by
  decide

/-- The second variable of the ambient seventeen-variable space, as a positive literal. -/
def secondPosLit17 : Literal 17 :=
  { var := ⟨1, by decide⟩, sign := true }

/-- The singleton positive-literal DNF on variable `1` over seventeen variables. -/
def oneLitDNFVar1Seventeen : DNF 17 := [[secondPosLit17]]

private theorem oneLitDNFVar1Seventeen_simple :
    SwitchingEncodeConstruct.SimpleDNF oneLitDNFVar1Seventeen := by
  intro t ht
  have ht' : t = [secondPosLit17] := by simpa [oneLitDNFVar1Seventeen] using ht
  subst t
  simp [SwitchingEncodeConstruct.SimpleTerm]

private theorem oneLitDNFVar1Seventeen_width : widthDNF oneLitDNFVar1Seventeen ≤ 1 := by
  decide

private theorem restrictionsWithStars_17_beat :
    2 * ((restrictionsWithStars 17 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 17 1).card := by
  have h0 : (restrictionsWithStars 17 0).card = 131072 := by
    rw [restrictionsWithStars_card 17 0]
    decide
  have h1 : (restrictionsWithStars 17 1).card = 1114112 := by
    rw [restrictionsWithStars_card 17 1]
    decide
  rw [show 1 - 1 = 0 by rfl, h0, h1]
  decide

/-- The concrete positive-literal DNF gate on variable `0`. -/
def oneLitVar0DNFGate17 : GateSpec 17 :=
  GateSpec.dnf
    (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF 16))
    (oneLitDNFView 16)

/-- The concrete positive-literal DNF gate on variable `1`. -/
def oneLitVar1DNFGate17 : GateSpec 17 :=
  GateSpec.dnf
    (BoundedDepthFregeSwitchingBridge.dnfToBD oneLitDNFVar1Seventeen)
    (BoundedDepthLayerView.dnfToBD_dnfView oneLitDNFVar1Seventeen oneLitDNFVar1Seventeen_simple)

private theorem oneLitVar0DNFGate17_width :
    widthDNF oneLitVar0DNFGate17.theDNF ≤ 1 := by
  exact oneLitDNF_width_16

private theorem oneLitVar1DNFGate17_width :
    widthDNF oneLitVar1DNFGate17.theDNF ≤ 1 := by
  exact oneLitDNFVar1Seventeen_width

/-- The concrete two-gate one-literal DNF layer under an `or` parent. -/
def twoGateOneLitOrLayer : MinimalLayeredFormula 17 where
  parent := ParentKind.or
  gates := [oneLitVar0DNFGate17, oneLitVar1DNFGate17]

private theorem twoGateOneLitOrLayer_beat :
    twoGateOneLitOrLayer.gates.length *
        ((restrictionsWithStars 17 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 17 1).card := by
  have hlen : twoGateOneLitOrLayer.gates.length = 2 := rfl
  rw [hlen]
  exact restrictionsWithStars_17_beat

/-- A concrete two-gate positive-literal DNF layer under an `or` parent.  The
ambient size is fixed at seventeen variables so the closed-form star-space count
gives the strict factor-4 beat for `m = 2`, `w = 1`, `s = 1`, `ℓ = 1`:
`2 * |R(17,0)| * 4^1 < |R(17,1)|`. -/
def twoGateOneLitOrInput : GeneratedOneStepInput 17 where
  layer := twoGateOneLitOrLayer
  w := 1
  s := 1
  ℓ := 1
  width := by
    intro g hg
    change g ∈ [oneLitVar0DNFGate17, oneLitVar1DNFGate17] at hg
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h
    · subst g
      exact oneLitVar0DNFGate17_width
    · subst g
      exact oneLitVar1DNFGate17_width
  beat := by
    exact twoGateOneLitOrLayer_beat

/-- Path-B richer generated one-step consumer instance: two distinct one-literal
DNF gates under an `or` parent have a generated one-step certificate from the
existing `GeneratedOneStepInput` infrastructure and the closed-form
`restrictionsWithStars_card` beat. -/
theorem twoGateOneLitOr_nonvacuous :
    ∃ C : GeneratedOneStepCertificate twoGateOneLitOrInput,
      C.ρ ∈ restrictionsWithStars 17 1 ∧
      C.reducedChildren.length = 2 ∧
      depth C.reducedFormula ≤ 2 := by
  obtain ⟨C, hρ, _hsem, hcount, hdepth⟩ :=
    generatedOneStepDepthReduction_exists twoGateOneLitOrInput
  have hgates : twoGateOneLitOrInput.layer.gates.length = 2 := rfl
  exact ⟨C, hρ, by rw [hcount, hgates], by simpa using hdepth⟩

/-- Summary pin for S2232-B2: a concrete two-gate, one-literal bottom layer
consumes the generated one-step depth-reduction theorem.  This is only a
one-step infrastructure instance, not a general switching lemma or lower-bound
claim. -/
theorem S2232_pathB_twoGateOneLit_oneStepCertificate :
    ∃ C : GeneratedOneStepCertificate twoGateOneLitOrInput,
      C.ρ ∈ restrictionsWithStars 17 1 ∧
      C.reducedChildren.length = 2 := by
  obtain ⟨C, hρ, hcount, _hdepth⟩ := twoGateOneLitOr_nonvacuous
  exact ⟨C, hρ, hcount⟩

end GeneratedOneStepTwoGateInstance
end PvNP
