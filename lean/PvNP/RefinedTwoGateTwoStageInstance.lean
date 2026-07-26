import PvNP.AutoReviewedIteration

/-!
# S2234-B4 two-gate two-stage generated/refined consumer

This module is a concrete multi-step consumer of the generated/refined collapse
infrastructure only.  It builds a real two-stage certificate for two one-literal
gates at `n = 203`: stage 1 uses `s = 2`, `ℓ = 17`, and stage 2 is the
automatically re-viewed generated layer with width budget `1`, `s = 1`,
`ℓ = 1` over the 17-star base.

The stage-2 beat is a genuine renormalized beat for two gates,
`2 * |R(17,0)| * 4 < |R(17,1)|` (equivalently `16 < 17` after cancelling the
common power of two).  This is not a `s = 1 → nextLayer` staging-only theorem and
not a constants-only package.

Scope: multi-step consumer infrastructure only; not a general switching lemma,
not AC0/Frege/PHP, not a lower bound, not P-vs-NP, and not `v0.11.0`.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RefinedTwoGateTwoStageInstance

set_option maxRecDepth 8192
set_option exponentiation.threshold 400

attribute [local irreducible] SwitchingLemmaStatement.restrictionsWithStars
attribute [local irreducible] RefinedSubspace.refinesSubspace
attribute [local irreducible] SwitchingLemmaStatement.stars

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open RestrictionComposition
open RefinedSubspace
open GeneratedOneStepDepthReduction
open GeneratedIteratedCollapseFinal
open GeneratedRefinedCollapse

def ambientN : Nat := 203

def requestedStageBudgets : List Nat := [2, 1]

def requestedStageStarCounts : List Nat := [17, 1]

def requestedStageGateCounts : List Nat := [2, 2]

theorem requestedParameters_recorded :
    ambientN = 203 ∧
    requestedStageBudgets = [2, 1] ∧
    requestedStageStarCounts = [17, 1] ∧
    requestedStageGateCounts = [2, 2] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Two one-literal stage-1 gates -/

def firstLit : Literal 203 := ⟨⟨0, by omega⟩, true⟩

def secondLit : Literal 203 := ⟨⟨1, by omega⟩, true⟩

def litGate (l : Literal 203) : GateSpec 203 :=
  GateSpec.dnf (BDFormula.lit l)
    { D := [[l]]
      sem_eq := by
        intro a
        simp [dnfEval, termEval, eval_lit]
      simple := by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm] }

def firstGate : GateSpec 203 := litGate firstLit

def secondGate : GateSpec 203 := litGate secondLit

def stage1Layer : MinimalLayeredFormula 203 :=
  { parent := ParentKind.or, gates := [firstGate, secondGate] }

private theorem litGate_width (l : Literal 203) : widthDNF (litGate l).theDNF ≤ 1 := by
  show widthDNF [[l]] ≤ 1
  simp [widthDNF, termWidth]

private theorem stage1_width :
    ∀ g ∈ stage1Layer.gates, widthDNF g.theDNF ≤ 1 := by
  intro g hg
  simp [stage1Layer] at hg
  rcases hg with rfl | rfl
  · exact litGate_width firstLit
  · exact litGate_width secondLit

private theorem stage1_length : stage1Layer.gates.length = 2 := rfl

/-! ## Counting arithmetic -/

private theorem choose203_ratio_17 :
    128 * Nat.choose 203 15 < Nat.choose 203 17 := by
  have h1' : Nat.choose 203 15 * (203 - 15) = Nat.choose 203 (15 + 1) * (15 + 1) :=
    (Nat.choose_succ_right_eq 203 15).symm
  have h2' : Nat.choose 203 (15 + 1) * (203 - (15 + 1)) =
      Nat.choose 203 (15 + 2) * (15 + 2) :=
    (Nat.choose_succ_right_eq 203 (15 + 1)).symm
  have hbeat : 128 * ((15 + 2) * (15 + 1)) < (203 - (15 + 1)) * (203 - 15) := by
    decide
  have hpos : 0 < Nat.choose 203 15 := Nat.choose_pos (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := (15 + 2) * (15 + 1))
  calc
    (128 * Nat.choose 203 15) * ((15 + 2) * (15 + 1))
        = Nat.choose 203 15 * (128 * ((15 + 2) * (15 + 1))) := by ac_rfl
    _ < Nat.choose 203 15 * ((203 - (15 + 1)) * (203 - 15)) :=
        Nat.mul_lt_mul_of_pos_left hbeat hpos
    _ = (Nat.choose 203 15 * (203 - 15)) * (203 - (15 + 1)) := by ac_rfl
    _ = (Nat.choose 203 (15 + 1) * (15 + 1)) * (203 - (15 + 1)) := by rw [h1']
    _ = (Nat.choose 203 (15 + 1) * (203 - (15 + 1))) * (15 + 1) := by ac_rfl
    _ = (Nat.choose 203 (15 + 2) * (15 + 2)) * (15 + 1) := by rw [h2']
    _ = Nat.choose 203 (15 + 2) * ((15 + 2) * (15 + 1)) := by ac_rfl

private theorem beat_from_ratio_two_gate {A B x y d e K : Nat}
    (hx : x = y + d) (hK : 2 * e * 2 ^ d = K) (hr : K * A < B) :
    2 * (A * 2 ^ x * e) < B * 2 ^ y := by
  subst hx
  rw [Nat.pow_add]
  have hE : 2 * (A * (2 ^ y * 2 ^ d) * e) = (2 * e * 2 ^ d) * A * 2 ^ y := by
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hE, hK]
  exact Nat.mul_lt_mul_of_lt_of_le hr (Nat.le_refl _)
    (Nat.pos_pow_of_pos _ (by decide))

private theorem stage1_beat :
    2 * ((restrictionsWithStars 203 (17 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 203 17).card := by
  rw [restrictionsWithStars_card, restrictionsWithStars_card]
  rw [show (17 - 2 : Nat) = 15 from rfl]
  exact beat_from_ratio_two_gate (d := 2) (K := 128) (by decide) (by decide)
    choose203_ratio_17

private theorem stage2_refined_beat_base17 :
    2 * ((restrictionsWithStars 17 (1 - 1)).card * (4 * 1) ^ 1) <
      (Nat.choose 17 1 * 2 ^ (17 - 1)) := by
  rw [restrictionsWithStars_card]
  decide

private theorem stage2_plain_beat :
    2 * ((restrictionsWithStars 203 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 203 1).card := by
  rw [restrictionsWithStars_card, restrictionsWithStars_card]
  rw [show (1 - 1 : Nat) = 0 from rfl, Nat.choose_zero_right,
    Nat.choose_one_right]
  decide

/-! ## Refined two-stage inputs -/

private theorem stage1_beatRefined :
    stage1Layer.gates.length *
        ((restrictionsWithStars (stars (freeRestriction 203)) (17 - 2)).card *
          (4 * 1) ^ 2) <
      (refinesSubspace (freeRestriction 203) 17).card := by
  rw [stage1_length, stars_freeRestriction, refinesSubspace_freeRestriction]
  exact stage1_beat

private theorem stage1_beatPlain :
    stage1Layer.gates.length *
        ((restrictionsWithStars 203 (17 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 203 17).card := by
  rw [stage1_length]
  exact stage1_beat

def stage1Input : GeneratedRefinedStepInput 203 (freeRestriction 203) where
  layer := stage1Layer
  w := 1
  s := 2
  ℓ := 17
  width := stage1_width
  beatRefined := stage1_beatRefined
  beatPlain := stage1_beatPlain

noncomputable def stage2Layer
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    MinimalLayeredFormula 203 :=
  AutoReviewedIteration.nextLayer C

private theorem stage2_width
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    ∀ g ∈ (stage2Layer C).gates, widthDNF g.theDNF ≤ 1 := by
  have h := AutoReviewedIteration.nextLayer_width C
  simpa [stage2Layer, stage1Input] using h

private theorem stage2_length
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length = 2 := by
  rw [stage2Layer, AutoReviewedIteration.nextLayer_gateCount C]
  rfl

private theorem stage1_stars
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    stars (compose (freeRestriction 203) C.ρ) = 17 := by
  rw [compose_freeRestriction]
  exact (mem_restrictionsWithStars C.ρ).mp C.stars

private theorem stage2_beatRefined
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length *
        ((restrictionsWithStars (stars (compose (freeRestriction 203) C.ρ))
            (1 - 1)).card * (4 * 1) ^ 1) <
      (refinesSubspace (compose (freeRestriction 203) C.ρ) 1).card := by
  rw [stage2_length C, refinesSubspace_card, stage1_stars C]
  exact stage2_refined_beat_base17

private theorem stage2_beatPlain
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length *
        ((restrictionsWithStars 203 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 203 1).card := by
  rw [stage2_length C]
  exact stage2_plain_beat

noncomputable def stage2Input
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    GeneratedRefinedStepInput 203 (compose (freeRestriction 203) C.ρ) where
  layer := stage2Layer C
  w := 1
  s := 1
  ℓ := 1
  width := stage2_width C
  beatRefined := stage2_beatRefined C
  beatPlain := stage2_beatPlain C

/-! ## The two-stage certificate pin -/

open GeneratedRefinedIteratedCertificate in
/-- S2234-B4: a concrete two-stage generated/refined certificate with two
stage-1 gates, stage budgets `[2, 1]`, star counts `[17, 1]`, and two generated
consumer gates at the nontrivial second stage. -/
theorem refinedTwoGateTwoStage_nonempty_twoStageCertificate :
    ∃ cert : GeneratedRefinedIteratedCertificate 203 (freeRestriction 203)
        stage1Layer.originalFormula 2,
      cert.stageGateCounts = [2, 2] ∧
      cert.stageBudgets = [2, 1] ∧
      cert.stageStarCounts = [17, 1] ∧
      RefinesSeq (freeRestriction 203) cert.stageRestrictions ∧
      (∃ a : Assignment 203, Agree cert.finalComposed a) ∧
      (∀ a : Assignment 203, Agree cert.finalComposed a →
        eval a cert.finalFormula =
          eval a (restrict cert.finalComposed stage1Layer.originalFormula)) := by
  obtain ⟨C₁, href₁⟩ := generatedRefinedOneStep_exists stage1Input
  obtain ⟨C₂, href₂⟩ := generatedRefinedOneStep_exists (stage2Input C₁)
  let rest2 : GeneratedRefinedIteratedCertificate 203
      (compose (freeRestriction 203) C₁.ρ) C₁.reducedFormula 1 := by
    rw [← AutoReviewedIteration.nextLayer_originalFormula C₁]
    exact .step (stage2Input C₁) C₂ href₂ (.done _ _)
  refine ⟨.step stage1Input C₁ href₁ rest2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact ⟨href₁, href₂, trivial⟩
  · exact finalComposed_extension _
  · exact finalFormula_restrict_eval _

end RefinedTwoGateTwoStageInstance
end PvNP
