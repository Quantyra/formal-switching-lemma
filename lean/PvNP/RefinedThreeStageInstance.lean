import PvNP.AutoReviewedIteration
import PvNP.RefinedThreeStageArith

/-!
# Concrete three-stage renormalized generated-collapse instance

This module proves one concrete finite representation/collapse instance with
`n = 5193`, stage budgets `[2, 2, 1]`, star counts `[306, 17, 1]`, and one
generated gate per stage.  The second and third layers are the automatically
re-viewed generated layers supplied by `AutoReviewedIteration.nextLayer`.

This is only a concrete finite formula-collapse certificate.  It is not a
frozen-form B4 theorem, not an automatic many-round iteration theorem, not a
Frege/PHP proof-size claim, not an NP/circuit lower bound, and not a P-vs-NP
claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RefinedThreeStageInstance

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

/-- Ambient variable count for the concrete finite instance. -/
def requestedN : Nat := 5193

/-- Stage budgets for the concrete finite instance. -/
def requestedStageBudgets : List Nat := [2, 2, 1]

/-- Stage star counts for the concrete finite instance. -/
def requestedStageStarCounts : List Nat := [306, 17, 1]

/-- Stage gate counts for the concrete finite instance. -/
def requestedStageGateCounts : List Nat := [1, 1, 1]

/-- The concrete milestone parameters as a small checked record. -/
theorem requestedParameters_recorded :
    requestedN = 5193 ∧
    requestedStageBudgets = [2, 2, 1] ∧
    requestedStageStarCounts = [306, 17, 1] ∧
    requestedStageGateCounts = [1, 1, 1] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Stage layers and inputs

The choose-ratio facts and per-stage counting beats live in
`PvNP.RefinedThreeStageArith` (same namespace). -/

def firstLit : Literal 5193 := ⟨⟨0, by omega⟩, true⟩

/-- Stage-1 gate: one single-literal DNF. -/
def stage1Gate : GateSpec 5193 :=
  GateSpec.dnf (BDFormula.lit firstLit)
    { D := [[firstLit]]
      sem_eq := by
        intro a
        simp [dnfEval, termEval, eval_lit]
      simple := by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm] }

/-- Stage-1 layer: one width-1 gate under an `or` parent. -/
def stage1Layer : MinimalLayeredFormula 5193 :=
  { parent := ParentKind.or, gates := [stage1Gate] }

private theorem stage1_width :
    ∀ g ∈ stage1Layer.gates, widthDNF g.theDNF ≤ 1 := by
  intro g hg
  have hg' : g = stage1Gate := by
    simpa [stage1Layer] using hg
  subst hg'
  show widthDNF [[firstLit]] ≤ 1
  simp [widthDNF, termWidth]

private theorem stage1_length : stage1Layer.gates.length = 1 := rfl

private theorem stage1_beatRefined :
    stage1Layer.gates.length *
        ((restrictionsWithStars (stars (freeRestriction 5193)) (306 - 2)).card *
          (4 * 1) ^ 2) <
      (refinesSubspace (freeRestriction 5193) 306).card := by
  rw [stage1_length, stars_freeRestriction, refinesSubspace_freeRestriction]
  exact stage1_beat

private theorem stage1_beatPlain :
    stage1Layer.gates.length *
        ((restrictionsWithStars 5193 (306 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 5193 306).card := by
  rw [stage1_length]
  exact stage1_beat

/-- Stage 1: one width-1 gate over the free base, `s = 2`, `ℓ = 306`. -/
def stage1Input : GeneratedRefinedStepInput 5193 (freeRestriction 5193) where
  layer := stage1Layer
  w := 1
  s := 2
  ℓ := 306
  width := stage1_width
  beatRefined := stage1_beatRefined
  beatPlain := stage1_beatPlain

/-- Stage 2, automatically re-viewed from the stage-1 certificate. -/
noncomputable def stage2Layer
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    MinimalLayeredFormula 5193 :=
  AutoReviewedIteration.nextLayer C

private theorem stage2_width
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    ∀ g ∈ (stage2Layer C).gates, widthDNF g.theDNF ≤ 1 := by
  have h := AutoReviewedIteration.nextLayer_width C
  simpa [stage2Layer, stage1Input] using h

private theorem stage2_length
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length = 1 := by
  rw [stage2Layer, AutoReviewedIteration.nextLayer_gateCount C]
  rfl

private theorem stage1_stars
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    stars (compose (freeRestriction 5193) C.ρ) = 306 := by
  rw [compose_freeRestriction]
  exact (mem_restrictionsWithStars C.ρ).mp C.stars

private theorem stage2_beatRefined
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length *
        ((restrictionsWithStars (stars (compose (freeRestriction 5193) C.ρ))
            (17 - 2)).card * (4 * 1) ^ 2) <
      (refinesSubspace (compose (freeRestriction 5193) C.ρ) 17).card := by
  rw [stage2_length C, refinesSubspace_card, stage1_stars C]
  exact stage2_refined_beat_base306

private theorem stage2_beatPlain
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length *
        ((restrictionsWithStars 5193 (17 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 5193 17).card := by
  rw [stage2_length C]
  exact stage2_plain_beat

/-- Stage 2 input: `s = 2`, `ℓ = 17`, one automatically re-viewed gate. -/
noncomputable def stage2Input
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    GeneratedRefinedStepInput 5193 (compose (freeRestriction 5193) C.ρ) where
  layer := stage2Layer C
  w := 1
  s := 2
  ℓ := 17
  width := stage2_width C
  beatRefined := stage2_beatRefined C
  beatPlain := stage2_beatPlain C

/-- Stage 3, automatically re-viewed from the stage-2 certificate. -/
noncomputable def stage3Layer
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain) :
    MinimalLayeredFormula 5193 :=
  AutoReviewedIteration.nextLayer C₂

private theorem stage3_width
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain) :
    ∀ g ∈ (stage3Layer C₁ C₂).gates, widthDNF g.theDNF ≤ 1 := by
  have h := AutoReviewedIteration.nextLayer_width C₂
  simpa [stage3Layer, stage2Input] using h

private theorem stage3_length
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain) :
    (stage3Layer C₁ C₂).gates.length = 1 := by
  rw [stage3Layer, AutoReviewedIteration.nextLayer_gateCount C₂]
  exact stage2_length C₁

private theorem stage2_stars
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain)
    (href₂ : RefinesWith (compose (freeRestriction 5193) C₁.ρ) C₂.ρ) :
    stars (compose (compose (freeRestriction 5193) C₁.ρ) C₂.ρ) = 17 := by
  rw [RefinedSubspace.compose_eq_of_refinesWith href₂]
  exact (mem_restrictionsWithStars C₂.ρ).mp C₂.stars

private theorem stage3_beatRefined
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain)
    (href₂ : RefinesWith (compose (freeRestriction 5193) C₁.ρ) C₂.ρ) :
    (stage3Layer C₁ C₂).gates.length *
        ((restrictionsWithStars
            (stars (compose (compose (freeRestriction 5193) C₁.ρ) C₂.ρ))
            (1 - 1)).card * (4 * 1) ^ 1) <
      (refinesSubspace (compose (compose (freeRestriction 5193) C₁.ρ) C₂.ρ) 1).card := by
  rw [stage3_length C₁ C₂, refinesSubspace_card, stage2_stars C₁ C₂ href₂]
  exact stage3_refined_beat_base17

private theorem stage3_beatPlain
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain) :
    (stage3Layer C₁ C₂).gates.length *
        ((restrictionsWithStars 5193 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 5193 1).card := by
  rw [stage3_length C₁ C₂]
  exact stage3_plain_beat

/-- Stage 3 input: `s = 1`, `ℓ = 1`, one automatically re-viewed gate. -/
noncomputable def stage3Input
    (C₁ : GeneratedOneStepCertificate stage1Input.toPlain)
    (C₂ : GeneratedOneStepCertificate (stage2Input C₁).toPlain)
    (href₂ : RefinesWith (compose (freeRestriction 5193) C₁.ρ) C₂.ρ) :
    GeneratedRefinedStepInput 5193
      (compose (compose (freeRestriction 5193) C₁.ρ) C₂.ρ) where
  layer := stage3Layer C₁ C₂
  w := 1
  s := 1
  ℓ := 1
  width := stage3_width C₁ C₂
  beatRefined := stage3_beatRefined C₁ C₂ href₂
  beatPlain := stage3_beatPlain C₁ C₂

/-! ## The concrete three-stage certificate -/

open GeneratedRefinedIteratedCertificate in
/-- A proved concrete finite three-stage auto-reviewed generated-collapse
instance with nonempty one-gate stage layers and star counts `306`, `17`, `1`. -/
theorem refinedThreeStage_autoReviewed_nonemptyGates_nonvacuous :
    ∃ cert : GeneratedRefinedIteratedCertificate 5193 (freeRestriction 5193)
        (BDFormula.or [BDFormula.lit firstLit]) 3,
      cert.stageGateCounts = [1, 1, 1] ∧
      cert.stageBudgets = [2, 2, 1] ∧
      cert.stageStarCounts = [306, 17, 1] ∧
      RefinesSeq (freeRestriction 5193) cert.stageRestrictions ∧
      (∃ a : Assignment 5193, Agree cert.finalComposed a) ∧
      (∀ a : Assignment 5193, Agree cert.finalComposed a →
        eval a cert.finalFormula =
          eval a (restrict cert.finalComposed
            (BDFormula.or [BDFormula.lit firstLit]))) := by
  obtain ⟨C₁, href₁⟩ := generatedRefinedOneStep_exists stage1Input
  obtain ⟨C₂, href₂⟩ := generatedRefinedOneStep_exists (stage2Input C₁)
  obtain ⟨C₃, href₃⟩ := generatedRefinedOneStep_exists (stage3Input C₁ C₂ href₂)
  let rest3 : GeneratedRefinedIteratedCertificate 5193
      (compose (compose (freeRestriction 5193) C₁.ρ) C₂.ρ)
      C₂.reducedFormula 1 := by
    rw [← AutoReviewedIteration.nextLayer_originalFormula C₂]
    exact .step (stage3Input C₁ C₂ href₂) C₃ href₃ (.done _ _)
  let rest2 : GeneratedRefinedIteratedCertificate 5193
      (compose (freeRestriction 5193) C₁.ρ) C₁.reducedFormula 2 := by
    rw [← AutoReviewedIteration.nextLayer_originalFormula C₁]
    exact .step (stage2Input C₁) C₂ href₂ rest3
  refine ⟨.step stage1Input C₁ href₁ rest2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact ⟨href₁, href₂, href₃, trivial⟩
  · exact finalComposed_extension _
  · exact finalFormula_restrict_eval _

end RefinedThreeStageInstance
end PvNP
