import PvNP.GeneratedGoodRestriction

/-!
# Gate B obstruction map for generated iterated collapse

This file is a Lean-facing map of the current Gate-B interface after the
counting-generated good-restriction work.  It deliberately stays at the formula
collapse infrastructure layer.

Scope boundary:
* formula-collapse infrastructure only;
* not a Frege/PHP lower bound;
* not an NP/circuit lower bound;
* not a `P` versus `NP` claim;
* Gate A rung 4 (matching switching lemma route) remains open.

The target `generatedIteratedCollapse` is **not** stated here.  The available
checked artifact is a shared-layer certificate produced by
`GeneratedGoodRestriction.simultaneousCollapse_exists`/mixed-stage wrappers.  The
missing B3/B4 ingredients are recorded as named obligations, not as theorem
hypotheses used to prove a stronger conclusion.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace GeneratedIteratedCollapse

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingLemmaStatement

/-! ## Shared generated bottom-layer input -/

/-- A generated mixed bottom-layer input: DNF-view and CNF-view gates, uniform
width and stage budgets, and the counting inequality needed to generate one
restriction shared by the whole layer. -/
structure GeneratedSharedLayerInput (n : Nat) where
  Ds : List ((F : BDFormula n) × DNFView F)
  Cs : List ((F : BDFormula n) × CNFView F)
  w : Nat
  s : Nat
  ℓ : Nat
  widthD : ∀ p ∈ Ds, widthDNF p.2.D ≤ w
  widthC : ∀ p ∈ Cs, widthDNF (cnfDualDNF p.2.C) ≤ w
  beat : (Ds.length + Cs.length) *
      ((restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s) <
    (restrictionsWithStars n ℓ).card

/-- A checked certificate for one generated shared layer.  It records the single
counting-generated restriction plus generated stage records for every DNF/CNF
gate in the supplied mixed layer. -/
structure GeneratedSharedLayerCertificate {n : Nat}
    (I : GeneratedSharedLayerInput n) where
  ρ : Restriction n
  stars : ρ ∈ restrictionsWithStars n I.ℓ
  dnfStages : ∀ p ∈ I.Ds, ∃ S : GeneratedDNFLayerStage p.1,
    S.view = p.2 ∧ S.s = I.s ∧ S.ℓ = I.ℓ ∧ S.ρ = ρ
  cnfStages : ∀ p ∈ I.Cs, ∃ S : GeneratedCNFLayerStage p.1,
    S.view = p.2 ∧ S.s = I.s ∧ S.ℓ = I.ℓ ∧ S.ρ = ρ

/-- The available generated shared-layer theorem: the B1/B2 counting route
produces a single restriction and mixed DNF/CNF generated stages for the whole
listed bottom layer.  This is not yet the B3 parent-layer rewrite/merge. -/
theorem generatedSharedLayerCertificate_exists {n : Nat}
    (I : GeneratedSharedLayerInput n) :
    ∃ C : GeneratedSharedLayerCertificate I, C.ρ ∈ restrictionsWithStars n I.ℓ := by
  obtain ⟨ρ, hρ, hD, hC⟩ := generatedSimultaneousMixedStages_exist
    I.Ds I.Cs I.w I.s I.ℓ I.widthD I.widthC I.beat
  exact ⟨{
    ρ := ρ
    stars := hρ
    dnfStages := hD
    cnfStages := hC
  }, hρ⟩

/-! ## Open B3/B4 route obligations (names only, no false theorem shell) -/

/-- Named missing ingredients for closing Gate B.  These constructors are an
obstruction map, not assumptions used to prove `generatedIteratedCollapse`. -/
inductive OpenObligation where
  /-- Formal layered `BDFormula` view exposing the current bottom layer. -/
  | layeredBDFormulaView
  /-- Replace each collapsed bottom gate by its generated decision tree/formula. -/
  | bottomGateReplacement
  /-- Merge the generated replacements into the parent layer with semantics. -/
  | parentLayerMerge
  /-- Compose generated restrictions across layers. -/
  | restrictionSequenceComposition
  /-- Aggregate the per-stage `s`/depth accounting over `d` layers. -/
  | aggregateDepthAccounting
  /-- Aggregate size accounting for the restricted/rewritten layered formula. -/
  | aggregateSizeAccounting
  /-- Closed-form or otherwise usable cardinality accounting for restriction spaces. -/
  | restrictionSpaceCardinality
  /-- A concrete final instance where the iterated bound beats the sequence space. -/
  | finalNonvacuity
  /-- State and prove the final generated iterated-collapse theorem. -/
  | finalGeneratedIteratedCollapse
deriving DecidableEq, Repr

/-- The current B3/B4 obstruction list. -/
def openObligations : List OpenObligation :=
  [ OpenObligation.layeredBDFormulaView
  , OpenObligation.bottomGateReplacement
  , OpenObligation.parentLayerMerge
  , OpenObligation.restrictionSequenceComposition
  , OpenObligation.aggregateDepthAccounting
  , OpenObligation.aggregateSizeAccounting
  , OpenObligation.restrictionSpaceCardinality
  , OpenObligation.finalNonvacuity
  , OpenObligation.finalGeneratedIteratedCollapse
  ]

/-- The obstruction map is intentionally nonempty: full Gate B is still open. -/
theorem openObligations_nonempty : openObligations ≠ [] := by
  decide

/-! ## Non-vacuity of the checked shared-layer wrapper -/

/-- A concrete empty mixed layer reusing the existing empty DNF/CNF witnesses. -/
def emptyMixedSharedLayerInput (n : Nat) (hn : 1 ≤ n) :
    GeneratedSharedLayerInput n where
  Ds := [⟨BDFormula.or [], emptyGateView n⟩]
  Cs := [⟨BDFormula.tru, emptyCNFView n⟩]
  w := 0
  s := 1
  ℓ := 1
  widthD := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    simp [emptyGateView]
  widthC := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    simp [emptyCNFView, cnfDualDNF]
  beat := by
    have hpos : 0 < (restrictionsWithStars n 1).card :=
      Finset.card_pos.mpr (restrictionsWithStars_nonempty hn)
    simpa using hpos

/-- Non-vacuity for the new shared-layer certificate wrapper, routed through the
previously checked empty mixed generated-stage witness. -/
theorem generatedSharedLayerCertificate_empty_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    ∃ C : GeneratedSharedLayerCertificate (emptyMixedSharedLayerInput n hn),
      C.ρ ∈ restrictionsWithStars n 1 := by
  obtain ⟨ρ, hρ, hD, hC⟩ := generatedMixedEmptyStages_nonvacuous n hn
  refine ⟨{
    ρ := ρ
    stars := hρ
    dnfStages := ?_
    cnfStages := ?_
  }, hρ⟩
  · intro p hp
    simp only [emptyMixedSharedLayerInput, List.mem_singleton] at hp
    subst p
    simpa using hD
  · intro p hp
    simp only [emptyMixedSharedLayerInput, List.mem_singleton] at hp
    subst p
    simpa using hC

end GeneratedIteratedCollapse
end PvNP
