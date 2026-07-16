import PvNP.GeneratedRefinedCollapse

/-!
# A concrete two-stage renormalized instance with width-budget-1 gates at BOTH stages

This module discharges, FOR THE REFINEMENT ROUTE, the KNOWN SATISFIABILITY GAP
disclosure with a proved instance (frozen-form B4 remains open): a depth-2 `GeneratedRefinedCollapsePlan` over `n = 306` variables in
which BOTH stages carry a nonempty bottom layer with width budget `w = 1` and
non-degenerate counting beats.

* Stage 1 (free base): one single-literal DNF gate, `s = 2`, `ℓ = 17`.  The
  renormalized beat reduces to `64 · C(306,15) < C(306,17)`, proved
  symbolically from `Nat.choose_succ_right_eq` (no big kernel computation).
* Stage 2 (base = the stage-1 generated restriction, refining the free base,
  hence with EXACTLY 17 free variables): the plan's `next` function re-views
  the stage-1 rewritten formula — an `or` over the generated depth-`≤ 1` tree
  — as one gate with an explicit depth-one DNF view (`depthOneDNFView`), width
  budget `1`, `s = 1`, `ℓ = 1`.  The renormalized beat is `2^18 < 17 · 2^16`,
  decidably checked.

The realized stage-2 DNF may be EMPTY or constant (the generated stage-1 tree
may be a leaf); realized width `≥ 1` at stage 2 is NOT certified.
"Nonempty-gate" means the gate LIST is nonempty (one gate per stage) with
width BUDGET `1` and the non-degenerate `(4·1)^s` beat factor at both stages;
only stage 1's gate is syntactically pinned at realized width 1.

## HONEST SCOPE STATEMENT (read this)

* One concrete finite instance; no asymptotic family is claimed.
* The stage-2 re-viewing works because stage-1 trees have depth `≤ 1`
  (`s = 2`); general tree-to-DNF/CNF re-viewing at larger budgets is NOT
  provided here.
* Frozen-form B4 (single upfront depth-`d` view, product hypothesis
  `B(m, w, s, d)`, `t(d, s)` tree bound) remains OPEN.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.
  Gate A rung 4 remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RefinedTwoStageInstance

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

/-! ## Depth-one trees re-view as width-1 DNFs -/

/-- The path DNF of a depth-`≤ 1` decision tree (constants and single-variable
queries; deeper trees, which never arise under the depth hypothesis, get the
empty DNF).  WARNING: this is semantically meaningful ONLY for trees of depth
`≤ 1`; use it exclusively through `depthOneDNFView`, whose depth hypothesis
refutes the deeper cases. -/
def depthOneDNF {n : Nat} : DTree n → DNF n
  | .leaf false => []
  | .leaf true => [[]]
  | .node _ (.leaf false) (.leaf false) => []
  | .node v (.leaf true) (.leaf false) => [[⟨v, false⟩]]
  | .node v (.leaf false) (.leaf true) => [[⟨v, true⟩]]
  | .node v (.leaf true) (.leaf true) => [[⟨v, false⟩], [⟨v, true⟩]]
  | .node _ _ _ => []

theorem widthDNF_depthOneDNF_le {n : Nat} (T : DTree n) :
    widthDNF (depthOneDNF T) ≤ 1 := by
  cases T with
  | leaf b => cases b <;> simp [depthOneDNF, widthDNF, termWidth]
  | node v t0 t1 =>
      cases t0 with
      | node _ _ _ =>
          cases t1 with
          | node _ _ _ => simp [depthOneDNF, widthDNF]
          | leaf b1 => cases b1 <;> simp [depthOneDNF, widthDNF]
      | leaf b0 =>
          cases t1 with
          | node _ _ _ => cases b0 <;> simp [depthOneDNF, widthDNF]
          | leaf b1 =>
              cases b0 <;> cases b1 <;>
                simp [depthOneDNF, widthDNF, termWidth]

theorem simpleDNF_depthOneDNF {n : Nat} (T : DTree n) :
    SimpleDNF (depthOneDNF T) := by
  intro t ht
  cases T with
  | leaf b =>
      cases b
      · simp [depthOneDNF] at ht
      · simp only [depthOneDNF, List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm]
  | node v t0 t1 =>
      cases t0 with
      | node _ _ _ =>
          cases t1 with
          | node _ _ _ => simp [depthOneDNF] at ht
          | leaf b1 => cases b1 <;> simp [depthOneDNF] at ht
      | leaf b0 =>
          cases t1 with
          | node _ _ _ => cases b0 <;> simp [depthOneDNF] at ht
          | leaf b1 =>
              cases b0 with
              | false =>
                  cases b1 with
                  | false => simp [depthOneDNF] at ht
                  | true =>
                      simp only [depthOneDNF, List.mem_singleton] at ht
                      subst ht
                      simp [SimpleTerm]
              | true =>
                  cases b1 with
                  | false =>
                      simp only [depthOneDNF, List.mem_singleton] at ht
                      subst ht
                      simp [SimpleTerm]
                  | true =>
                      simp only [depthOneDNF, List.mem_cons,
                        List.mem_singleton, List.not_mem_nil, or_false] at ht
                      rcases ht with rfl | rfl <;> simp [SimpleTerm]

/-- Re-view a depth-`≤ 1` tree formula as a simple width-`≤ 1` DNF. -/
def depthOneDNFView {n : Nat} (T : DTree n) (hT : dtDepth T ≤ 1) :
    DNFView (treeToFormula T) where
  D := depthOneDNF T
  sem_eq := by
    intro a
    rw [eval_treeToFormula]
    cases T with
    | leaf b => cases b <;> simp [depthOneDNF, dnfEval]
    | node v t0 t1 =>
        cases t0 with
        | node v0 s0 s1 =>
            exfalso
            simp only [dtDepth_node] at hT
            omega
        | leaf b0 =>
            cases t1 with
            | node v1 s0 s1 =>
                exfalso
                simp only [dtDepth_node] at hT
                omega
            | leaf b1 =>
                cases b0 <;> cases b1 <;> cases hv : a v <;>
                  simp [depthOneDNF, dnfEval, termEval, litEval, hv]
  simple := simpleDNF_depthOneDNF T

/-! ## The choose-ratio arithmetic (symbolic; no big kernel computation) -/

set_option maxHeartbeats 1000000 in
private theorem choose306_ratio :
    256 * Nat.choose 306 15 < Nat.choose 306 17 := by
  have h1 := Nat.choose_succ_right_eq 306 15
  have h2 := Nat.choose_succ_right_eq 306 16
  simp only [Nat.reduceAdd, Nat.reduceSub] at h1 h2
  have hpos : 0 < Nat.choose 306 15 := Nat.choose_pos (by omega)
  generalize _hA : Nat.choose 306 15 = A at h1 hpos ⊢
  generalize _hB : Nat.choose 306 16 = B at h1 h2
  generalize _hC : Nat.choose 306 17 = C at h2 ⊢
  omega

/-- The stage-1 counting beat over the full 306-variable star space. -/
private theorem stage1_beat :
    1 * ((restrictionsWithStars 306 (17 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 306 17).card := by
  rw [restrictionsWithStars_card, restrictionsWithStars_card]
  rw [Nat.one_mul, Nat.mul_assoc]
  rw [show ((4 : Nat) * 1) ^ 2 = 2 ^ 4 from rfl]
  rw [← pow_add]
  rw [show (306 - (17 - 2) + 4 : Nat) = 6 + (306 - 17) from rfl]
  rw [pow_add, show (2 : Nat) ^ 6 = 64 from rfl, ← Nat.mul_assoc]
  have hp : 0 < (2 : Nat) ^ (306 - 17) := Nat.pos_pow_of_pos _ (by omega)
  apply Nat.mul_lt_mul_of_lt_of_le _ (Nat.le_refl _) hp
  rw [show (17 - 2 : Nat) = 15 from rfl, Nat.mul_comm]
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (by decide : (64 : Nat) ≤ 256)) choose306_ratio

/-! ## The two-stage plan -/

def firstLit : Literal 306 := ⟨⟨0, by omega⟩, true⟩

/-- The stage-1 gate: one single-literal DNF. -/
def stage1Gate : GateSpec 306 :=
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

/-- The stage-1 layer: one width-1 gate under an `or` parent. -/
def stage1Layer : MinimalLayeredFormula 306 :=
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
        ((restrictionsWithStars (stars (freeRestriction 306)) (17 - 2)).card *
          (4 * 1) ^ 2) <
      (refinesSubspace (freeRestriction 306) 17).card := by
  rw [stage1_length, stars_freeRestriction, refinesSubspace_freeRestriction]
  exact stage1_beat

private theorem stage1_beatPlain :
    stage1Layer.gates.length *
        ((restrictionsWithStars 306 (17 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 306 17).card := by
  rw [stage1_length]
  exact stage1_beat

/-- Stage 1: one width-1 gate over the free base, `s = 2`, `ℓ = 17`. -/
def stage1Input : GeneratedRefinedStepInput 306 (freeRestriction 306) where
  layer := stage1Layer
  w := 1
  s := 2
  ℓ := 17
  width := stage1_width
  beatRefined := stage1_beatRefined
  beatPlain := stage1_beatPlain

/-- The stage-1 generated tree for the single gate. -/
noncomputable def stage1Tree
    (C : GeneratedOneStepCertificate stage1Input.toPlain) : DTree 306 :=
  C.treeOf stage1Gate (List.mem_singleton_self _)

private theorem stage1_toPlain_s : stage1Input.toPlain.s = 2 := rfl

private theorem stage1_toPlain_ell : stage1Input.toPlain.ℓ = 17 := rfl

private theorem stage1Tree_depth
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    dtDepth (stage1Tree C) ≤ 1 := by
  have h := C.treeDepth stage1Gate (List.mem_singleton_self _)
  rw [stage1_toPlain_s] at h
  exact Nat.le_of_lt_succ h

/-- The stage-2 layer: the stage-1 rewritten formula's single generated tree,
re-viewed as one width-budget-1 gate. -/
noncomputable def stage2Layer
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    MinimalLayeredFormula 306 :=
  { parent := ParentKind.or
    gates := [GateSpec.dnf (treeToFormula (stage1Tree C))
      (depthOneDNFView (stage1Tree C) (stage1Tree_depth C))] }

private theorem stage2_width
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    ∀ g ∈ (stage2Layer C).gates, widthDNF g.theDNF ≤ 1 := by
  intro g hg
  have hg' : g = GateSpec.dnf (treeToFormula (stage1Tree C))
      (depthOneDNFView (stage1Tree C) (stage1Tree_depth C)) := by
    simpa [stage2Layer] using hg
  subst hg'
  exact widthDNF_depthOneDNF_le _

private theorem stage2_length
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length = 1 := rfl

private theorem stage1_stars
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    stars (compose (freeRestriction 306) C.ρ) = 17 := by
  rw [compose_freeRestriction, ← stage1_toPlain_ell]
  exact (mem_restrictionsWithStars C.ρ).mp C.stars

private theorem stage2_beatRefined
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length *
        ((restrictionsWithStars (stars (compose (freeRestriction 306) C.ρ))
            (1 - 1)).card * (4 * 1) ^ 1) <
      (refinesSubspace (compose (freeRestriction 306) C.ρ) 1).card := by
  rw [stage2_length, stage1_stars C, refinesSubspace_card, stage1_stars C,
    restrictionsWithStars_card]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSub]
  decide

private theorem stage2_beatPlain
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    (stage2Layer C).gates.length *
        ((restrictionsWithStars 306 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 306 1).card := by
  rw [stage2_length, restrictionsWithStars_card, restrictionsWithStars_card]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSub]
  decide

/-- Stage 2, built from the stage-1 certificate: re-view the generated
depth-`≤ 1` tree as one width-budget-1 gate over the 17 free variables of the
stage-1 restriction, `s = 1`, `ℓ = 1`. -/
noncomputable def stage2Input
    (C : GeneratedOneStepCertificate stage1Input.toPlain) :
    GeneratedRefinedStepInput 306 (compose (freeRestriction 306) C.ρ) where
  layer := stage2Layer C
  w := 1
  s := 1
  ℓ := 1
  width := stage2_width C
  beatRefined := stage2_beatRefined C
  beatPlain := stage2_beatPlain C

/-- The depth-2 renormalized plan with nonempty width-1 gate lists at BOTH
stages. -/
noncomputable def refinedTwoStagePlan :
    GeneratedRefinedCollapsePlan 306 (freeRestriction 306)
      (BDFormula.or [BDFormula.lit firstLit]) 2 :=
  .step stage1Input (fun C _href =>
    .step (stage2Input C) (fun _C' _href' => .done _ _))

/-! ## The satisfiability-gap-closing instance -/

open GeneratedRefinedIteratedCertificate in
/-- **A proved nonempty-gate multi-stage instance.**  The depth-2 renormalized
plan over `306` variables runs: both stages carry ONE gate (width budget `1`,
non-degenerate beats), the two counting-generated restrictions refine in
sequence with star counts `17` then `1`, a common total extension exists, and
the final rewritten formula computes the fully restricted original on every
agreeing assignment. -/
theorem refinedTwoStage_nonemptyGates_nonvacuous :
    ∃ cert : GeneratedRefinedIteratedCertificate 306 (freeRestriction 306)
        (BDFormula.or [BDFormula.lit firstLit]) 2,
      cert.stageGateCounts = [1, 1] ∧
      cert.stageBudgets = [2, 1] ∧
      cert.stageStarCounts = [17, 1] ∧
      RefinesSeq (freeRestriction 306) cert.stageRestrictions ∧
      (∃ a : Assignment 306, Agree cert.finalComposed a) ∧
      (∀ a : Assignment 306, Agree cert.finalComposed a →
        eval a cert.finalFormula =
          eval a (restrict cert.finalComposed
            (BDFormula.or [BDFormula.lit firstLit]))) := by
  obtain ⟨C1, href1⟩ := generatedRefinedOneStep_exists stage1Input
  obtain ⟨C2, href2⟩ := generatedRefinedOneStep_exists (stage2Input C1)
  refine ⟨.step stage1Input C1 href1
    (.step (stage2Input C1) C2 href2 (.done _ _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact ⟨href1, href2, trivial⟩
  · exact finalComposed_extension _
  · exact finalFormula_restrict_eval _

end RefinedTwoStageInstance
end PvNP
