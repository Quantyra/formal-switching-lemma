import PvNP.GeneratedIteratedCollapse

/-!
# Gate B / B3: one generated bottom-layer depth-reduction step

This module closes only the minimal B3 parent-merge/replacement step for a
layered formula view whose parent is an explicit `and`/`or` over a list of
bottom `GateSpec`s.  It consumes the B1/B2 generated shared-restriction theorem
`GeneratedGoodRestriction.simultaneousCollapse_exists4` and proves concrete
semantics for replacing every bottom gate by the formula associated to its
generated decision-tree witness.

It is not an iterated collapse theorem and makes no Frege/PHP/P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace GeneratedOneStepDepthReduction

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open GeneratedIteratedCollapse
open SwitchingLemmaStatement

/-! ## Minimal layered parent view -/

/-- The explicit parent gate above the listed bottom layer. -/
inductive ParentKind where
  | and
  | or
deriving DecidableEq, Repr

namespace ParentKind

private theorem list_all_map_id {α : Type _} (xs : List α) (p : α → Bool) :
    (xs.map p).all id = xs.all p := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem list_any_map_id {α : Type _} (xs : List α) (p : α → Bool) :
    (xs.map p).any id = xs.any p := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Merge child formulas under the parent kind. -/
def merge {n : Nat} : ParentKind → List (BDFormula n) → BDFormula n
  | .and, children => BDFormula.and children
  | .or, children => BDFormula.or children

/-- Evaluate the Boolean aggregator associated with the parent kind. -/
def evalList : ParentKind → List Bool → Bool
  | .and, bs => bs.all id
  | .or, bs => bs.any id

theorem eval_merge {n : Nat} (a : Assignment n) (k : ParentKind)
    (children : List (BDFormula n)) :
    eval a (k.merge children) = k.evalList (children.map (fun F => eval a F)) := by
  cases k
  · rw [merge, evalList, eval_and, list_all_map_id]
  · rw [merge, evalList, eval_or, list_any_map_id]

end ParentKind

/-- A minimal layered formula: one explicit parent over listed bottom gates. -/
structure MinimalLayeredFormula (n : Nat) where
  parent : ParentKind
  gates : List (GateSpec n)

namespace MinimalLayeredFormula

/-- The concrete formula represented by the layered view. -/
def originalFormula {n : Nat} (L : MinimalLayeredFormula n) : BDFormula n :=
  L.parent.merge (L.gates.map GateSpec.formula)

/-- Bottom-layer gate count. -/
def bottomGateCount {n : Nat} (L : MinimalLayeredFormula n) : Nat :=
  L.gates.length

theorem bottomGateCount_eq_length {n : Nat} (L : MinimalLayeredFormula n) :
    L.bottomGateCount = L.gates.length := rfl

end MinimalLayeredFormula

/-! ## Generated one-step input and certificate -/

/-- Generated one-step input: uniform width budget plus the B1/B2 counting beat. -/
structure GeneratedOneStepInput (n : Nat) where
  layer : MinimalLayeredFormula n
  w : Nat
  s : Nat
  ℓ : Nat
  width : ∀ g ∈ layer.gates, widthDNF g.theDNF ≤ w
  beat : layer.gates.length *
      ((restrictionsWithStars n (ℓ - s)).card * (4 * w) ^ s) <
    (restrictionsWithStars n ℓ).card

namespace GeneratedOneStepInput

/-- The original parent-merged formula carried by an input. -/
def originalFormula {n : Nat} (I : GeneratedOneStepInput n) : BDFormula n :=
  I.layer.originalFormula

end GeneratedOneStepInput

/-- A concrete B3 certificate: one generated restriction, one generated tree per
bottom gate, and the reduced parent-merged formula built from those trees. -/
structure GeneratedOneStepCertificate {n : Nat} (I : GeneratedOneStepInput n) where
  ρ : Restriction n
  stars : ρ ∈ restrictionsWithStars n I.ℓ
  treeOf : ∀ g ∈ I.layer.gates, DTree n
  treeDepth : ∀ g (hg : g ∈ I.layer.gates), dtDepth (treeOf g hg) < I.s
  treeSemantics : ∀ g (hg : g ∈ I.layer.gates), ∀ a : Assignment n, Agree ρ a →
    dtEval a (treeOf g hg) = eval a (restrict ρ g.formula)

namespace GeneratedOneStepCertificate

/-- Child formulas after replacing every bottom gate by its generated tree. -/
def reducedChildren {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) : List (BDFormula n) :=
  I.layer.gates.attach.map (fun g => treeToFormula (C.treeOf g.1 g.2))

/-- The concrete reduced formula: same parent kind, generated tree formulas below. -/
def reducedFormula {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) : BDFormula n :=
  I.layer.parent.merge C.reducedChildren

theorem reducedChildCount {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    C.reducedChildren.length = I.layer.gates.length := by
  simp [reducedChildren]

theorem bottomGateCount {n : Nat} {I : GeneratedOneStepInput n}
    (_C : GeneratedOneStepCertificate I) :
    I.layer.bottomGateCount = I.layer.gates.length := rfl

theorem reducedChild_depth_bound {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) (F : BDFormula n)
    (hF : F ∈ C.reducedChildren) :
    depth F ≤ 2 * (I.s - 1) + 1 := by
  rw [reducedChildren] at hF
  rcases List.mem_map.mp hF with ⟨g, _hgmem, rfl⟩
  have hdt := C.treeDepth g.1 g.2
  have hle : dtDepth (C.treeOf g.1 g.2) ≤ I.s - 1 := by omega
  calc depth (treeToFormula (C.treeOf g.1 g.2))
      ≤ 2 * dtDepth (C.treeOf g.1 g.2) + 1 := depth_treeToFormula_le _
    _ ≤ 2 * (I.s - 1) + 1 := by omega

private theorem foldr_max_le_of_all {xs : List Nat} {B : Nat}
    (h : ∀ x ∈ xs, x ≤ B) : xs.foldr Nat.max 0 ≤ B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact (Nat.max_le).2 ⟨h x (List.mem_cons_self x xs),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

private theorem parent_depth_bound {n : Nat} (k : ParentKind)
    (children : List (BDFormula n)) {B : Nat}
    (hB : ∀ F ∈ children, depth F ≤ B) :
    depth (k.merge children) ≤ 1 + B := by
  cases k
  · rw [ParentKind.merge]
    rw [show depth (BDFormula.and children)
        = 1 + (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 from by
          rw [depth]]
    show 1 + (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 ≤ 1 + B
    have hfold : (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 ≤ B :=
      foldr_max_le_of_all (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨(f : {F // F ∈ children}), _hfmem, rfl⟩
      exact hB f.1 f.2)
    omega
  · rw [ParentKind.merge]
    rw [show depth (BDFormula.or children)
        = 1 + (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 from by
          rw [depth]]
    show 1 + (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 ≤ 1 + B
    have hfold : (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 ≤ B :=
      foldr_max_le_of_all (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨(f : {F // F ∈ children}), _hfmem, rfl⟩
      exact hB f.1 f.2)
    omega

/-- Reduced formula depth, accounting only for this one generated step. -/
theorem reducedFormula_depth_bound {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    depth C.reducedFormula ≤ 1 + (2 * (I.s - 1) + 1) := by
  exact parent_depth_bound I.layer.parent C.reducedChildren
    (fun F hF => C.reducedChild_depth_bound F hF)

private theorem reducedChildren_eval_eq {n : Nat} (gates : List (GateSpec n))
    (ρ : Restriction n) (treeOf : ∀ g ∈ gates, DTree n)
    (treeSemantics : ∀ g (hg : g ∈ gates), ∀ a : Assignment n, Agree ρ a →
      dtEval a (treeOf g hg) = eval a (restrict ρ g.formula))
    (a : Assignment n) (ha : Agree ρ a) :
    (gates.attach.map (fun g => treeToFormula (treeOf g.1 g.2))).map
        (fun F => eval a F) =
      gates.map (fun g => eval a (restrict ρ g.formula)) := by
  induction gates with
  | nil => simp
  | cons g gates ih =>
      simp only [List.attach_cons, List.map_cons]
      rw [eval_treeToFormula, treeSemantics g (List.mem_cons_self g gates) a ha]
      simpa [List.map_map, Function.comp_def] using congrArg (fun t => eval a (restrict ρ g.formula) :: t)
        (ih
          (fun g' hg' => treeOf g' (List.mem_cons_of_mem g hg'))
          (fun g' hg' => treeSemantics g' (List.mem_cons_of_mem g hg')))

theorem child_semantics {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) (a : Assignment n) (ha : Agree C.ρ a) :
    C.reducedChildren.map (fun F => eval a F) =
      (I.layer.gates.map (fun g => eval a (restrict C.ρ g.formula))) := by
  simpa [reducedChildren] using
    reducedChildren_eval_eq I.layer.gates C.ρ C.treeOf C.treeSemantics a ha

/-- Semantic preservation for the one-step replacement under assignments that
agree with the generated restriction. -/
theorem semantic_preservation {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) (a : Assignment n) (ha : Agree C.ρ a) :
    eval a C.reducedFormula = eval a (restrict C.ρ I.originalFormula) := by
  calc eval a C.reducedFormula
      = I.layer.parent.evalList (C.reducedChildren.map (fun F => eval a F)) := by
          simp [reducedFormula, ParentKind.eval_merge]
    _ = I.layer.parent.evalList
          (I.layer.gates.map (fun g => eval a (restrict C.ρ g.formula))) := by
          rw [C.child_semantics a ha]
    _ = eval a (I.layer.parent.merge
          (I.layer.gates.map (fun g => restrict C.ρ g.formula))) := by
          rw [ParentKind.eval_merge]
          simp [List.map_map, Function.comp_def]
    _ = eval a (restrict C.ρ I.originalFormula) := by
          cases hparent : I.layer.parent <;>
            simp [GeneratedOneStepInput.originalFormula,
              MinimalLayeredFormula.originalFormula, ParentKind.merge,
              hparent, restrict_and, restrict_or, List.map_map, Function.comp_def]

end GeneratedOneStepCertificate

/-! ## Generated one-step theorem -/

/-- **Gate B / B3, minimal one-step form.**  The B1/B2 counting theorem
generates one restriction and per-gate decision-tree witnesses; replacing every
bottom gate by its generated `treeToFormula` under the same parent preserves
semantics for assignments agreeing with that generated restriction. -/
theorem generatedOneStepDepthReduction_exists {n : Nat}
    (I : GeneratedOneStepInput n) :
    ∃ C : GeneratedOneStepCertificate I,
      C.ρ ∈ restrictionsWithStars n I.ℓ ∧
      (∀ a : Assignment n, Agree C.ρ a →
        eval a C.reducedFormula = eval a (restrict C.ρ I.originalFormula)) ∧
      C.reducedChildren.length = I.layer.gates.length ∧
      depth C.reducedFormula ≤ 1 + (2 * (I.s - 1) + 1) := by
  classical
  obtain ⟨ρ, hstars, hcollapse⟩ := simultaneousCollapse_exists4
    I.layer.gates I.w I.s I.ℓ I.width I.beat
  let treeOf : ∀ g ∈ I.layer.gates, DTree n :=
    fun g hg => Classical.choose (hcollapse g hg)
  have hdepth : ∀ g (hg : g ∈ I.layer.gates), dtDepth (treeOf g hg) < I.s := by
    intro g hg
    exact (Classical.choose_spec (hcollapse g hg)).1
  have hsem : ∀ g (hg : g ∈ I.layer.gates), ∀ a : Assignment n, Agree ρ a →
      dtEval a (treeOf g hg) = eval a (restrict ρ g.formula) := by
    intro g hg a ha
    exact (Classical.choose_spec (hcollapse g hg)).2 a ha
  let C : GeneratedOneStepCertificate I := {
    ρ := ρ
    stars := hstars
    treeOf := treeOf
    treeDepth := hdepth
    treeSemantics := hsem
  }
  exact ⟨C, hstars, C.semantic_preservation,
    C.reducedChildCount, C.reducedFormula_depth_bound⟩

/-! ## Concrete non-vacuity -/

/-- A singleton empty-DNF layer under an `or` parent. -/
def singletonEmptyDNFOrInput (n : Nat) (hn : 1 ≤ n) :
    GeneratedOneStepInput n where
  layer := {
    parent := ParentKind.or
    gates := [GateSpec.dnf (BDFormula.or []) (emptyGateView n)]
  }
  w := 0
  s := 1
  ℓ := 1
  width := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [GateSpec.theDNF, emptyGateView]
  beat := by
    have hpos : 0 < (restrictionsWithStars n 1).card :=
      Finset.card_pos.mpr (restrictionsWithStars_nonempty hn)
    simpa using hpos

/-- Non-vacuity for the minimal B3 view: the singleton empty-DNF layer has a
generated one-step certificate. -/
theorem singletonEmptyDNFOr_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    ∃ C : GeneratedOneStepCertificate (singletonEmptyDNFOrInput n hn),
      C.ρ ∈ restrictionsWithStars n 1 ∧
      C.reducedChildren.length = 1 := by
  obtain ⟨C, hρ, _hsem, hcount, _hdepth⟩ :=
    generatedOneStepDepthReduction_exists (singletonEmptyDNFOrInput n hn)
  exact ⟨C, hρ, by simpa [singletonEmptyDNFOrInput] using hcount⟩

end GeneratedOneStepDepthReduction
end PvNP
