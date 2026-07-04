import PvNP.FormulaStructuralSchedule

/-!
# Raw-formula one-step depth decomposition

`FormulaTruthTableView` and `FormulaStructuralSchedule` route positive-depth
raw formulas through a synthesized top `FrozenDepthView`.  This module exposes
the structural fact that makes that route a real depth-decomposition step:
every immediate child formula in the synthesized layer has strictly smaller
`depth` than the original formula.

## HONEST SCOPE STATEMENT (read this)

* This is a one-step structural peel for positive-depth raw formulas.  It is
  not a complete recursive decomposition algorithm and it does not synthesize
  product/counting hypotheses.
* Child gates still use the truth-table/path-DNF fallback from
  `FormulaTruthTableView`; this proves a syntactic depth decrease, not an
  efficient bottom-width bound.
* Leaves and constants are excluded by positive depth.  They still do not have
  an exact identity parent inside `MinimalLayeredFormula`.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower bound,
  NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a statement
  about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaDepthDecomposition

open CNFModel
open BoundedDepthFrege
open GeneratedOneStepDepthReduction
open FormulaTruthTableView

/-! ## Public list-depth helpers -/

theorem mem_le_foldr_max {xs : List Nat} {x : Nat} (hx : x ∈ xs) :
    x <= xs.foldr Nat.max 0 := by
  induction xs with
  | nil =>
      exact absurd hx (List.not_mem_nil x)
  | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hxys
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hxys) (Nat.le_max_right _ _)

theorem child_depth_le_foldr_depths {n : Nat} {children : List (BDFormula n)}
    {child : BDFormula n} (hchild : child ∈ children) :
    depth child <= (children.attach.map (fun f => depth f.1)).foldr Nat.max 0 := by
  apply mem_le_foldr_max
  exact List.mem_map.mpr
    ⟨⟨child, hchild⟩, List.mem_attach children ⟨child, hchild⟩, rfl⟩

/-! ## Top-child depth decrease -/

/-- Every exposed top child of a raw formula is strictly shallower than the
formula itself.  This is the structural depth-decrease fact behind the
positive-depth `FrozenDepthView` synthesis. -/
theorem topChildren_depth_lt {n : Nat} (F child : BDFormula n)
    (hchild : child ∈ topChildren F) :
    depth child < depth F := by
  cases F with
  | tru =>
      simp [topChildren] at hchild
  | fls =>
      simp [topChildren] at hchild
  | lit l =>
      simp [topChildren] at hchild
  | and children =>
      have hle := child_depth_le_foldr_depths (children := children)
        (child := child) hchild
      rw [depth]
      omega
  | or children =>
      have hle := child_depth_le_foldr_depths (children := children)
        (child := child) hchild
      rw [depth]
      omega

/-- Equivalent predecessor-budget form of `topChildren_depth_lt`. -/
theorem topChildren_depth_le_pred {n : Nat} (F child : BDFormula n)
    (hchild : child ∈ topChildren F) :
    depth child <= depth F - 1 := by
  have hlt := topChildren_depth_lt F child hchild
  omega

/-! ## Synthesized-view child depth decrease -/

/-- Every gate formula in the synthesized positive-depth frozen view is
strictly shallower than the original raw formula. -/
theorem positiveDepthFrozenDepthView_gate_formula_depth_lt {n : Nat}
    (F : BDFormula n) (hpos : 0 < depth F) :
    forall g, g ∈ (positiveDepthFrozenDepthView F hpos).layer.gates ->
      depth g.formula < depth F := by
  cases F with
  | tru =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | fls =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | lit l =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | and children =>
      intro g hg
      change g ∈ children.map formulaGate at hg
      rcases List.mem_map.mp hg with ⟨child, hchild, rfl⟩
      simpa [formulaGate]
        using
        topChildren_depth_lt (BDFormula.and children) child
          (by simpa [topChildren] using hchild)
  | or children =>
      intro g hg
      change g ∈ children.map formulaGate at hg
      rcases List.mem_map.mp hg with ⟨child, hchild, rfl⟩
      simpa [formulaGate]
        using
        topChildren_depth_lt (BDFormula.or children) child
          (by simpa [topChildren] using hchild)

/-- Predecessor-budget form for synthesized-view gate formulas. -/
theorem positiveDepthFrozenDepthView_gate_formula_depth_le_pred {n : Nat}
    (F : BDFormula n) (hpos : 0 < depth F) :
    forall g, g ∈ (positiveDepthFrozenDepthView F hpos).layer.gates ->
      depth g.formula <= depth F - 1 := by
  intro g hg
  have hlt := positiveDepthFrozenDepthView_gate_formula_depth_lt F hpos g hg
  omega

/-! ## Packaged one-step peel -/

/-- A one-step structural peel of a positive-depth formula: a synthesized
frozen view plus the proof that every gate formula is strictly shallower. -/
structure PositiveDepthPeel {n : Nat} (F : BDFormula n) where
  hpos : 0 < depth F
  view : FrozenDepthView.FrozenDepthView n F (depth F)
  gateFormulaDepth : forall g, g ∈ view.layer.gates -> depth g.formula < depth F

/-- Construct the one-step peel from raw positive-depth syntax. -/
def positiveDepthPeel {n : Nat} (F : BDFormula n) (hpos : 0 < depth F) :
    PositiveDepthPeel F where
  hpos := hpos
  view := positiveDepthFrozenDepthView F hpos
  gateFormulaDepth := positiveDepthFrozenDepthView_gate_formula_depth_lt F hpos

theorem positiveDepthPeel_gateCount {n : Nat} (F : BDFormula n)
    (hpos : 0 < depth F) :
    (positiveDepthPeel F hpos).view.gateCount = topChildCount F := by
  simp [positiveDepthPeel, positiveDepthFrozenDepthView_gateCount]

theorem positiveDepthPeel_gateFormulaDepth_le_pred {n : Nat}
    (F : BDFormula n) (hpos : 0 < depth F) :
    forall g, g ∈ (positiveDepthPeel F hpos).view.layer.gates ->
      depth g.formula <= depth F - 1 := by
  simpa [positiveDepthPeel] using
    positiveDepthFrozenDepthView_gate_formula_depth_le_pred F hpos

end FormulaDepthDecomposition
end PvNP
