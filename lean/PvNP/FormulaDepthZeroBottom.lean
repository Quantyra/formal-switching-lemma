import PvNP.FormulaRecursiveDepth

/-!
# Depth-zero raw formulas as width-one bottom gates

`FormulaRecursiveDepth` proves that every surviving member of the full-depth
recursive top-child frontier has raw formula depth zero.  This module turns that
syntactic fact into the bottom-layer witness needed by later B4 decomposition
work: depth-zero formulas are constants or literals, and each such formula has
an exact simple DNF view of width at most one.

## HONEST SCOPE STATEMENT (read this)

* This is bottom-layer synthesis for raw formulas already known to have
  `depth = 0`.
* It does not build a full depth-`d` layered decomposition, does not combine
  frontier gates into a global certificate, and does not prove a `t(d,s)`
  switching schedule.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaDepthZeroBottom

open CNFModel
open BoundedDepthFrege
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open FormulaRecursiveDepth

/-! ## Exact width-one-or-less DNF witnesses -/

/-- The DNF computing constant true: one empty term. -/
def trueDNF (n : Nat) : DNF n := [[]]

/-- The DNF computing constant false: no terms. -/
def falseDNF (n : Nat) : DNF n := []

/-- The DNF computing one literal: one singleton term. -/
def literalDNF {n : Nat} (l : Literal n) : DNF n := [[l]]

theorem trueDNF_simple (n : Nat) : SimpleDNF (trueDNF n) := by
  intro t ht
  have ht' : t = [] := by simpa [trueDNF] using ht
  subst t
  simp [SimpleTerm]

theorem falseDNF_simple (n : Nat) : SimpleDNF (falseDNF n) := by
  intro t ht
  simp [falseDNF] at ht

theorem literalDNF_simple {n : Nat} (l : Literal n) :
    SimpleDNF (literalDNF l) := by
  intro t ht
  have ht' : t = [l] := by simpa [literalDNF] using ht
  subst t
  simp [SimpleTerm]

theorem widthDNF_trueDNF (n : Nat) :
    widthDNF (trueDNF n) = 0 := by
  simp [trueDNF, widthDNF, termWidth]

theorem widthDNF_falseDNF (n : Nat) :
    widthDNF (falseDNF n) = 0 := by
  simp [falseDNF, widthDNF]

theorem widthDNF_literalDNF {n : Nat} (l : Literal n) :
    widthDNF (literalDNF l) = 1 := by
  simp [literalDNF, widthDNF, termWidth]

/-! ## Exact DNF views for depth-zero formulas -/

/-- Exact simple DNF view for the true formula. -/
def trueFormulaDNFView (n : Nat) :
    DNFView (BDFormula.tru : BDFormula n) where
  D := trueDNF n
  sem_eq := fun a => by
    simp [trueDNF, eval_tru, dnfEval, termEval]
  simple := trueDNF_simple n

/-- Exact simple DNF view for the false formula. -/
def falseFormulaDNFView (n : Nat) :
    DNFView (BDFormula.fls : BDFormula n) where
  D := falseDNF n
  sem_eq := fun a => by
    simp [falseDNF, eval_fls, dnfEval]
  simple := falseDNF_simple n

/-- Exact simple DNF view for a literal formula. -/
def literalFormulaDNFView {n : Nat} (l : Literal n) :
    DNFView (BDFormula.lit l) where
  D := literalDNF l
  sem_eq := fun a => by
    simp [literalDNF, eval_lit, dnfEval, termEval]
  simple := literalDNF_simple l

/-- A raw formula of depth zero is exactly a constant or a literal. -/
theorem depthZeroFormula_cases {n : Nat} (F : BDFormula n)
    (hdepth : depth F = 0) :
    F = BDFormula.tru ∨ F = BDFormula.fls ∨
      ∃ l : Literal n, F = BDFormula.lit l := by
  cases F with
  | tru =>
      exact Or.inl rfl
  | fls =>
      exact Or.inr (Or.inl rfl)
  | lit l =>
      exact Or.inr (Or.inr ⟨l, rfl⟩)
  | and children =>
      simp [depth] at hdepth
  | or children =>
      simp [depth] at hdepth

/-- Synthesize an exact simple DNF view from a proof that raw formula depth is
zero. -/
def depthZeroFormulaDNFView {n : Nat} :
    (F : BDFormula n) -> depth F = 0 -> DNFView F
  | .tru, _ => trueFormulaDNFView n
  | .fls, _ => falseFormulaDNFView n
  | .lit l, _ => literalFormulaDNFView l
  | .and _children, hdepth => by
      simp [depth] at hdepth
  | .or _children, hdepth => by
      simp [depth] at hdepth

/-- Package a depth-zero raw formula as a `GateSpec.dnf`. -/
def depthZeroFormulaGate {n : Nat} (F : BDFormula n)
    (hdepth : depth F = 0) : GateSpec n :=
  GateSpec.dnf F (depthZeroFormulaDNFView F hdepth)

theorem depthZeroFormulaGate_formula {n : Nat} (F : BDFormula n)
    (hdepth : depth F = 0) :
    (depthZeroFormulaGate F hdepth).formula = F := rfl

theorem depthZeroFormulaGate_width_le_one {n : Nat} (F : BDFormula n)
    (hdepth : depth F = 0) :
    widthDNF (depthZeroFormulaGate F hdepth).theDNF <= 1 := by
  cases F with
  | tru =>
      change widthDNF (trueDNF n) <= 1
      rw [widthDNF_trueDNF]
      omega
  | fls =>
      change widthDNF (falseDNF n) <= 1
      rw [widthDNF_falseDNF]
      omega
  | lit l =>
      change widthDNF (literalDNF l) <= 1
      rw [widthDNF_literalDNF]
  | and children =>
      simp [depth] at hdepth
  | or children =>
      simp [depth] at hdepth

/-! ## Full-depth frontier bottom gates -/

/-- Any full-depth recursive frontier member can be packaged as a width-one
bottom `GateSpec.dnf`. -/
def fullDepthFrontierFormulaGate {n : Nat} (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier (depth F) F) : GateSpec n :=
  depthZeroFormulaGate child (formulaDepthFrontier_fullDepth_zero F child hchild)

theorem fullDepthFrontierFormulaGate_formula {n : Nat}
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier (depth F) F) :
    (fullDepthFrontierFormulaGate F child hchild).formula = child := rfl

theorem fullDepthFrontierFormulaGate_width_le_one {n : Nat}
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier (depth F) F) :
    widthDNF (fullDepthFrontierFormulaGate F child hchild).theDNF <= 1 := by
  exact depthZeroFormulaGate_width_le_one child
    (formulaDepthFrontier_fullDepth_zero F child hchild)

/-- Packaged bottom-gate witness for any full-depth frontier member. -/
structure FullDepthFrontierBottomGate {n : Nat}
    (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier (depth F) F) where
  gate : GateSpec n
  formula_eq : gate.formula = child
  width_le_one : widthDNF gate.theDNF <= 1

/-- Construct the packaged bottom-gate witness for a full-depth frontier member. -/
def fullDepthFrontierBottomGate {n : Nat} (F child : BDFormula n)
    (hchild : child ∈ formulaDepthFrontier (depth F) F) :
    FullDepthFrontierBottomGate F child hchild where
  gate := fullDepthFrontierFormulaGate F child hchild
  formula_eq := fullDepthFrontierFormulaGate_formula F child hchild
  width_le_one := fullDepthFrontierFormulaGate_width_le_one F child hchild

/-! ## Full-depth frontier bottom layers -/

/-- The full-depth recursive frontier, reified as bottom `GateSpec.dnf` gates. -/
def fullDepthFrontierGateList {n : Nat} (F : BDFormula n) :
    List (GateSpec n) :=
  (formulaDepthFrontier (depth F) F).attach.map
    (fun child => fullDepthFrontierFormulaGate F child.1 child.2)

theorem fullDepthFrontierGateList_length {n : Nat} (F : BDFormula n) :
    (fullDepthFrontierGateList F).length =
      (formulaDepthFrontier (depth F) F).length := by
  simp [fullDepthFrontierGateList]

theorem fullDepthFrontierGateList_formulas {n : Nat} (F : BDFormula n) :
    (fullDepthFrontierGateList F).map GateSpec.formula =
      formulaDepthFrontier (depth F) F := by
  unfold fullDepthFrontierGateList
  rw [List.map_map]
  change (formulaDepthFrontier (depth F) F).attach.map
      (fun child => child.1) = formulaDepthFrontier (depth F) F
  rw [List.attach_map_val (formulaDepthFrontier (depth F) F) (fun child => child)]
  simp

theorem fullDepthFrontierGateList_width_le_one {n : Nat} (F : BDFormula n) :
    forall g, g ∈ fullDepthFrontierGateList F -> widthDNF g.theDNF <= 1 := by
  intro g hg
  unfold fullDepthFrontierGateList at hg
  rcases List.mem_map.mp hg with ⟨child, _hchild, rfl⟩
  exact fullDepthFrontierFormulaGate_width_le_one F child.1 child.2

/-- Packaged bottom layer for the full-depth frontier. -/
structure FullDepthFrontierBottomLayer {n : Nat} (F : BDFormula n) where
  gates : List (GateSpec n)
  formulas_eq : gates.map GateSpec.formula =
    formulaDepthFrontier (depth F) F
  gate_width : forall g, g ∈ gates -> widthDNF g.theDNF <= 1
  gate_count : gates.length = (formulaDepthFrontier (depth F) F).length

/-- Construct the packaged bottom layer for the full-depth frontier. -/
def fullDepthFrontierBottomLayer {n : Nat} (F : BDFormula n) :
    FullDepthFrontierBottomLayer F where
  gates := fullDepthFrontierGateList F
  formulas_eq := fullDepthFrontierGateList_formulas F
  gate_width := fullDepthFrontierGateList_width_le_one F
  gate_count := fullDepthFrontierGateList_length F

end FormulaDepthZeroBottom
end PvNP
