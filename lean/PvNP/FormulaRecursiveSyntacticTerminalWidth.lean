import PvNP.FormulaRecursiveSyntacticTerminalStructural
import PvNP.FormulaRecursiveSyntacticTerminalConcrete
import PvNP.FormulaSyntacticDNF

/-!
# Efficient width-profile synthesis for syntactic-terminal packed families

This module advances Gate B after S2150 by synthesizing a non-fallback width
envelope from formula structure alone.  The synthesized profile is the S2142
terminal-sharp budget: width one at the full-depth frontier and formula size at
intermediate frontiers.  The depth-indexed envelope is `1` for depth-zero
formulas and the formula-size cap otherwise, so it is never the ambient
truth-table fallback `n`.  For depth-zero restricted families the envelope is
strictly smaller than any ambient arity `n > 1`.

S2152 extends the package with two honest intermediate-depth surfaces for a
restricted positive-depth witness (`productCountingGatedLiteralTrue`):

* **Part A (budget efficient envelope):** the S2142 budget envelope at positive
  depth equals the size cap (not ambient `n`), discharges structural data, and
  routes S2142 final-tree consumers under unchanged `t(d,s)=S(d)*(s-1)`.
* **Part B (intermediate actual-width envelope):** a *parallel* depth-indexed
  actual-width envelope that is `1` whenever formula depth is at most one, hence
  strictly smaller than size cap `3` and ambient arity on the depth-1 product
  family.  This does **not** change budget `WidthEnvelope` semantics (which
  still require `W ≥ formulaSize` at non-terminal levels).

The package routes S2142 final-tree consumers under the unchanged budget
`t(d,s)=S(d)*(s-1)`.  It does not improve thresholds, synthesize arbitrary
formula-class schedules, prove arbitrary normalization, arbitrary
AC0/bounded-depth collapse, full B4, PHP switching, Frege/PHP, NP/circuit lower
bounds, P-vs-NP, or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalWidth

open BoundedDepthFrege
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalConcrete
open FormulaRecursiveSyntacticTerminalExact
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalProduct
open FormulaRecursiveSyntacticTerminalRegime
open FormulaRecursiveSyntacticTerminalStructural
open FormulaRecursiveLayerProfile
open FormulaSyntacticDNF
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open CNFModel
open SwitchingLemmaStatement

/-! ## Synthesized efficient width profile -/

/-- Level-wise efficient width profile: terminal-sharp S2142 budget synthesized
from formula structure (not ambient `n`). -/
def efficientSyntacticTerminalWidthProfile {n : Nat} (F : BDFormula n)
    (level : Nat) : Nat :=
  syntacticTerminalFrontierWidthBudget F level

/-- Depth-indexed efficient width envelope synthesized from the packed formula:
depth-zero formulas get envelope `1`; positive-depth formulas get the raw
formula-size cap. -/
def efficientSyntacticTerminalWidthEnvelope
    (F : SyntacticTerminalPackedFamily) (d : Nat) : Nat :=
  if depth (syntacticTerminalPackedFamilyFormula F d) = 0 then 1
  else syntacticTerminalPackedFamilySizeCap F d

/-- The synthesized profile agrees with the S2142 width budget. -/
theorem efficientSyntacticTerminalWidthProfile_eq_budget {n : Nat}
    (F : BDFormula n) (level : Nat) :
    efficientSyntacticTerminalWidthProfile F level =
      syntacticTerminalFrontierWidthBudget F level :=
  rfl

/-- The synthesized depth-indexed envelope is at most the formula-size cap. -/
theorem efficientSyntacticTerminalWidthEnvelope_le_sizeCap
    (F : SyntacticTerminalPackedFamily) (d : Nat) :
    efficientSyntacticTerminalWidthEnvelope F d ≤
      syntacticTerminalPackedFamilySizeCap F d := by
  unfold efficientSyntacticTerminalWidthEnvelope
  split_ifs with hdepth
  · have hpos : 0 < formulaSize (syntacticTerminalPackedFamilyFormula F d) :=
      formulaSize_pos _
    simpa [syntacticTerminalPackedFamilySizeCap] using hpos
  · exact Nat.le_refl _

/-- Depth-zero formulas synthesize envelope exactly `1`. -/
theorem efficientSyntacticTerminalWidthEnvelope_of_depth_zero
    (F : SyntacticTerminalPackedFamily) (d : Nat)
    (hdepth : depth (syntacticTerminalPackedFamilyFormula F d) = 0) :
    efficientSyntacticTerminalWidthEnvelope F d = 1 := by
  simp [efficientSyntacticTerminalWidthEnvelope, hdepth]

/-- Positive-depth formulas synthesize envelope equal to the size cap. -/
theorem efficientSyntacticTerminalWidthEnvelope_of_pos_depth
    (F : SyntacticTerminalPackedFamily) (d : Nat)
    (hdepth : depth (syntacticTerminalPackedFamilyFormula F d) ≠ 0) :
    efficientSyntacticTerminalWidthEnvelope F d =
      syntacticTerminalPackedFamilySizeCap F d := by
  simp [efficientSyntacticTerminalWidthEnvelope, hdepth]

/-! ## Width-envelope discharge -/

/-- The synthesized envelope covers every in-depth S2142 width budget. -/
theorem SyntacticTerminalPackedFamilyWidthEnvelope.of_efficient
    (F : SyntacticTerminalPackedFamily) :
    SyntacticTerminalPackedFamilyWidthEnvelope F
      (efficientSyntacticTerminalWidthEnvelope F) := by
  intro d level hk
  unfold efficientSyntacticTerminalWidthEnvelope
  by_cases hdepth : depth (syntacticTerminalPackedFamilyFormula F d) = 0
  · have hlevel : level = 0 := by
      have : level ≤ 0 := by simpa [hdepth] using hk
      exact Nat.eq_zero_of_le_zero this
    subst hlevel
    simp [syntacticTerminalFrontierWidthBudget, hdepth, terminalLayerWidthBudget]
  · have hne : depth (syntacticTerminalPackedFamilyFormula F d) ≠ 0 := hdepth
    simp only [hne, ↓reduceIte]
    exact syntacticTerminalFrontierWidthBudget_le_classSize
      (syntacticTerminalPackedFamilyFormula F d)
      (fun _ => syntacticTerminalPackedFamilySizeCap F d) d level
      (by simp [syntacticTerminalPackedFamilySizeCap])

/-- Structural data using the synthesized efficient width envelope and a supplied
class-size envelope. -/
theorem SyntacticTerminalPackedFamilyStructuralData.of_efficientWidth
    {F : SyntacticTerminalPackedFamily} {S : Nat → Nat}
    (hClass : SyntacticTerminalPackedFamilyClass F)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S) :
    SyntacticTerminalPackedFamilyStructuralData F S
      (efficientSyntacticTerminalWidthEnvelope F) :=
  ⟨hClass, hDepth, hSize, SyntacticTerminalPackedFamilyWidthEnvelope.of_efficient F⟩

/-! ## Non-fallback strictness -/

/-- Depth-zero restricted family: every packed formula has depth zero. -/
def SyntacticTerminalPackedFamilyDepthZero
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∀ d, depth (syntacticTerminalPackedFamilyFormula F d) = 0

/-- For depth-zero families the efficient envelope is constantly `1`. -/
theorem efficientSyntacticTerminalWidthEnvelope_eq_one_of_depthZero
    {F : SyntacticTerminalPackedFamily}
    (hZero : SyntacticTerminalPackedFamilyDepthZero F) (d : Nat) :
    efficientSyntacticTerminalWidthEnvelope F d = 1 :=
  efficientSyntacticTerminalWidthEnvelope_of_depth_zero F d (hZero d)

/-- Non-fallback strictness: for depth-zero families the efficient envelope is
strictly smaller than any ambient arity `n > 1`. -/
theorem efficientSyntacticTerminalWidthEnvelope_lt_ambient_of_depthZero
    {F : SyntacticTerminalPackedFamily} {d n : Nat}
    (hZero : SyntacticTerminalPackedFamilyDepthZero F)
    (hn : 1 < n) :
    efficientSyntacticTerminalWidthEnvelope F d < n := by
  simpa [efficientSyntacticTerminalWidthEnvelope_eq_one_of_depthZero hZero d] using hn

/-- Under S2145 ambient adequacy with positive size cap, the efficient envelope
is strictly smaller than the packed ambient arity (non-fallback vs ambient). -/
theorem efficientSyntacticTerminalWidthEnvelope_lt_arity_of_ambientAdequate
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat → Nat} {d : Nat}
    (hAmb : SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf)
    (hSizePos : 0 < syntacticTerminalPackedFamilySizeCap F d) :
    efficientSyntacticTerminalWidthEnvelope F d <
      syntacticTerminalPackedFamilyArity F d := by
  have hle := efficientSyntacticTerminalWidthEnvelope_le_sizeCap F d
  set M := syntacticTerminalPackedFamilySizeCap F d
  set N := syntacticTerminalPackedFamilyArity F d
  have hthr : syntacticTerminalClassCoarseEntryThreshold M (roundsOf d) ≤ N :=
    hAmb d
  have hpow : 1 ≤ (64 * M) ^ roundsOf d :=
    Nat.one_le_pow _ _ (Nat.mul_pos (by decide : 0 < 64) hSizePos)
  have hM_lt_128MM : M < 128 * M * M := by
    have hstep : M < 128 * M :=
      calc
        M = 1 * M := (Nat.one_mul M).symm
        _ < 128 * M := Nat.mul_lt_mul_of_pos_right (by decide : 1 < 128) hSizePos
    exact Nat.lt_of_lt_of_le hstep (Nat.le_mul_of_pos_right (128 * M) hSizePos)
  have hM_lt_base : M < 2 * ((64 * M) * M) := by
    have h128 : 128 * M * M = 2 * ((64 * M) * M) := by
      have hconst : (128 : Nat) = 2 * 64 := by decide
      calc
        128 * M * M = (2 * 64) * M * M := by rw [hconst]
        _ = 2 * (64 * M * M) := by
            ac_rfl
        _ = 2 * ((64 * M) * M) := by
            simp [Nat.mul_assoc]
    simpa [h128] using hM_lt_128MM
  have hbase_le_thr :
      2 * ((64 * M) * M) ≤
        syntacticTerminalClassCoarseEntryThreshold M (roundsOf d) := by
    unfold syntacticTerminalClassCoarseEntryThreshold
    have hfront : 2 * 1 ≤ 2 * (64 * M) ^ roundsOf d :=
      Nat.mul_le_mul_left 2 hpow
    simpa [Nat.mul_one, Nat.mul_assoc] using
      Nat.mul_le_mul hfront (Nat.le_refl ((64 * M) * M))
  have hcap_lt_thr :
      M < syntacticTerminalClassCoarseEntryThreshold M (roundsOf d) :=
    Nat.lt_of_lt_of_le hM_lt_base hbase_le_thr
  exact Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le hcap_lt_thr hthr)

/-! ## Concrete one-literal efficient-width witness -/

/-- The one-literal exact-threshold family is depth-zero. -/
theorem oneLiteralThresholdPackedFamily_depthZero
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyDepthZero
      (oneLiteralThresholdPackedFamily roundsOf) := by
  intro d
  simpa using oneLiteralThresholdPackedFamily_depth roundsOf d

/-- Efficient envelope is constantly `1` on the one-literal family. -/
theorem oneLiteralThresholdPackedFamily_efficientWidth
    (roundsOf : Nat → Nat) (d : Nat) :
    efficientSyntacticTerminalWidthEnvelope
      (oneLiteralThresholdPackedFamily roundsOf) d = 1 :=
  efficientSyntacticTerminalWidthEnvelope_eq_one_of_depthZero
    (oneLiteralThresholdPackedFamily_depthZero roundsOf) d

/-- Width envelope discharge for the one-literal family at constant `1`. -/
theorem oneLiteralThresholdPackedFamily_widthEnvelope_one
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyWidthEnvelope
      (oneLiteralThresholdPackedFamily roundsOf) (fun _ => 1) := by
  intro d level hk
  have hW := SyntacticTerminalPackedFamilyWidthEnvelope.of_efficient
    (oneLiteralThresholdPackedFamily roundsOf) d level hk
  simpa [oneLiteralThresholdPackedFamily_efficientWidth roundsOf d] using hW

/-- Class-size envelope at size cap `1`. -/
theorem oneLiteralThresholdPackedFamily_classSizeEnvelope_one
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClassSizeEnvelope
      (oneLiteralThresholdPackedFamily roundsOf) (fun _ => 1) := by
  intro d
  simpa [oneLiteralThresholdPackedFamily_sizeCap] using
    (Nat.le_refl 1)

/-- Structural ambient adequacy for the one-literal family at envelope `S≡1`. -/
theorem oneLiteralThresholdPackedFamily_structuralAmbientAdequate_one
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralAmbientAdequate
      (oneLiteralThresholdPackedFamily roundsOf) (fun _ => 1) roundsOf := by
  intro d
  simpa [oneLiteralThresholdPackedFamily_sizeCap,
    SyntacticTerminalPackedFamilyAmbientAdequate,
    syntacticTerminalPackedFamilyArity, oneLiteralThresholdPackedFamily,
    oneLiteralThresholdArity] using
    (oneLiteralThresholdPackedFamily_ambientAdequate roundsOf d)

/-- Structural data with class-size envelope `1` and efficient width envelope. -/
theorem oneLiteralThresholdPackedFamily_structuralData_efficient
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralData
      (oneLiteralThresholdPackedFamily roundsOf) (fun _ => 1)
      (efficientSyntacticTerminalWidthEnvelope
        (oneLiteralThresholdPackedFamily roundsOf)) :=
  SyntacticTerminalPackedFamilyStructuralData.of_efficientWidth
    (oneLiteralThresholdPackedFamily_class roundsOf)
    (oneLiteralThresholdPackedFamily_depthBound roundsOf)
    (oneLiteralThresholdPackedFamily_classSizeEnvelope_one roundsOf)

/-- Non-fallback: efficient width `1` is strictly below ambient arity for the
one-literal family. -/
theorem oneLiteralThresholdPackedFamily_efficientWidth_lt_arity
    (roundsOf : Nat → Nat) (d : Nat) :
    efficientSyntacticTerminalWidthEnvelope
        (oneLiteralThresholdPackedFamily roundsOf) d <
      syntacticTerminalPackedFamilyArity
        (oneLiteralThresholdPackedFamily roundsOf) d := by
  have hAmb := oneLiteralThresholdPackedFamily_ambientAdequate roundsOf
  have hSizePos : 0 < syntacticTerminalPackedFamilySizeCap
      (oneLiteralThresholdPackedFamily roundsOf) d := by
    simpa [oneLiteralThresholdPackedFamily_sizeCap]
  exact efficientSyntacticTerminalWidthEnvelope_lt_arity_of_ambientAdequate
    hAmb hSizePos

/-- S2142 final-tree route under efficient width synthesis for the one-literal
family, with class budget `t(d,s)=S(d)*(s-1)` at `S≡1`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_oneLiteralEfficientWidth
    (roundsOf : Nat → Nat) {d : Nat} (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (oneLiteralThresholdPackedFamily roundsOf) d) →
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula
          (oneLiteralThresholdPackedFamily roundsOf) d)
        (fun _ => 1) d (roundsOf d) parent
        (oneLiteralThresholdPackedFamily_class roundsOf d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_structural
      parent
      (oneLiteralThresholdPackedFamily_structuralData_efficient roundsOf)
      (oneLiteralThresholdPackedFamily_structuralAmbientAdequate_one roundsOf)

/-- Non-vacuity package: synthesized efficient width envelope is non-fallback
and routes S2142 consumers. -/
theorem exists_efficientWidthProfile_nonFallback_finalTreeRoute
    (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ S : Nat → Nat,
        SyntacticTerminalPackedFamilyDepthZero F ∧
        SyntacticTerminalPackedFamilyStructuralData F S
          (efficientSyntacticTerminalWidthEnvelope F) ∧
        SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
        (∀ d, efficientSyntacticTerminalWidthEnvelope F d = 1) ∧
        (∀ d, efficientSyntacticTerminalWidthEnvelope F d <
          syntacticTerminalPackedFamilyArity F d) := by
  refine ⟨oneLiteralThresholdPackedFamily roundsOf, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact oneLiteralThresholdPackedFamily_depthZero roundsOf
  · exact oneLiteralThresholdPackedFamily_structuralData_efficient roundsOf
  · exact oneLiteralThresholdPackedFamily_structuralAmbientAdequate_one roundsOf
  · intro d
    exact oneLiteralThresholdPackedFamily_efficientWidth roundsOf d
  · intro d
    exact oneLiteralThresholdPackedFamily_efficientWidth_lt_arity roundsOf d

/-! ## S2152 Part A — Positive-depth budget efficient envelope (productCounting) -/

/-- Positive formula-depth witness: some packed index has strictly positive depth. -/
def SyntacticTerminalPackedFamilyPosFormulaDepth
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∃ d, 0 < depth (syntacticTerminalPackedFamilyFormula F d)

/-- The product/counting family has positive formula depth (at every `d ≥ 1`). -/
theorem productCountingGatedLiteralTruePackedFamily_posFormulaDepth
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyPosFormulaDepth
      (productCountingGatedLiteralTruePackedFamily roundsOf) := by
  refine ⟨1, ?_⟩
  have h := productCountingGatedLiteralTrueDepth roundsOf 1
  simp at h
  simpa [h]

/-- Efficient budget envelope at depth-zero index of the product/counting family. -/
theorem productCountingGatedLiteralTruePackedFamily_efficientWidth_zero
    (roundsOf : Nat → Nat) :
    efficientSyntacticTerminalWidthEnvelope
      (productCountingGatedLiteralTruePackedFamily roundsOf) 0 = 1 := by
  have hdepth := productCountingGatedLiteralTrueDepth roundsOf 0
  simp at hdepth
  exact efficientSyntacticTerminalWidthEnvelope_of_depth_zero
    (productCountingGatedLiteralTruePackedFamily roundsOf) 0 hdepth

/-- Efficient budget envelope at positive depth equals the size cap (`3`). -/
theorem productCountingGatedLiteralTruePackedFamily_efficientWidth_succ
    (roundsOf : Nat → Nat) (d : Nat) :
    efficientSyntacticTerminalWidthEnvelope
      (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) = 3 := by
  have hdepth := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
  simp at hdepth
  have hne :
      depth (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1)) ≠ 0 := by
    simp [hdepth]
  have hW := efficientSyntacticTerminalWidthEnvelope_of_pos_depth
    (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) hne
  have hsize := productCountingGatedLiteralTrueSizeCap roundsOf (d + 1)
  simpa [hW, hsize, gatedLiteralTrueThresholdSizeCapIndex]

/-- Structural data with class-size envelope `S` and efficient budget width. -/
theorem productCountingGatedLiteralTruePackedFamily_structuralData_efficient
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralData
      (productCountingGatedLiteralTruePackedFamily roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf)
      (efficientSyntacticTerminalWidthEnvelope
        (productCountingGatedLiteralTruePackedFamily roundsOf)) :=
  SyntacticTerminalPackedFamilyStructuralData.of_efficientWidth
    (productCountingGatedLiteralTruePackedFamily_class roundsOf)
    (productCountingGatedLiteralTruePackedFamily_depthBound roundsOf)
    (productCountingGatedLiteralTruePackedFamily_classSizeEnvelope roundsOf)

/-- Structural ambient adequacy reuses the S2150 product/counting package. -/
theorem productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate_efficient
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralAmbientAdequate
      (productCountingGatedLiteralTruePackedFamily roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf) roundsOf :=
  productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate roundsOf

/-- Non-fallback vs ambient: efficient budget width is strictly below arity at
positive depth indices. -/
theorem productCountingGatedLiteralTruePackedFamily_efficientWidth_lt_arity_succ
    (roundsOf : Nat → Nat) (d : Nat) :
    efficientSyntacticTerminalWidthEnvelope
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) <
      syntacticTerminalPackedFamilyArity
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) := by
  have hAmb := productCountingGatedLiteralTruePackedFamily_ambientAdequate roundsOf
  have hSizePos : 0 < syntacticTerminalPackedFamilySizeCap
      (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) := by
    simpa [productCountingGatedLiteralTrueSizeCap,
      gatedLiteralTrueThresholdSizeCapIndex]
  exact efficientSyntacticTerminalWidthEnvelope_lt_arity_of_ambientAdequate
    hAmb hSizePos

/-- S2142 final-tree route under efficient budget width for the product/counting
family, with class budget `t(d,s)=S(d)*(s-1)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_productCountingEfficientWidth
    (roundsOf : Nat → Nat) {d : Nat} (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) d) →
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula
          (productCountingGatedLiteralTruePackedFamily roundsOf) d)
        (productCountingGatedLiteralTrueClassSize roundsOf) d (roundsOf d) parent
        (productCountingGatedLiteralTruePackedFamily_class roundsOf d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_structural
      parent
      (productCountingGatedLiteralTruePackedFamily_structuralData_efficient roundsOf)
      (productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate_efficient
        roundsOf)

/-! ## S2152 Part B — Intermediate actual-width envelope (stricter than sizeCap) -/

/-- Intermediate actual-width envelope: `1` whenever formula depth is at most one,
and the raw size cap otherwise.  On the concrete product/counting depth-1 witness
(`lit OR true`) this is backed by an actual syntactic-DNF width bound of `1`,
but the definition itself is only a depth-indexed numeric profile — not a proved
gate-wise width fact for arbitrary depth-1 syntactic-terminal formulas.  This is
a *parallel* actual-width surface; it does not discharge the S2142 budget
`WidthEnvelope` (which still requires `W ≥ formulaSize` at non-terminal levels).
-/
def intermediateEfficientSyntacticTerminalWidthEnvelope
    (F : SyntacticTerminalPackedFamily) (d : Nat) : Nat :=
  if depth (syntacticTerminalPackedFamilyFormula F d) ≤ 1 then 1
  else syntacticTerminalPackedFamilySizeCap F d

/-- The intermediate envelope never exceeds the formula-size cap. -/
theorem intermediateEfficientSyntacticTerminalWidthEnvelope_le_sizeCap
    (F : SyntacticTerminalPackedFamily) (d : Nat) :
    intermediateEfficientSyntacticTerminalWidthEnvelope F d ≤
      syntacticTerminalPackedFamilySizeCap F d := by
  unfold intermediateEfficientSyntacticTerminalWidthEnvelope
  split_ifs with hdepth
  · have hpos : 0 < formulaSize (syntacticTerminalPackedFamilyFormula F d) :=
      formulaSize_pos _
    simpa [syntacticTerminalPackedFamilySizeCap] using hpos
  · exact Nat.le_refl _

/-- Depth ≤ 1 formulas synthesize intermediate envelope exactly `1`. -/
theorem intermediateEfficientSyntacticTerminalWidthEnvelope_of_depth_le_one
    (F : SyntacticTerminalPackedFamily) (d : Nat)
    (hdepth : depth (syntacticTerminalPackedFamilyFormula F d) ≤ 1) :
    intermediateEfficientSyntacticTerminalWidthEnvelope F d = 1 := by
  simp [intermediateEfficientSyntacticTerminalWidthEnvelope, hdepth]

/-- When depth is exactly one and the size cap exceeds one, the intermediate
envelope is strictly smaller than the size cap. -/
theorem intermediateEfficient_lt_sizeCap_of_depth_one_size_gt_one
    (F : SyntacticTerminalPackedFamily) (d : Nat)
    (hdepth : depth (syntacticTerminalPackedFamilyFormula F d) = 1)
    (hsize : 1 < syntacticTerminalPackedFamilySizeCap F d) :
    intermediateEfficientSyntacticTerminalWidthEnvelope F d <
      syntacticTerminalPackedFamilySizeCap F d := by
  have hle : depth (syntacticTerminalPackedFamilyFormula F d) ≤ 1 := by
    simp [hdepth]
  simpa [intermediateEfficientSyntacticTerminalWidthEnvelope_of_depth_le_one F d hle]
    using hsize

/-- Product/counting intermediate envelope at positive depth is constantly `1`. -/
theorem productCountingGatedLiteralTruePackedFamily_intermediateEfficient_succ
    (roundsOf : Nat → Nat) (d : Nat) :
    intermediateEfficientSyntacticTerminalWidthEnvelope
      (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) = 1 := by
  have hdepth := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
  simp at hdepth
  have hle :
      depth (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1)) ≤ 1 := by
    simp [hdepth]
  exact intermediateEfficientSyntacticTerminalWidthEnvelope_of_depth_le_one
    (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) hle

/-- Intermediate envelope is strictly smaller than size cap at positive depth
(`1 < 3`). -/
theorem productCountingGatedLiteralTruePackedFamily_intermediateEfficient_lt_sizeCap_succ
    (roundsOf : Nat → Nat) (d : Nat) :
    intermediateEfficientSyntacticTerminalWidthEnvelope
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) <
      syntacticTerminalPackedFamilySizeCap
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) := by
  have hdepth := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
  simp at hdepth
  have hsize :
      1 < syntacticTerminalPackedFamilySizeCap
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) := by
    simpa [productCountingGatedLiteralTrueSizeCap,
      gatedLiteralTrueThresholdSizeCapIndex]
  exact intermediateEfficient_lt_sizeCap_of_depth_one_size_gt_one
    (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) hdepth hsize

/-- Intermediate envelope is strictly smaller than ambient arity at positive
depth. -/
theorem productCountingGatedLiteralTruePackedFamily_intermediateEfficient_lt_arity_succ
    (roundsOf : Nat → Nat) (d : Nat) :
    intermediateEfficientSyntacticTerminalWidthEnvelope
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) <
      syntacticTerminalPackedFamilyArity
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) := by
  have hW :
      intermediateEfficientSyntacticTerminalWidthEnvelope
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) = 1 :=
    productCountingGatedLiteralTruePackedFamily_intermediateEfficient_succ
      roundsOf d
  have hEff :
      efficientSyntacticTerminalWidthEnvelope
          (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) <
        syntacticTerminalPackedFamilyArity
          (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) :=
    productCountingGatedLiteralTruePackedFamily_efficientWidth_lt_arity_succ
      roundsOf d
  have hEffEq :
      efficientSyntacticTerminalWidthEnvelope
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) = 3 :=
    productCountingGatedLiteralTruePackedFamily_efficientWidth_succ roundsOf d
  -- 1 < arity follows from 3 < arity (or more directly: 1 ≤ 3 and 3 < arity)
  have h1_le_3 : (1 : Nat) ≤ 3 := by decide
  have h3_lt :
      (3 : Nat) <
        syntacticTerminalPackedFamilyArity
          (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) := by
    simpa [hEffEq] using hEff
  have h1_lt : (1 : Nat) <
      syntacticTerminalPackedFamilyArity
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1) :=
    Nat.lt_of_le_of_lt h1_le_3 h3_lt
  simpa [hW] using h1_lt

/-- Formula depth is exactly one at every positive index of the product family. -/
theorem productCountingGatedLiteralTruePackedFamily_depth_eq_one_of_pos
    (roundsOf : Nat → Nat) (d : Nat) (hd : 0 < d) :
    depth (syntacticTerminalPackedFamilyFormula
      (productCountingGatedLiteralTruePackedFamily roundsOf) d) = 1 := by
  cases d with
  | zero => exact absurd hd (Nat.lt_irrefl 0)
  | succ d =>
      have h := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
      simp at h
      exact h

/-! ### Supporting actual DNF-width evidence (non-vacuous intermediate envelope) -/

/-- Syntactic DNF of a positive literal has width exactly one. -/
private theorem widthDNF_syntacticDNF_lit_eq_one {n : Nat} (l : Literal n) :
    widthDNF (syntacticDNF (BDFormula.lit l : BDFormula n)) = 1 := by
  simp [syntacticDNF, FormulaSyntacticDNF.literalDNF, widthDNF, termWidth]

/-- Syntactic DNF of constant true has width zero. -/
private theorem widthDNF_syntacticDNF_tru_eq_zero (n : Nat) :
    widthDNF (syntacticDNF (BDFormula.tru : BDFormula n)) = 0 := by
  simp [syntacticDNF, FormulaSyntacticDNF.trueDNF, widthDNF, termWidth]

/-- Actual syntactic DNF width of the depth-1 product formula `lit OR true`
is at most one (supporting evidence that the intermediate envelope is not
vacuous). -/
theorem productCountingGatedLiteralTrueFormula_succ_widthDNF_syntactic_le_one
    (roundsOf : Nat → Nat) (d : Nat) :
    widthDNF (syntacticDNF
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1))) ≤ 1 := by
  change widthDNF (syntacticDNF
    (BDFormula.or
      [productCountingGatedLiteralTrueLit0 roundsOf (d + 1), BDFormula.tru])) ≤ 1
  -- syntacticOrDNF [lit, tru] = orDNF (litDNF) (orDNF trueDNF falseDNF)
  have hLit :
      widthDNF (syntacticDNF
        (productCountingGatedLiteralTrueLit0 roundsOf (d + 1))) ≤ 1 := by
    have h := widthDNF_syntacticDNF_lit_eq_one
      ({ var := ⟨0, productCountingGatedLiteralTrueArity_pos roundsOf (d + 1)⟩
         sign := true } : Literal _)
    simpa [productCountingGatedLiteralTrueLit0] using (le_of_eq h)
  have hTru :
      widthDNF (syntacticDNF (BDFormula.tru :
        BDFormula (productCountingGatedLiteralTrueArity roundsOf (d + 1)))) ≤ 1 := by
    have h := widthDNF_syntacticDNF_tru_eq_zero
      (productCountingGatedLiteralTrueArity roundsOf (d + 1))
    exact Nat.le_trans (le_of_eq h) (by decide : (0 : Nat) ≤ 1)
  have hNil :
      widthDNF (syntacticOrDNF
        ([] : List (BDFormula (productCountingGatedLiteralTrueArity roundsOf (d + 1))))) ≤ 1 := by
    simp [syntacticOrDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
  have hRest :
      widthDNF (syntacticOrDNF
        ([BDFormula.tru] :
          List (BDFormula (productCountingGatedLiteralTrueArity roundsOf (d + 1))))) ≤ 1 := by
    simp only [syntacticOrDNF]
    exact widthDNF_orDNF_le hTru hNil
  simp only [syntacticDNF, syntacticOrDNF]
  exact widthDNF_orDNF_le hLit hRest

/-- Non-vacuity package: intermediate-depth efficient width is stricter than both
size cap and ambient arity on a positive-depth restricted family, while the
S2142 final-tree route still discharges via the *budget* efficient envelope. -/
theorem exists_intermediateDepth_efficientWidth_stricter_than_sizeCap_and_arity_finalTreeRoute
    (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ S : Nat → Nat,
        SyntacticTerminalPackedFamilyPosFormulaDepth F ∧
        SyntacticTerminalPackedFamilyStructuralData F S
          (efficientSyntacticTerminalWidthEnvelope F) ∧
        SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
        (∀ d, 0 < d →
          intermediateEfficientSyntacticTerminalWidthEnvelope F d = 1) ∧
        (∀ d, 0 < d →
          intermediateEfficientSyntacticTerminalWidthEnvelope F d <
            syntacticTerminalPackedFamilySizeCap F d) ∧
        (∀ d, 0 < d →
          intermediateEfficientSyntacticTerminalWidthEnvelope F d <
            syntacticTerminalPackedFamilyArity F d) ∧
        (∀ d, 0 < d →
          depth (syntacticTerminalPackedFamilyFormula F d) = 1) := by
  refine ⟨productCountingGatedLiteralTruePackedFamily roundsOf,
    productCountingGatedLiteralTrueClassSize roundsOf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact productCountingGatedLiteralTruePackedFamily_posFormulaDepth roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_structuralData_efficient roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate_efficient
      roundsOf
  · intro d hd
    cases d with
    | zero => exact absurd hd (Nat.lt_irrefl 0)
    | succ d =>
        exact productCountingGatedLiteralTruePackedFamily_intermediateEfficient_succ
          roundsOf d
  · intro d hd
    cases d with
    | zero => exact absurd hd (Nat.lt_irrefl 0)
    | succ d =>
        exact productCountingGatedLiteralTruePackedFamily_intermediateEfficient_lt_sizeCap_succ
          roundsOf d
  · intro d hd
    cases d with
    | zero => exact absurd hd (Nat.lt_irrefl 0)
    | succ d =>
        exact productCountingGatedLiteralTruePackedFamily_intermediateEfficient_lt_arity_succ
          roundsOf d
  · intro d hd
    exact productCountingGatedLiteralTruePackedFamily_depth_eq_one_of_pos
      roundsOf d hd

end FormulaRecursiveSyntacticTerminalWidth
end PvNP
