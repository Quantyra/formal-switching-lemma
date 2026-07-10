import PvNP.FormulaRecursiveSyntacticTerminalProduct

/-!
# Structural restricted-family ambient adequacy with class/width envelopes

This module advances Gate B after S2149 by packaging useful class-size and
width envelope data for the S2145 packed-family interface.  A structural
restricted-family package records class membership, depth bounds, a class-size
envelope `S`, and a width envelope `W`.  For the restricted syntactic-terminal
class, the width envelope is derived from the class-size envelope.  Structural
ambient adequacy is stated against the class-size envelope and routes the S2142
final-tree consumers under the unchanged budget `t(d,s)=S(d)*(s-1)`.

This is only a bounded structural envelope packaging for the current packed-
family interface.  It does not synthesize efficient width profiles, improve
thresholds, prove arbitrary normalization, arbitrary AC0/bounded-depth
collapse, full B4, PHP switching, Frege/PHP, NP/circuit lower bounds, P-vs-NP,
or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalStructural

open BoundedDepthFrege
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalExact
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalProduct
open FormulaRecursiveSyntacticTerminalRegime
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-! ## Class-size and width envelopes -/

/-- Class-size envelope: every packed formula size is bounded by `S d`. -/
def SyntacticTerminalPackedFamilyClassSizeEnvelope
    (F : SyntacticTerminalPackedFamily) (S : Nat → Nat) : Prop :=
  ∀ d, syntacticTerminalPackedFamilySizeCap F d ≤ S d

/-- Width envelope: every in-depth S2142 syntactic-terminal frontier width budget
is bounded by `W d`. -/
def SyntacticTerminalPackedFamilyWidthEnvelope
    (F : SyntacticTerminalPackedFamily) (W : Nat → Nat) : Prop :=
  ∀ d level,
    level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      syntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula F d) level ≤ W d

/-- Structural restricted-family data: class, depth, class-size envelope, and
width envelope. -/
def SyntacticTerminalPackedFamilyStructuralData
    (F : SyntacticTerminalPackedFamily) (S W : Nat → Nat) : Prop :=
  SyntacticTerminalPackedFamilyClass F ∧
  SyntacticTerminalPackedFamilyDepthBound F ∧
  SyntacticTerminalPackedFamilyClassSizeEnvelope F S ∧
  SyntacticTerminalPackedFamilyWidthEnvelope F W

/-- Structural ambient adequacy against the class-size envelope: packed arity
meets the S2144 coarse threshold computed from `S d`, not merely from the raw
formula-size cap. -/
def SyntacticTerminalPackedFamilyStructuralAmbientAdequate
    (F : SyntacticTerminalPackedFamily) (S roundsOf : Nat → Nat) : Prop :=
  ∀ d,
    syntacticTerminalClassCoarseEntryThreshold (S d) (roundsOf d) ≤
      syntacticTerminalPackedFamilyArity F d

/-! ## Width envelope from class-size envelope -/

/-- For the restricted syntactic-terminal class, the S2142 width budget is
covered by any class-size envelope. -/
theorem SyntacticTerminalPackedFamilyWidthEnvelope.of_classSizeEnvelope
    {F : SyntacticTerminalPackedFamily} {S : Nat → Nat}
    (_hClass : SyntacticTerminalPackedFamilyClass F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S) :
    SyntacticTerminalPackedFamilyWidthEnvelope F S := by
  intro d level _hk
  have hSizeCap : formulaSize (syntacticTerminalPackedFamilyFormula F d) ≤ S d := by
    simpa [syntacticTerminalPackedFamilySizeCap] using hSize d
  exact syntacticTerminalFrontierWidthBudget_le_classSize
    (syntacticTerminalPackedFamilyFormula F d) S d level hSizeCap

/-- Structural data from class, depth, and a class-size envelope, with width
envelope derived from the class-size envelope. -/
theorem SyntacticTerminalPackedFamilyStructuralData.of_classSizeEnvelope
    {F : SyntacticTerminalPackedFamily} {S : Nat → Nat}
    (hClass : SyntacticTerminalPackedFamilyClass F)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S) :
    SyntacticTerminalPackedFamilyStructuralData F S S :=
  ⟨hClass, hDepth, hSize,
    SyntacticTerminalPackedFamilyWidthEnvelope.of_classSizeEnvelope hClass hSize⟩

/-! ## Threshold monotonicity and ambient recovery -/

/-- The coarse entry threshold is monotone in the size-cap argument. -/
theorem syntacticTerminalClassCoarseEntryThreshold_mono
    {M M' rounds : Nat} (hM : M ≤ M') :
    syntacticTerminalClassCoarseEntryThreshold M rounds ≤
      syntacticTerminalClassCoarseEntryThreshold M' rounds := by
  have h64 : 64 * M ≤ 64 * M' := Nat.mul_le_mul_left 64 hM
  have hpow : (64 * M) ^ rounds ≤ (64 * M') ^ rounds :=
    Nat.pow_le_pow_left h64 rounds
  have htail : 64 * M * M ≤ 64 * M' * M' := Nat.mul_le_mul h64 hM
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) htail

/-- Structural ambient adequacy plus a class-size envelope recovers the S2145
ambient-adequacy predicate on the actual formula-size caps. -/
theorem SyntacticTerminalPackedFamilyAmbientAdequate.of_structural
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S)
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf := by
  intro d
  exact Nat.le_trans
    (syntacticTerminalClassCoarseEntryThreshold_mono (hSize d))
    (hAmb d)

/-- Structural ambient adequacy induces the S2144 parameter regime at envelope
`S`, with `M = S` and `N` the packed arity. -/
theorem SyntacticTerminalClassParameterRegime.of_structural
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    SyntacticTerminalClassParameterRegime
      S S roundsOf (syntacticTerminalPackedFamilyArity F) := by
  intro d
  exact ⟨Nat.le_refl _, hAmb d⟩

/-- Pointwise S2143 entry feasibility from structural ambient adequacy. -/
theorem SyntacticTerminalClassEntryFeasible.of_structural
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat} {d : Nat}
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    FormulaRecursiveSyntacticTerminalEntry.SyntacticTerminalClassEntryFeasible
      S d (roundsOf d) (syntacticTerminalPackedFamilyArity F d) := by
  exact SyntacticTerminalClassEntryFeasible.of_parameterRegime
    (SyntacticTerminalClassParameterRegime.of_structural hAmb)

/-! ## S2142 final-tree routing under structural envelopes -/

/-- S2142 all-level final-tree consumer routed from structural data and
structural ambient adequacy.  The class budget remains `t(d,s)=S(d)*(s-1)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_structural
    {F : SyntacticTerminalPackedFamily} {S W roundsOf : Nat → Nat} {d : Nat}
    (parent : ParentKind)
    (hData : SyntacticTerminalPackedFamilyStructuralData F S W)
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d)
        S d (roundsOf d) parent (hData.1 d) level := by
  have hregime := SyntacticTerminalClassParameterRegime.of_structural hAmb
  have hDepth : depth (syntacticTerminalPackedFamilyFormula F d) ≤ d := hData.2.1 d
  have hSize : formulaSize (syntacticTerminalPackedFamilyFormula F d) ≤ S d := by
    simpa [syntacticTerminalPackedFamilySizeCap] using hData.2.2.1 d
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_parameterRegime
      (syntacticTerminalPackedFamilyFormula F d) parent hregime hDepth hSize (hData.1 d)

/-- Convenience wrapper when the width envelope is the class-size envelope. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_structural_classSize
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat} {d : Nat}
    (parent : ParentKind)
    (hClass : SyntacticTerminalPackedFamilyClass F)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S)
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d)
        S d (roundsOf d) parent (hClass d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_structural
      parent
      (SyntacticTerminalPackedFamilyStructuralData.of_classSizeEnvelope
        hClass hDepth hSize)
      hAmb

/-! ## Concrete structural witness from the S2149 product/counting family -/

/-- Class-size envelope for the multiplicity-2 product/counting family, taking
`S` to be the actual gated size-cap profile. -/
def productCountingGatedLiteralTrueClassSize
    (roundsOf : Nat → Nat) : Nat → Nat :=
  fun d =>
    syntacticTerminalPackedFamilySizeCap
      (productCountingGatedLiteralTruePackedFamily roundsOf) d

/-- The product/counting family satisfies the class-size envelope at its own
size-cap profile. -/
theorem productCountingGatedLiteralTruePackedFamily_classSizeEnvelope
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClassSizeEnvelope
      (productCountingGatedLiteralTruePackedFamily roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf) := by
  intro d
  simp [productCountingGatedLiteralTrueClassSize]

/-- Width envelope for the product/counting family, derived from its class-size
envelope. -/
theorem productCountingGatedLiteralTruePackedFamily_widthEnvelope
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyWidthEnvelope
      (productCountingGatedLiteralTruePackedFamily roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf) :=
  SyntacticTerminalPackedFamilyWidthEnvelope.of_classSizeEnvelope
    (productCountingGatedLiteralTruePackedFamily_class roundsOf)
    (productCountingGatedLiteralTruePackedFamily_classSizeEnvelope roundsOf)

/-- Full structural data for the product/counting family. -/
theorem productCountingGatedLiteralTruePackedFamily_structuralData
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralData
      (productCountingGatedLiteralTruePackedFamily roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf) :=
  SyntacticTerminalPackedFamilyStructuralData.of_classSizeEnvelope
    (productCountingGatedLiteralTruePackedFamily_class roundsOf)
    (productCountingGatedLiteralTruePackedFamily_depthBound roundsOf)
    (productCountingGatedLiteralTruePackedFamily_classSizeEnvelope roundsOf)

/-- Structural ambient adequacy for the product/counting family at its own
class-size envelope, via the S2149 product/counting ambient source. -/
theorem productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralAmbientAdequate
      (productCountingGatedLiteralTruePackedFamily roundsOf)
      (productCountingGatedLiteralTrueClassSize roundsOf) roundsOf := by
  intro d
  have hAmb := productCountingGatedLiteralTruePackedFamily_ambientAdequate roundsOf d
  simpa [productCountingGatedLiteralTrueClassSize,
    SyntacticTerminalPackedFamilyAmbientAdequate,
    syntacticTerminalPackedFamilySizeCap] using hAmb

/-- S2142 final-tree wrapper for the concrete structural product/counting family. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_productCountingStructural
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
      (productCountingGatedLiteralTruePackedFamily_structuralData roundsOf)
      (productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate roundsOf)

/-- Non-vacuity package: structural class/width envelope data plus structural
ambient adequacy for a concrete restricted family. -/
theorem exists_structuralRestrictedFamily_classWidthEnvelope_ambientAdequate
    (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ S W : Nat → Nat,
        SyntacticTerminalPackedFamilyStructuralData F S W ∧
        SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
        SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf ∧
        SyntacticTerminalPackedFamilyWidthEnvelope F W ∧
        (∀ d, W d = S d) := by
  refine ⟨productCountingGatedLiteralTruePackedFamily roundsOf,
    productCountingGatedLiteralTrueClassSize roundsOf,
    productCountingGatedLiteralTrueClassSize roundsOf, ?_, ?_, ?_, ?_, ?_⟩
  · exact productCountingGatedLiteralTruePackedFamily_structuralData roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate roundsOf
  · exact SyntacticTerminalPackedFamilyAmbientAdequate.of_structural
      (productCountingGatedLiteralTruePackedFamily_classSizeEnvelope roundsOf)
      (productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate roundsOf)
  · exact productCountingGatedLiteralTruePackedFamily_widthEnvelope roundsOf
  · intro d; rfl

end FormulaRecursiveSyntacticTerminalStructural
end PvNP
