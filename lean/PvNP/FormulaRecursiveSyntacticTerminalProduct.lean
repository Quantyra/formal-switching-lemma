import PvNP.FormulaRecursiveSyntacticTerminalExact

/-!
# Product/counting ambient arity source for packed syntactic-terminal families

This module advances Gate B after S2148 by naming the S2144 coarse entry
threshold as an explicit product of counting factors and using a positive
counting multiplicity as an ambient-arity source.  Ambient adequacy is obtained
from the product/counting inequality without requiring exact-threshold arity
equality.  A concrete gated literal/true family with multiplicity `2` witnesses
that the source can meet the ambient threshold strictly above exact equality.

This is only a bounded product/counting arity source for the current packed-
family interface.  It does not improve the threshold, synthesize efficient
width profiles, prove arbitrary normalization, arbitrary AC0/bounded-depth
collapse, full B4, PHP switching, Frege/PHP, NP/circuit lower bounds, P-vs-NP,
or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalProduct

open BoundedDepthFrege
open CNFModel
open FormulaRecursiveNonempty
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalExact
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalRegime
open FormulaSyntacticSimpleBridge
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-! ## Named product factors for the S2144 coarse entry threshold -/

/-- Front counting factor of the coarse entry threshold. -/
def syntacticTerminalCoarseEntryFront : Nat := 2

/-- Round-base counting factor of the coarse entry threshold. -/
def syntacticTerminalCoarseEntryBase (M : Nat) : Nat := 64 * M

/-- Tail counting factor of the coarse entry threshold. -/
def syntacticTerminalCoarseEntryTail (M : Nat) : Nat := 64 * M * M

/-- Explicit product reconstruction of the S2144 coarse entry threshold. -/
def syntacticTerminalCoarseEntryProduct (M rounds : Nat) : Nat :=
  syntacticTerminalCoarseEntryFront *
    (syntacticTerminalCoarseEntryBase M) ^ rounds *
    syntacticTerminalCoarseEntryTail M

/-- The named product equals the existing coarse entry threshold definition. -/
theorem syntacticTerminalCoarseEntryProduct_eq_threshold (M rounds : Nat) :
    syntacticTerminalCoarseEntryProduct M rounds =
      syntacticTerminalClassCoarseEntryThreshold M rounds := by
  rfl

/-! ## Product/counting ambient source -/

/-- Product/counting ambient source: the packed arity is at least the product
reconstruction of the coarse threshold times a positive counting multiplicity. -/
def SyntacticTerminalPackedFamilyProductCountingSource
    (F : SyntacticTerminalPackedFamily) (roundsOf : Nat -> Nat)
    (countOf : Nat -> Nat) : Prop :=
  ∀ d,
    0 < countOf d ∧
      syntacticTerminalCoarseEntryProduct
          (syntacticTerminalPackedFamilySizeCap F d) (roundsOf d) * countOf d ≤
        syntacticTerminalPackedFamilyArity F d

/-- A positive count multiplies the product threshold into a lower bound. -/
theorem syntacticTerminalCoarseEntryProduct_le_mul_count
    {M rounds count : Nat} (hcount : 0 < count) :
    syntacticTerminalCoarseEntryProduct M rounds ≤
      syntacticTerminalCoarseEntryProduct M rounds * count :=
  Nat.le_mul_of_pos_right _ hcount

/-- Product/counting source implies S2145 ambient adequacy without exact equality. -/
theorem SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource
    {F : SyntacticTerminalPackedFamily} {roundsOf countOf : Nat -> Nat}
    (hSource : SyntacticTerminalPackedFamilyProductCountingSource F roundsOf countOf) :
    SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf := by
  intro d
  have hd := hSource d
  have hprod :
      syntacticTerminalClassCoarseEntryThreshold
          (syntacticTerminalPackedFamilySizeCap F d) (roundsOf d) ≤
        syntacticTerminalCoarseEntryProduct
          (syntacticTerminalPackedFamilySizeCap F d) (roundsOf d) * countOf d := by
    simpa [syntacticTerminalCoarseEntryProduct_eq_threshold] using
      syntacticTerminalCoarseEntryProduct_le_mul_count hd.1
  exact Nat.le_trans hprod hd.2

/-- Parameter regime from a product/counting source. -/
theorem SyntacticTerminalClassParameterRegime.of_productCountingSource
    {F : SyntacticTerminalPackedFamily} {roundsOf countOf : Nat -> Nat}
    (hSource : SyntacticTerminalPackedFamilyProductCountingSource F roundsOf countOf) :
    SyntacticTerminalClassParameterRegime
      (syntacticTerminalPackedFamilySizeCap F)
      (syntacticTerminalPackedFamilySizeCap F)
      roundsOf
      (syntacticTerminalPackedFamilyArity F) := by
  exact SyntacticTerminalClassParameterRegime.of_packedFamily
    (SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource hSource)

/-- Pointwise entry feasibility from a product/counting source. -/
theorem SyntacticTerminalClassEntryFeasible.of_productCountingSource
    {F : SyntacticTerminalPackedFamily} {roundsOf countOf : Nat -> Nat} {d : Nat}
    (hSource : SyntacticTerminalPackedFamilyProductCountingSource F roundsOf countOf) :
    FormulaRecursiveSyntacticTerminalEntry.SyntacticTerminalClassEntryFeasible
      (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d)
      (syntacticTerminalPackedFamilyArity F d) := by
  exact SyntacticTerminalClassEntryFeasible.of_packedFamily
    (SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource hSource)

/-- Final-tree wrapper from a product/counting source plus class/depth predicates. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_productCountingSource
    {F : SyntacticTerminalPackedFamily} {roundsOf countOf : Nat -> Nat} {d : Nat}
    (parent : ParentKind)
    (hSource : SyntacticTerminalPackedFamilyProductCountingSource F roundsOf countOf)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hClass : SyntacticTerminalPackedFamilyClass F) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d)
        (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d) parent
        (hClass d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_packedFamily_predicates
      parent
      (SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource hSource)
      hDepth hClass

/-! ## Concrete multiplicity-2 product/counting family -/

/-- Product/counting ambient arity for the gated size-cap profile with multiplicity `2`. -/
def productCountingGatedLiteralTrueArity (roundsOf : Nat → Nat) (d : Nat) : Nat :=
  syntacticTerminalCoarseEntryProduct
    (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d) * 2

/-- The multiplicity-2 product/counting arity is positive. -/
theorem productCountingGatedLiteralTrueArity_pos
    (roundsOf : Nat → Nat) (d : Nat) :
    0 < productCountingGatedLiteralTrueArity roundsOf d := by
  have hM : 0 < gatedLiteralTrueThresholdSizeCapIndex d := by
    cases d <;> simp [gatedLiteralTrueThresholdSizeCapIndex]
  have hprod :
      0 < syntacticTerminalCoarseEntryProduct
        (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d) := by
    simpa [syntacticTerminalCoarseEntryProduct_eq_threshold] using
      syntacticTerminalClassCoarseEntryThreshold_pos_of_pos hM
  exact Nat.mul_pos hprod (by decide : 0 < 2)

/-- Variable `0` as a positive literal over the product/counting arity. -/
def productCountingGatedLiteralTrueLit0 (roundsOf : Nat → Nat) (d : Nat) :
    BDFormula (productCountingGatedLiteralTrueArity roundsOf d) :=
  BDFormula.lit
    { var := ⟨0, productCountingGatedLiteralTrueArity_pos roundsOf d⟩
      sign := true }

/-- The concrete product/counting formula: one literal at `0`, and `lit0 OR true`
at every positive depth index. -/
def productCountingGatedLiteralTrueFormula (roundsOf : Nat → Nat) :
    (d : Nat) → BDFormula (productCountingGatedLiteralTrueArity roundsOf d)
  | 0 => productCountingGatedLiteralTrueLit0 roundsOf 0
  | d + 1 => BDFormula.or
      [productCountingGatedLiteralTrueLit0 roundsOf (d + 1), BDFormula.tru]

/-- The concrete multiplicity-2 product/counting packed family. -/
def productCountingGatedLiteralTruePackedFamily
    (roundsOf : Nat → Nat) : SyntacticTerminalPackedFamily :=
  fun d => ⟨productCountingGatedLiteralTrueArity roundsOf d,
    productCountingGatedLiteralTrueFormula roundsOf d⟩

/-- Size cap profile matches the gated exact-threshold family. -/
theorem productCountingGatedLiteralTrueSizeCap
    (roundsOf : Nat → Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap
      (productCountingGatedLiteralTruePackedFamily roundsOf) d =
        gatedLiteralTrueThresholdSizeCapIndex d := by
  cases d <;>
    simp [syntacticTerminalPackedFamilySizeCap,
      syntacticTerminalPackedFamilyFormula, productCountingGatedLiteralTruePackedFamily,
      productCountingGatedLiteralTrueFormula, productCountingGatedLiteralTrueLit0,
      gatedLiteralTrueThresholdSizeCapIndex, formulaSize_lit, formulaSize_or,
      formulaSize]

/-- Depth profile: `0` at index `0`, `1` at successors. -/
theorem productCountingGatedLiteralTrueDepth
    (roundsOf : Nat → Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (productCountingGatedLiteralTruePackedFamily roundsOf) d) =
        if d = 0 then 0 else 1 := by
  cases d <;>
    simp [syntacticTerminalPackedFamilyFormula, productCountingGatedLiteralTruePackedFamily,
      productCountingGatedLiteralTrueFormula, productCountingGatedLiteralTrueLit0, depth]

/-- Restricted syntactic-terminal class membership. -/
theorem productCountingGatedLiteralTruePackedFamily_class
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClass
      (productCountingGatedLiteralTruePackedFamily roundsOf) := by
  intro d
  cases d with
  | zero =>
      constructor
      · simp [syntacticTerminalPackedFamilyFormula,
          productCountingGatedLiteralTruePackedFamily,
          productCountingGatedLiteralTrueFormula, productCountingGatedLiteralTrueLit0,
          syntacticFormulaSimpleDNF, syntacticOrListSimpleDNF]
      · exact NoEmptyFanins.lit _
  | succ d =>
      constructor
      · simp [syntacticTerminalPackedFamilyFormula,
          productCountingGatedLiteralTruePackedFamily,
          productCountingGatedLiteralTrueFormula, productCountingGatedLiteralTrueLit0,
          syntacticFormulaSimpleDNF, syntacticOrListSimpleDNF]
      · refine NoEmptyFanins.or (by simp) ?_
        intro child hchild
        simp at hchild
        rcases hchild with hchild | hchild
        · subst child
          exact NoEmptyFanins.lit _
        · subst child
          exact NoEmptyFanins.tru

/-- Depth-bound predicate. -/
theorem productCountingGatedLiteralTruePackedFamily_depthBound
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyDepthBound
      (productCountingGatedLiteralTruePackedFamily roundsOf) := by
  intro d
  cases d with
  | zero =>
      have h := productCountingGatedLiteralTrueDepth roundsOf 0
      simp at h
      simp [h]
  | succ d =>
      have h := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
      simp at h
      exact Nat.le_trans (le_of_eq h) (Nat.succ_le_succ (Nat.zero_le _))

/-- Constant multiplicity `2` counting schedule. -/
def productCountingMultiplicityTwo : Nat → Nat := fun _ => 2

/-- The concrete family is a product/counting ambient source with multiplicity `2`. -/
theorem productCountingGatedLiteralTruePackedFamily_productCountingSource
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyProductCountingSource
      (productCountingGatedLiteralTruePackedFamily roundsOf) roundsOf
      productCountingMultiplicityTwo := by
  intro d
  refine ⟨Nat.zero_lt_two, ?_⟩
  simp [productCountingMultiplicityTwo, syntacticTerminalPackedFamilyArity,
    productCountingGatedLiteralTruePackedFamily, productCountingGatedLiteralTrueArity,
    productCountingGatedLiteralTrueSizeCap]

/-- Ambient adequacy via the product/counting source, not exact-threshold equality. -/
theorem productCountingGatedLiteralTruePackedFamily_ambientAdequate
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyAmbientAdequate
      (productCountingGatedLiteralTruePackedFamily roundsOf) roundsOf := by
  exact SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource
    (productCountingGatedLiteralTruePackedFamily_productCountingSource roundsOf)

/-- The concrete multiplicity-2 arity is strictly above the exact coarse threshold. -/
theorem productCountingGatedLiteralTrueArity_gt_threshold
    (roundsOf : Nat → Nat) (d : Nat) :
    syntacticTerminalClassCoarseEntryThreshold
        (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d) <
      productCountingGatedLiteralTrueArity roundsOf d := by
  have hM : 0 < gatedLiteralTrueThresholdSizeCapIndex d := by
    cases d <;> simp [gatedLiteralTrueThresholdSizeCapIndex]
  have hpos :
      0 < syntacticTerminalClassCoarseEntryThreshold
        (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d) :=
    syntacticTerminalClassCoarseEntryThreshold_pos_of_pos hM
  have hmul :
      syntacticTerminalClassCoarseEntryThreshold
          (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d) *
        2 =
        productCountingGatedLiteralTrueArity roundsOf d := by
    simp [productCountingGatedLiteralTrueArity,
      syntacticTerminalCoarseEntryProduct_eq_threshold]
  set T :=
    syntacticTerminalClassCoarseEntryThreshold
      (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d)
  have hlt : T < T * 2 :=
    calc
      T = T * 1 := (Nat.mul_one T).symm
      _ < T * 2 := Nat.mul_lt_mul_of_pos_left (by decide : 1 < 2) hpos
  simpa [hmul, T] using hlt

/-- The concrete family is not an exact-threshold packed family. -/
theorem productCountingGatedLiteralTruePackedFamily_not_exactThreshold
    (roundsOf : Nat → Nat) :
    ¬ SyntacticTerminalPackedFamilyExactThreshold
        (productCountingGatedLiteralTruePackedFamily roundsOf) roundsOf := by
  intro hExact
  have h0 := hExact 0
  have hgt := productCountingGatedLiteralTrueArity_gt_threshold roundsOf 0
  have harity :
      syntacticTerminalPackedFamilyArity
          (productCountingGatedLiteralTruePackedFamily roundsOf) 0 =
        productCountingGatedLiteralTrueArity roundsOf 0 := by
    simp [syntacticTerminalPackedFamilyArity, productCountingGatedLiteralTruePackedFamily]
  have hsize :
      syntacticTerminalPackedFamilySizeCap
          (productCountingGatedLiteralTruePackedFamily roundsOf) 0 =
        gatedLiteralTrueThresholdSizeCapIndex 0 :=
    productCountingGatedLiteralTrueSizeCap roundsOf 0
  have hneq :
      productCountingGatedLiteralTrueArity roundsOf 0 ≠
        syntacticTerminalClassCoarseEntryThreshold
          (gatedLiteralTrueThresholdSizeCapIndex 0) (roundsOf 0) :=
    ne_of_gt hgt
  apply hneq
  calc
    productCountingGatedLiteralTrueArity roundsOf 0
        = syntacticTerminalPackedFamilyArity
            (productCountingGatedLiteralTruePackedFamily roundsOf) 0 := by
          simpa using harity.symm
    _ = syntacticTerminalClassCoarseEntryThreshold
          (syntacticTerminalPackedFamilySizeCap
            (productCountingGatedLiteralTruePackedFamily roundsOf) 0)
          (roundsOf 0) := h0
    _ = syntacticTerminalClassCoarseEntryThreshold
          (gatedLiteralTrueThresholdSizeCapIndex 0) (roundsOf 0) := by
          simp [hsize]

/-- Parameter regime for the concrete product/counting family. -/
theorem SyntacticTerminalClassParameterRegime.of_productCountingGatedLiteralTruePackedFamily
    (roundsOf : Nat → Nat) :
    SyntacticTerminalClassParameterRegime
      (syntacticTerminalPackedFamilySizeCap
        (productCountingGatedLiteralTruePackedFamily roundsOf))
      (syntacticTerminalPackedFamilySizeCap
        (productCountingGatedLiteralTruePackedFamily roundsOf))
      roundsOf
      (syntacticTerminalPackedFamilyArity
        (productCountingGatedLiteralTruePackedFamily roundsOf)) := by
  exact SyntacticTerminalClassParameterRegime.of_productCountingSource
    (productCountingGatedLiteralTruePackedFamily_productCountingSource roundsOf)

/-- Pointwise entry feasibility for the concrete product/counting family. -/
theorem SyntacticTerminalClassEntryFeasible.of_productCountingGatedLiteralTruePackedFamily
    (roundsOf : Nat → Nat) (d : Nat) :
    FormulaRecursiveSyntacticTerminalEntry.SyntacticTerminalClassEntryFeasible
      (syntacticTerminalPackedFamilySizeCap
        (productCountingGatedLiteralTruePackedFamily roundsOf)) d (roundsOf d)
      (syntacticTerminalPackedFamilyArity
        (productCountingGatedLiteralTruePackedFamily roundsOf) d) := by
  exact SyntacticTerminalClassEntryFeasible.of_productCountingSource
    (productCountingGatedLiteralTruePackedFamily_productCountingSource roundsOf)

/-- Final-tree wrapper for the concrete product/counting family. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_productCountingGatedLiteralTruePackedFamily
    (roundsOf : Nat → Nat) {d : Nat} (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) d) →
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula
          (productCountingGatedLiteralTruePackedFamily roundsOf) d)
        (syntacticTerminalPackedFamilySizeCap
          (productCountingGatedLiteralTruePackedFamily roundsOf)) d (roundsOf d) parent
        (productCountingGatedLiteralTruePackedFamily_class roundsOf d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_productCountingSource
      parent
      (productCountingGatedLiteralTruePackedFamily_productCountingSource roundsOf)
      (productCountingGatedLiteralTruePackedFamily_depthBound roundsOf)
      (productCountingGatedLiteralTruePackedFamily_class roundsOf)

/-- Non-vacuity package: product/counting source meets ambient adequacy without
exact-threshold equality. -/
theorem exists_productCountingSource_ambientAdequate_not_exactThreshold
    (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ countOf : Nat → Nat,
        SyntacticTerminalPackedFamilyClass F ∧
        SyntacticTerminalPackedFamilyDepthBound F ∧
        SyntacticTerminalPackedFamilyProductCountingSource F roundsOf countOf ∧
        SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf ∧
        ¬ SyntacticTerminalPackedFamilyExactThreshold F roundsOf := by
  refine ⟨productCountingGatedLiteralTruePackedFamily roundsOf,
    productCountingMultiplicityTwo, ?_, ?_, ?_, ?_, ?_⟩
  · exact productCountingGatedLiteralTruePackedFamily_class roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_depthBound roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_productCountingSource roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_ambientAdequate roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_not_exactThreshold roundsOf

end FormulaRecursiveSyntacticTerminalProduct
end PvNP
