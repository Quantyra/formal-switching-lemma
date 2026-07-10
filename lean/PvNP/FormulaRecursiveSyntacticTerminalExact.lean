import PvNP.FormulaRecursiveSyntacticTerminalConcrete

/-!
# Exact-threshold syntactic-terminal packed families

This module isolates the packed-family subclass whose ambient arity is exactly
the S2144 coarse threshold for the family's actual formula-size cap.  It also
adds a concrete gated literal/true family: depth index `0` is a single literal,
and every positive depth index is the non-leaf formula `lit0 OR true`.

The results are only bounded consumers of the existing S2145 packed-family
interface.  They do not prove product/counting synthesis, threshold improvement,
arbitrary normalization, arbitrary AC0/bounded-depth collapse, PHP switching,
Frege/PHP, NP/circuit lower bounds, P-vs-NP, or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalExact

open BoundedDepthFrege
open CNFModel
open FormulaRecursiveNonempty
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalRegime
open FormulaSyntacticSimpleBridge
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-! ## Exact-threshold packed-family subclass -/

/-- A packed family whose ambient arity is exactly the S2144 coarse threshold for
its actual formula-size cap at every depth index. -/
def SyntacticTerminalPackedFamilyExactThreshold
    (F : SyntacticTerminalPackedFamily) (roundsOf : Nat -> Nat) : Prop :=
  ∀ d, syntacticTerminalPackedFamilyArity F d =
    syntacticTerminalClassCoarseEntryThreshold
      (syntacticTerminalPackedFamilySizeCap F d) (roundsOf d)

/-- Exact-threshold packed families satisfy the S2145 ambient-adequacy premise. -/
theorem SyntacticTerminalPackedFamilyAmbientAdequate.of_exactThreshold
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat}
    (hExact : SyntacticTerminalPackedFamilyExactThreshold F roundsOf) :
    SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf := by
  intro d
  rw [hExact d]

/-- An exact-threshold packed family induces the S2144 parameter regime. -/
theorem SyntacticTerminalClassParameterRegime.of_exactThresholdPackedFamily
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat}
    (hExact : SyntacticTerminalPackedFamilyExactThreshold F roundsOf) :
    SyntacticTerminalClassParameterRegime
      (syntacticTerminalPackedFamilySizeCap F)
      (syntacticTerminalPackedFamilySizeCap F)
      roundsOf
      (syntacticTerminalPackedFamilyArity F) := by
  exact SyntacticTerminalClassParameterRegime.of_packedFamily
    (SyntacticTerminalPackedFamilyAmbientAdequate.of_exactThreshold hExact)

/-- Pointwise S2143 entry feasibility from an exact-threshold packed family. -/
theorem SyntacticTerminalClassEntryFeasible.of_exactThresholdPackedFamily
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat} {d : Nat}
    (hExact : SyntacticTerminalPackedFamilyExactThreshold F roundsOf) :
    FormulaRecursiveSyntacticTerminalEntry.SyntacticTerminalClassEntryFeasible
      (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d)
      (syntacticTerminalPackedFamilyArity F d) := by
  exact SyntacticTerminalClassEntryFeasible.of_packedFamily
    (SyntacticTerminalPackedFamilyAmbientAdequate.of_exactThreshold hExact)

/-- Final-tree wrapper consuming exact-threshold, depth-bound, and class
predicates through the S2145 packed-family predicate wrapper. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_exactThresholdPackedFamily
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat} {d : Nat}
    (parent : ParentKind)
    (hExact : SyntacticTerminalPackedFamilyExactThreshold F roundsOf)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hClass : SyntacticTerminalPackedFamilyClass F) :
    ∀ level, level <= depth (syntacticTerminalPackedFamilyFormula F d) ->
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d)
        (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d) parent
        (hClass d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_packedFamily_predicates
      parent
      (SyntacticTerminalPackedFamilyAmbientAdequate.of_exactThreshold hExact)
      hDepth hClass

/-! ## Concrete gated literal/true exact-threshold family -/

/-- The intended size cap of the gated literal/true family at each depth index. -/
def gatedLiteralTrueThresholdSizeCapIndex : Nat -> Nat
  | 0 => 1
  | _ + 1 => 3

/-- The exact S2144 coarse threshold arity for the gated literal/true family. -/
def gatedLiteralTrueThresholdArity (roundsOf : Nat -> Nat) (d : Nat) : Nat :=
  syntacticTerminalClassCoarseEntryThreshold
    (gatedLiteralTrueThresholdSizeCapIndex d) (roundsOf d)

/-- A positive coarse threshold whenever the size cap is positive. -/
theorem syntacticTerminalClassCoarseEntryThreshold_pos_of_pos
    {M rounds : Nat} (hM : 0 < M) :
    0 < syntacticTerminalClassCoarseEntryThreshold M rounds := by
  unfold syntacticTerminalClassCoarseEntryThreshold
  have h64M : 0 < 64 * M := Nat.mul_pos (by decide) hM
  exact Nat.mul_pos
    (Nat.mul_pos (by decide) (Nat.pow_pos h64M : 0 < (64 * M) ^ rounds))
    (Nat.mul_pos h64M hM)

/-- The gated literal/true family always has a positive ambient arity. -/
theorem gatedLiteralTrueThresholdArity_pos (roundsOf : Nat -> Nat) (d : Nat) :
    0 < gatedLiteralTrueThresholdArity roundsOf d := by
  cases d <;>
    simp [gatedLiteralTrueThresholdArity, gatedLiteralTrueThresholdSizeCapIndex,
      syntacticTerminalClassCoarseEntryThreshold_pos_of_pos]

/-- Variable `0` as a positive literal over the gated threshold arity. -/
def gatedLiteralTrueThresholdLit0 (roundsOf : Nat -> Nat) (d : Nat) :
    BDFormula (gatedLiteralTrueThresholdArity roundsOf d) :=
  BDFormula.lit
    { var := ⟨0, gatedLiteralTrueThresholdArity_pos roundsOf d⟩
      sign := true }

/-- The concrete exact-threshold formula: one literal at `0`, and the non-leaf
`lit0 OR true` at every positive depth index. -/
def gatedLiteralTrueThresholdFormula (roundsOf : Nat -> Nat) :
    (d : Nat) -> BDFormula (gatedLiteralTrueThresholdArity roundsOf d)
  | 0 => gatedLiteralTrueThresholdLit0 roundsOf 0
  | d + 1 => BDFormula.or
      [gatedLiteralTrueThresholdLit0 roundsOf (d + 1), BDFormula.tru]

/-- The concrete gated literal/true exact-threshold packed family. -/
def gatedLiteralTrueThresholdPackedFamily
    (roundsOf : Nat -> Nat) : SyntacticTerminalPackedFamily :=
  fun d => ⟨gatedLiteralTrueThresholdArity roundsOf d,
    gatedLiteralTrueThresholdFormula roundsOf d⟩

/-- The concrete gated family has size cap `1` at depth index `0` and `3` at
successor depth indices. -/
theorem gatedLiteralTrueThresholdSizeCap
    (roundsOf : Nat -> Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap
      (gatedLiteralTrueThresholdPackedFamily roundsOf) d =
        gatedLiteralTrueThresholdSizeCapIndex d := by
  cases d <;>
    simp [syntacticTerminalPackedFamilySizeCap,
      syntacticTerminalPackedFamilyFormula, gatedLiteralTrueThresholdPackedFamily,
      gatedLiteralTrueThresholdFormula, gatedLiteralTrueThresholdLit0,
      gatedLiteralTrueThresholdSizeCapIndex, formulaSize_lit, formulaSize_or,
      formulaSize]

/-- The gated family has exact size cap `1` at depth index `0`. -/
theorem gatedLiteralTrueThresholdSizeCap_zero
    (roundsOf : Nat -> Nat) :
    syntacticTerminalPackedFamilySizeCap
      (gatedLiteralTrueThresholdPackedFamily roundsOf) 0 = 1 := by
  simpa [gatedLiteralTrueThresholdSizeCapIndex] using
    gatedLiteralTrueThresholdSizeCap roundsOf 0

/-- The gated family has exact size cap `3` at positive depth indices. -/
theorem gatedLiteralTrueThresholdSizeCap_succ
    (roundsOf : Nat -> Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap
      (gatedLiteralTrueThresholdPackedFamily roundsOf) (d + 1) = 3 := by
  simpa [gatedLiteralTrueThresholdSizeCapIndex] using
    gatedLiteralTrueThresholdSizeCap roundsOf (d + 1)

/-- The gated family has depth `0` at depth index `0` and `1` at successors. -/
theorem gatedLiteralTrueThresholdDepth
    (roundsOf : Nat -> Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (gatedLiteralTrueThresholdPackedFamily roundsOf) d) =
        if d = 0 then 0 else 1 := by
  cases d <;>
    simp [syntacticTerminalPackedFamilyFormula, gatedLiteralTrueThresholdPackedFamily,
      gatedLiteralTrueThresholdFormula, gatedLiteralTrueThresholdLit0, depth]

/-- The gated family has depth `0` at depth index `0`. -/
theorem gatedLiteralTrueThresholdDepth_zero
    (roundsOf : Nat -> Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (gatedLiteralTrueThresholdPackedFamily roundsOf) 0) = 0 := by
  simpa using gatedLiteralTrueThresholdDepth roundsOf 0

/-- The gated family has depth `1` at positive depth indices. -/
theorem gatedLiteralTrueThresholdDepth_succ
    (roundsOf : Nat -> Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (gatedLiteralTrueThresholdPackedFamily roundsOf) (d + 1)) = 1 := by
  simpa using gatedLiteralTrueThresholdDepth roundsOf (d + 1)

/-- The gated family lies in the restricted syntactic-terminal class. -/
theorem gatedLiteralTrueThresholdPackedFamily_class
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyClass
      (gatedLiteralTrueThresholdPackedFamily roundsOf) := by
  intro d
  cases d with
  | zero =>
      constructor
      · simp [syntacticTerminalPackedFamilyFormula,
          gatedLiteralTrueThresholdPackedFamily,
          gatedLiteralTrueThresholdFormula, gatedLiteralTrueThresholdLit0,
          syntacticFormulaSimpleDNF, syntacticOrListSimpleDNF]
      · exact NoEmptyFanins.lit _
  | succ d =>
      constructor
      · simp [syntacticTerminalPackedFamilyFormula,
          gatedLiteralTrueThresholdPackedFamily,
          gatedLiteralTrueThresholdFormula, gatedLiteralTrueThresholdLit0,
          syntacticFormulaSimpleDNF, syntacticOrListSimpleDNF]
      · refine NoEmptyFanins.or (by simp) ?_
        intro child hchild
        simp at hchild
        rcases hchild with hchild | hchild
        · subst child
          exact NoEmptyFanins.lit _
        · subst child
          exact NoEmptyFanins.tru

/-- The gated family satisfies the depth bound at every index. -/
theorem gatedLiteralTrueThresholdPackedFamily_depthBound
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyDepthBound
      (gatedLiteralTrueThresholdPackedFamily roundsOf) := by
  intro d
  cases d with
  | zero => simp [gatedLiteralTrueThresholdDepth_zero]
  | succ d =>
      simp [gatedLiteralTrueThresholdDepth_succ]

/-- The gated family satisfies the exact-threshold subclass predicate. -/
theorem gatedLiteralTrueThresholdPackedFamily_exactThreshold
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyExactThreshold
      (gatedLiteralTrueThresholdPackedFamily roundsOf) roundsOf := by
  intro d
  simp [SyntacticTerminalPackedFamilyExactThreshold,
    syntacticTerminalPackedFamilyArity, gatedLiteralTrueThresholdPackedFamily,
    gatedLiteralTrueThresholdArity, gatedLiteralTrueThresholdSizeCap]

/-- Ambient adequacy for the gated family follows from exact-threshold status. -/
theorem gatedLiteralTrueThresholdPackedFamily_ambientAdequate
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyAmbientAdequate
      (gatedLiteralTrueThresholdPackedFamily roundsOf) roundsOf := by
  exact SyntacticTerminalPackedFamilyAmbientAdequate.of_exactThreshold
    (gatedLiteralTrueThresholdPackedFamily_exactThreshold roundsOf)

/-- The gated exact-threshold family induces the S2144 parameter regime. -/
theorem SyntacticTerminalClassParameterRegime.of_gatedLiteralTrueThresholdPackedFamily
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalClassParameterRegime
      (syntacticTerminalPackedFamilySizeCap
        (gatedLiteralTrueThresholdPackedFamily roundsOf))
      (syntacticTerminalPackedFamilySizeCap
        (gatedLiteralTrueThresholdPackedFamily roundsOf))
      roundsOf
      (syntacticTerminalPackedFamilyArity
        (gatedLiteralTrueThresholdPackedFamily roundsOf)) := by
  exact SyntacticTerminalClassParameterRegime.of_exactThresholdPackedFamily
    (gatedLiteralTrueThresholdPackedFamily_exactThreshold roundsOf)

/-- Pointwise S2143 entry feasibility for the gated exact-threshold family. -/
theorem SyntacticTerminalClassEntryFeasible.of_gatedLiteralTrueThresholdPackedFamily
    (roundsOf : Nat -> Nat) (d : Nat) :
    FormulaRecursiveSyntacticTerminalEntry.SyntacticTerminalClassEntryFeasible
      (syntacticTerminalPackedFamilySizeCap
        (gatedLiteralTrueThresholdPackedFamily roundsOf)) d (roundsOf d)
      (syntacticTerminalPackedFamilyArity
        (gatedLiteralTrueThresholdPackedFamily roundsOf) d) := by
  exact SyntacticTerminalClassEntryFeasible.of_exactThresholdPackedFamily
    (gatedLiteralTrueThresholdPackedFamily_exactThreshold roundsOf)

/-- Final-tree wrapper for the gated exact-threshold family. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_gatedLiteralTrueThresholdPackedFamily
    (roundsOf : Nat -> Nat) {d : Nat} (parent : ParentKind) :
    ∀ level, level <= depth (syntacticTerminalPackedFamilyFormula
        (gatedLiteralTrueThresholdPackedFamily roundsOf) d) ->
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula
          (gatedLiteralTrueThresholdPackedFamily roundsOf) d)
        (syntacticTerminalPackedFamilySizeCap
          (gatedLiteralTrueThresholdPackedFamily roundsOf)) d (roundsOf d) parent
        (gatedLiteralTrueThresholdPackedFamily_class roundsOf d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_exactThresholdPackedFamily
      parent (gatedLiteralTrueThresholdPackedFamily_exactThreshold roundsOf)
      (gatedLiteralTrueThresholdPackedFamily_depthBound roundsOf)
      (gatedLiteralTrueThresholdPackedFamily_class roundsOf)

end FormulaRecursiveSyntacticTerminalExact
end PvNP
