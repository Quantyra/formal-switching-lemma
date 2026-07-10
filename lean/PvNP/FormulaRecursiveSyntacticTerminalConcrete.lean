import PvNP.FormulaRecursiveSyntacticTerminalFamily

/-!
# Concrete one-literal syntactic-terminal packed family

This module instantiates the S2145 packed-family interface with a single positive
literal over an ambient arity chosen to be exactly the S2144 coarse threshold for
size cap `1`.  It is only a concrete adequacy witness for that bounded interface:
it does not prove product/counting synthesis, threshold improvement, arbitrary
normalization, arbitrary AC0/bounded-depth collapse, PHP switching, Frege/PHP,
NP/circuit lower bounds, P-vs-NP, or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalConcrete

open BoundedDepthFrege
open CNFModel
open FormulaRecursiveNonempty
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalRegime
open FormulaSyntacticSimpleBridge
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-! ## Exact-threshold one-literal family -/

/-- The exact S2144 coarse threshold arity for a one-literal size cap. -/
def oneLiteralThresholdArity (roundsOf : Nat -> Nat) (d : Nat) : Nat :=
  syntacticTerminalClassCoarseEntryThreshold 1 (roundsOf d)

/-- The exact-threshold arity is positive, so variable `0` is available. -/
theorem oneLiteralThresholdArity_pos (roundsOf : Nat -> Nat) (d : Nat) :
    0 < oneLiteralThresholdArity roundsOf d := by
  unfold oneLiteralThresholdArity syntacticTerminalClassCoarseEntryThreshold
  exact Nat.mul_pos
    (Nat.mul_pos (by decide) (Nat.pow_pos (by decide : 0 < 64 * 1)))
    (by decide)

/-- The positive literal on variable `0` at the exact-threshold ambient arity. -/
def oneLiteralThresholdFormula (roundsOf : Nat -> Nat) (d : Nat) :
    BDFormula (oneLiteralThresholdArity roundsOf d) :=
  BDFormula.lit
    { var := ⟨0, oneLiteralThresholdArity_pos roundsOf d⟩
      sign := true }

/-- The concrete packed family carrying the one-literal formula at each depth. -/
def oneLiteralThresholdPackedFamily
    (roundsOf : Nat -> Nat) : SyntacticTerminalPackedFamily :=
  fun d => ⟨oneLiteralThresholdArity roundsOf d,
    oneLiteralThresholdFormula roundsOf d⟩

/-- The concrete one-literal family has exact formula-size cap `1`. -/
theorem oneLiteralThresholdPackedFamily_sizeCap
    (roundsOf : Nat -> Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap
      (oneLiteralThresholdPackedFamily roundsOf) d = 1 := by
  simp [syntacticTerminalPackedFamilySizeCap,
    syntacticTerminalPackedFamilyFormula, oneLiteralThresholdPackedFamily,
    oneLiteralThresholdFormula, formulaSize_lit]

/-- The concrete one-literal family has depth `0`. -/
theorem oneLiteralThresholdPackedFamily_depth
    (roundsOf : Nat -> Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (oneLiteralThresholdPackedFamily roundsOf) d) = 0 := by
  simp [syntacticTerminalPackedFamilyFormula, oneLiteralThresholdPackedFamily,
    oneLiteralThresholdFormula, depth]

/-- The concrete one-literal family lies in the restricted syntactic-terminal class. -/
theorem oneLiteralThresholdPackedFamily_class
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyClass
      (oneLiteralThresholdPackedFamily roundsOf) := by
  intro d
  constructor
  · simp [syntacticTerminalPackedFamilyFormula, oneLiteralThresholdPackedFamily,
      oneLiteralThresholdFormula, syntacticFormulaSimpleDNF]
  · exact NoEmptyFanins.lit _

/-- The concrete one-literal family satisfies the depth bound at every index. -/
theorem oneLiteralThresholdPackedFamily_depthBound
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyDepthBound
      (oneLiteralThresholdPackedFamily roundsOf) := by
  intro d
  simp [oneLiteralThresholdPackedFamily_depth]

/-- The concrete one-literal family meets ambient adequacy exactly at threshold. -/
theorem oneLiteralThresholdPackedFamily_ambientAdequate
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalPackedFamilyAmbientAdequate
      (oneLiteralThresholdPackedFamily roundsOf) roundsOf := by
  intro d
  simp [SyntacticTerminalPackedFamilyAmbientAdequate,
    syntacticTerminalPackedFamilyArity, oneLiteralThresholdPackedFamily,
    oneLiteralThresholdArity, oneLiteralThresholdPackedFamily_sizeCap]

/-! ## Consumer wrappers -/

/-- The one-literal exact-threshold family induces the S2144 parameter regime. -/
theorem SyntacticTerminalClassParameterRegime.of_oneLiteralThresholdPackedFamily
    (roundsOf : Nat -> Nat) :
    SyntacticTerminalClassParameterRegime
      (syntacticTerminalPackedFamilySizeCap
        (oneLiteralThresholdPackedFamily roundsOf))
      (syntacticTerminalPackedFamilySizeCap
        (oneLiteralThresholdPackedFamily roundsOf))
      roundsOf
      (syntacticTerminalPackedFamilyArity
        (oneLiteralThresholdPackedFamily roundsOf)) := by
  exact SyntacticTerminalClassParameterRegime.of_packedFamily
    (oneLiteralThresholdPackedFamily_ambientAdequate roundsOf)

/-- Pointwise S2143 entry feasibility for the one-literal exact-threshold family. -/
theorem SyntacticTerminalClassEntryFeasible.of_oneLiteralThresholdPackedFamily
    (roundsOf : Nat -> Nat) (d : Nat) :
    FormulaRecursiveSyntacticTerminalEntry.SyntacticTerminalClassEntryFeasible
      (syntacticTerminalPackedFamilySizeCap
        (oneLiteralThresholdPackedFamily roundsOf)) d (roundsOf d)
      (syntacticTerminalPackedFamilyArity
        (oneLiteralThresholdPackedFamily roundsOf) d) := by
  exact SyntacticTerminalClassEntryFeasible.of_packedFamily
    (oneLiteralThresholdPackedFamily_ambientAdequate roundsOf)

/-- Final-tree wrapper for the one-literal exact-threshold family. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_oneLiteralThresholdPackedFamily
    (roundsOf : Nat -> Nat) {d : Nat} (parent : ParentKind) :
    ∀ level, level <= depth (syntacticTerminalPackedFamilyFormula
        (oneLiteralThresholdPackedFamily roundsOf) d) ->
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula
          (oneLiteralThresholdPackedFamily roundsOf) d)
        (syntacticTerminalPackedFamilySizeCap
          (oneLiteralThresholdPackedFamily roundsOf)) d (roundsOf d) parent
        (oneLiteralThresholdPackedFamily_class roundsOf d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_packedFamily_predicates
      parent (oneLiteralThresholdPackedFamily_ambientAdequate roundsOf)
      (oneLiteralThresholdPackedFamily_depthBound roundsOf)
      (oneLiteralThresholdPackedFamily_class roundsOf)

end FormulaRecursiveSyntacticTerminalConcrete
end PvNP
