import PvNP.FormulaRecursiveSyntacticTerminalRegime

/-!
# Packed syntactic-terminal formula-family feasibility

This module adds only a Gate B family-derived source for the S2144 coarse
parameter regime.  The coarse cap `M` is the actual formula size of the packed
depth-indexed formula, and the ambient arity `N` is the actual packed arity.
The class budget remains `t(d,s)=S(d)*(s-1)` with `S` instantiated by the same
formula-derived size cap.  It does not prove product/counting synthesis,
threshold improvement, arbitrary normalization, arbitrary AC0/bounded-depth
collapse, full B4, PHP switching, Frege/PHP, NP/circuit lower bounds, P-vs-NP,
or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalFamily

open BoundedDepthFrege
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalEntry
open FormulaRecursiveSyntacticTerminalRegime

/-! ## Packed depth-indexed families -/

/-- A packed formula family whose ambient arity may vary with the depth index. -/
abbrev SyntacticTerminalPackedFamily : Type :=
  Nat -> Sigma (fun n => BDFormula n)

/-- The arity carried by a packed family at depth index `d`. -/
def syntacticTerminalPackedFamilyArity
    (F : SyntacticTerminalPackedFamily) (d : Nat) : Nat :=
  (F d).1

/-- The formula carried by a packed family at depth index `d`. -/
def syntacticTerminalPackedFamilyFormula
    (F : SyntacticTerminalPackedFamily) (d : Nat) :
    BDFormula (syntacticTerminalPackedFamilyArity F d) :=
  (F d).2

/-- The formula-size cap sourced from the packed family at depth index `d`. -/
def syntacticTerminalPackedFamilySizeCap
    (F : SyntacticTerminalPackedFamily) (d : Nat) : Nat :=
  formulaSize (syntacticTerminalPackedFamilyFormula F d)

/-- Every packed formula lies in the restricted syntactic-terminal class. -/
def SyntacticTerminalPackedFamilyClass
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∀ d, SyntacticTerminalFormulaClass (syntacticTerminalPackedFamilyFormula F d)

/-- Every packed formula has depth bounded by its depth index. -/
def SyntacticTerminalPackedFamilyDepthBound
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∀ d, depth (syntacticTerminalPackedFamilyFormula F d) <= d

/-- The packed ambient arity meets the S2144 coarse threshold for the actual
formula-size cap at every depth. -/
def SyntacticTerminalPackedFamilyAmbientAdequate
    (F : SyntacticTerminalPackedFamily) (roundsOf : Nat -> Nat) : Prop :=
  ∀ d,
    syntacticTerminalClassCoarseEntryThreshold
      (syntacticTerminalPackedFamilySizeCap F d) (roundsOf d) <=
        syntacticTerminalPackedFamilyArity F d

/-! ## Family-derived coarse regimes and consumers -/

/-- A packed family with adequate ambient arity induces the S2144 parameter
regime, taking both `S` and `M` to be the actual formula-size cap and `N` to be
the actual packed arity. -/
theorem SyntacticTerminalClassParameterRegime.of_packedFamily
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat}
    (hAmbient : SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf) :
    SyntacticTerminalClassParameterRegime
      (syntacticTerminalPackedFamilySizeCap F)
      (syntacticTerminalPackedFamilySizeCap F)
      roundsOf
      (syntacticTerminalPackedFamilyArity F) := by
  intro d
  exact ⟨Nat.le_refl _, hAmbient d⟩

/-- Pointwise S2143 entry feasibility from a packed family's actual size cap and
actual ambient arity. -/
theorem SyntacticTerminalClassEntryFeasible.of_packedFamily
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat} {d : Nat}
    (hAmbient : SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf) :
    SyntacticTerminalClassEntryFeasible
      (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d)
      (syntacticTerminalPackedFamilyArity F d) := by
  exact SyntacticTerminalClassEntryFeasible.of_parameterRegime
    (SyntacticTerminalClassParameterRegime.of_packedFamily hAmbient)

/-- Final-tree wrapper at a fixed depth, with `S` and `M` discharged by the
packed formula's actual size and `N` by the packed arity. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_packedFamily
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat} {d : Nat}
    (parent : ParentKind)
    (hAmbient : SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf)
    (hDepth : depth (syntacticTerminalPackedFamilyFormula F d) <= d)
    (hClass : SyntacticTerminalFormulaClass (syntacticTerminalPackedFamilyFormula F d)) :
    ∀ level, level <= depth (syntacticTerminalPackedFamilyFormula F d) ->
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d)
        (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d) parent hClass level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_parameterRegime
      (syntacticTerminalPackedFamilyFormula F d) parent
      (SyntacticTerminalClassParameterRegime.of_packedFamily hAmbient)
      hDepth (Nat.le_refl _) hClass

/-- Convenience final-tree wrapper consuming family-wide class/depth predicates. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_packedFamily_predicates
    {F : SyntacticTerminalPackedFamily} {roundsOf : Nat -> Nat} {d : Nat}
    (parent : ParentKind)
    (hAmbient : SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hClass : SyntacticTerminalPackedFamilyClass F) :
    ∀ level, level <= depth (syntacticTerminalPackedFamilyFormula F d) ->
      SyntacticTerminalClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d)
        (syntacticTerminalPackedFamilySizeCap F) d (roundsOf d) parent (hClass d) level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_packedFamily
      parent hAmbient (hDepth d) (hClass d)

end FormulaRecursiveSyntacticTerminalFamily
end PvNP
