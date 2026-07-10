import PvNP.FormulaRecursiveSyntacticTerminalEntry

/-!
# Syntactic-terminal coarse parameter regimes

This module adds only a coarse size-cap sufficient condition for the S2143
syntactic-terminal entry predicate and routes the existing S2142 final-tree
consumer through that condition.  The class budget remains
`t(d,s)=S(d)*(s-1)`.  It does not prove product/counting synthesis, threshold
improvement, arbitrary normalization, arbitrary AC0/bounded-depth collapse, PHP
switching, Frege/PHP, NP/circuit lower bounds, P-vs-NP, or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalRegime

open BoundedDepthFrege
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalEntry

/-! ## Coarse single-depth entry feasibility -/

/-- A coarse, depth-independent size-cap variant of the S2143 entry threshold. -/
def syntacticTerminalClassCoarseEntryThreshold (M rounds : Nat) : Nat :=
  2 * (64 * M) ^ rounds * (64 * M * M)

/-- Single-depth sufficient condition: the class envelope at depth `d` is at most
`M`, and the ambient size is at least the coarse threshold at `M`. -/
def SyntacticTerminalClassCoarseEntryFeasible (S : Nat -> Nat)
    (d rounds M n : Nat) : Prop :=
  S d <= M ∧ syntacticTerminalClassCoarseEntryThreshold M rounds <= n

/-- The exact S2143 entry threshold is bounded by the coarse threshold whenever
the depth-`d` class envelope is bounded by `M`. -/
theorem syntacticTerminalClassEntryThreshold_le_coarse
    {S : Nat -> Nat} {d rounds M : Nat} (hM : S d <= M) :
    syntacticTerminalClassEntryThreshold S d rounds <=
      syntacticTerminalClassCoarseEntryThreshold M rounds := by
  have h64 : 64 * S d <= 64 * M := Nat.mul_le_mul_left 64 hM
  have hpow : (64 * S d) ^ rounds <= (64 * M) ^ rounds :=
    Nat.pow_le_pow_left h64 rounds
  have htail : 64 * S d * S d <= 64 * M * M :=
    Nat.mul_le_mul h64 hM
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) htail

/-- Coarse single-depth feasibility implies the named S2143 entry predicate. -/
theorem SyntacticTerminalClassEntryFeasible.of_coarse
    {S : Nat -> Nat} {d rounds M n : Nat}
    (hcoarse : SyntacticTerminalClassCoarseEntryFeasible S d rounds M n) :
    SyntacticTerminalClassEntryFeasible S d rounds n := by
  exact Nat.le_trans
    (syntacticTerminalClassEntryThreshold_le_coarse hcoarse.1)
    hcoarse.2

/-! ## Depth-indexed parameter regimes -/

/-- Depth-indexed coarse parameter regime: at each depth `d`, `M d` bounds the
class envelope `S d`, and `N d` meets the corresponding coarse threshold for
`roundsOf d`. -/
def SyntacticTerminalClassParameterRegime
    (S M roundsOf N : Nat -> Nat) : Prop :=
  ∀ d, S d <= M d ∧
    syntacticTerminalClassCoarseEntryThreshold (M d) (roundsOf d) <= N d

/-- A depth-indexed coarse parameter regime gives the named S2143 feasibility
predicate at every depth. -/
theorem SyntacticTerminalClassEntryFeasible.of_parameterRegime
    {S M roundsOf N : Nat -> Nat} {d : Nat}
    (hregime : SyntacticTerminalClassParameterRegime S M roundsOf N) :
    SyntacticTerminalClassEntryFeasible S d (roundsOf d) (N d) := by
  exact SyntacticTerminalClassEntryFeasible.of_coarse (hregime d)

/-- S2142 all-level final-tree theorem discharged from a depth-indexed coarse
parameter regime.  The class budget is unchanged from the S2142/S2143 consumer:
`formulaClassDepthTreeBudget S d`, i.e. `t(d,s)=S(d)*(s-1)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_parameterRegime
    {S M roundsOf N : Nat -> Nat} {d : Nat}
    (F : BDFormula (N d)) (parent : ParentKind)
    (hregime : SyntacticTerminalClassParameterRegime S M roundsOf N)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F) :
    ∀ level, level <= depth F ->
      SyntacticTerminalClassDepthFinalTreeAt F S d (roundsOf d) parent hClass level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_entryFeasible
      F S d (roundsOf d) parent hDepth hSize hClass
      (SyntacticTerminalClassEntryFeasible.of_parameterRegime hregime)

end FormulaRecursiveSyntacticTerminalRegime
end PvNP
