import PvNP.FormulaRecursiveSyntacticTerminalClassProfile

/-!
# Syntactic-terminal entry-size feasibility packet

This module names and discharges only the ambient geometric entry inequality used
by the S2142 syntactic-terminal class-budget final-tree theorem.  It is a small
feasibility/no-go wrapper for
`2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n`; it does not synthesize
product/counting hypotheses, arbitrary normal forms, arbitrary AC0 collapse,
PHP switching, Frege/PHP lower bounds, NP/circuit lower bounds, or P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalEntry

open BoundedDepthFrege
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open FormulaRecursiveSyntacticTerminalClassProfile

/-! ## Named entry threshold and feasibility predicate -/

/-- The exact ambient entry-size threshold used by the S2142 syntactic-terminal
class-budget theorem, with class budget `t(d,s)=S(d)*(s-1)`. -/
def syntacticTerminalClassEntryThreshold (S : Nat -> Nat)
    (d rounds : Nat) : Nat :=
  2 * (64 * S d) ^ rounds * (64 * S d * S d)

/-- Feasibility of the S2142 ambient entry inequality at ambient size `n`. -/
def SyntacticTerminalClassEntryFeasible (S : Nat -> Nat)
    (d rounds n : Nat) : Prop :=
  syntacticTerminalClassEntryThreshold S d rounds <= n

/-- The named feasibility predicate unfolds to the raw S2142 ambient inequality. -/
theorem syntacticTerminalClassEntryFeasible_iff (S : Nat -> Nat)
    (d rounds n : Nat) :
    SyntacticTerminalClassEntryFeasible S d rounds n ↔
      2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n := by
  rfl

/-- The exact threshold is feasible for the named S2142 entry predicate. -/
theorem syntacticTerminalClassEntryFeasible_exact (S : Nat -> Nat)
    (d rounds : Nat) :
    SyntacticTerminalClassEntryFeasible S d rounds
      (syntacticTerminalClassEntryThreshold S d rounds) := by
  exact Nat.le_refl _

/-- Feasibility is monotone in the ambient variable count. -/
theorem SyntacticTerminalClassEntryFeasible.mono_n {S : Nat -> Nat}
    {d rounds n n' : Nat}
    (hentry : SyntacticTerminalClassEntryFeasible S d rounds n)
    (hnn' : n <= n') :
    SyntacticTerminalClassEntryFeasible S d rounds n' := by
  exact Nat.le_trans hentry hnn'

/-- No-go below the exact threshold: the named entry predicate is impossible. -/
theorem not_syntacticTerminalClassEntryFeasible_of_lt_threshold
    {S : Nat -> Nat} {d rounds n : Nat}
    (hlt : n < syntacticTerminalClassEntryThreshold S d rounds) :
    ¬ SyntacticTerminalClassEntryFeasible S d rounds n := by
  intro hentry
  exact Nat.not_lt_of_ge hentry hlt

/-- Round-zero simplification of the named threshold. -/
theorem syntacticTerminalClassEntryThreshold_zero_rounds (S : Nat -> Nat)
    (d : Nat) :
    syntacticTerminalClassEntryThreshold S d 0 = 2 * (64 * S d * S d) := by
  simp [syntacticTerminalClassEntryThreshold]

/-! ## Routing S2142 through named entry feasibility -/

/-- S2142 all-level final-tree theorem routed through the named entry feasibility
predicate instead of the raw ambient inequality. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_entryFeasible
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hentry : SyntacticTerminalClassEntryFeasible S d rounds n) :
    forall level, level <= depth F ->
      SyntacticTerminalClassDepthFinalTreeAt F S d rounds parent hClass level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree
      F S d rounds parent hDepth hSize hClass hentry

/-- Exact-threshold discharge of the S2142 all-level final-tree theorem.  The
ambient inequality is supplied solely by `syntacticTerminalClassEntryThreshold`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_at_entryThreshold
    (S : Nat -> Nat) (d rounds : Nat)
    (F : BDFormula (syntacticTerminalClassEntryThreshold S d rounds))
    (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F) :
    forall level, level <= depth F ->
      SyntacticTerminalClassDepthFinalTreeAt F S d rounds parent hClass level := by
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_of_entryFeasible
      F S d rounds parent hDepth hSize hClass
      (syntacticTerminalClassEntryFeasible_exact S d rounds)

end FormulaRecursiveSyntacticTerminalEntry
end PvNP
