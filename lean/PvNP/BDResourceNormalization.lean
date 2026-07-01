import PvNP.GraphIndexedBridge

/-!
# Bounded-depth resource normalization

This module documents normalization facts for the existing measured
bounded-depth Frege trace resources.  These facts only name the current accessor
semantics: `lineCount` is the node-count-style trace `size`, `maxFormulaDepth`
is conclusion-sequent formula depth, and profile budgets are supplied accessor
upper-bound pins.  This module does not extract PHP search from traces, prove a
lower bound, prove proof-system completeness, or inhabit any proof-complexity
route obligation.
-/

namespace PvNP

namespace BoundedDepthFrege

/-- Normalization facts for the current proof-trace resource accessors.  The
`lineCount` accessor is presently just trace `size`; `maxFormulaDepth` is the
maximum formula depth of the conclusion sequent, not an internal whole-trace
maximum. -/
structure BDProofTraceResourceNormalization {n : Nat} {Gamma : List (BDFormula n)}
    (pi : BDProofTrace Gamma) : Prop where
  lineCount_eq_size : pi.lineCount = pi.size
  maxFormulaDepth_eq_conclusionSequent :
    pi.maxFormulaDepth = BDProofTrace.sequentMaxFormulaDepth Gamma

namespace BDProofTrace

/-- Every measured proof trace satisfies the current resource-normalization
identities by definition of the existing accessors. -/
theorem resourceNormalization {n : Nat} {Gamma : List (BDFormula n)}
    (pi : BDProofTrace Gamma) :
    BDProofTraceResourceNormalization pi := by
  constructor <;> rfl

end BDProofTrace

/-- Normalization facts for the current refutation-trace resource accessors.
They route through the underlying proof trace, so `lineCount` remains
node-count-style trace `size`, and `maxFormulaDepth` remains conclusion-sequent
formula depth for `F.map neg`. -/
structure BDRefutationTraceResourceNormalization {n : Nat}
    {F : List (BDFormula n)} (pi : BDRefutationTrace F) : Prop where
  size_eq_proofSize : pi.size = pi.proof.size
  lineCount_eq_size : pi.lineCount = pi.size
  derivationDepth_eq_proofDerivationDepth :
    pi.derivationDepth = pi.proof.derivationDepth
  maxFormulaDepth_eq_conclusionSequent :
    pi.maxFormulaDepth = BDProofTrace.sequentMaxFormulaDepth (F.map neg)

namespace BDRefutationTrace

/-- Every measured refutation trace satisfies the current resource-normalization
identities by definition of the existing accessors. -/
theorem resourceNormalization {n : Nat} {F : List (BDFormula n)}
    (pi : BDRefutationTrace F) :
    BDRefutationTraceResourceNormalization pi := by
  constructor <;> rfl

end BDRefutationTrace

/-- The profile budget fields are supplied upper-bound pins for the existing
accessors.  This record does not assert minimality, lower bounds, or independent
Frege line accounting. -/
structure BDRefutationTraceProfileBudgetPins {n : Nat}
    {F : List (BDFormula n)} (profile : BDRefutationTraceProfile F) : Prop where
  sizeBudget_upperBound : profile.trace.size <= profile.sizeBudget
  lineCountBudget_upperBound : profile.trace.lineCount <= profile.lineCountBudget
  derivationDepthBudget_upperBound :
    profile.trace.derivationDepth <= profile.derivationDepthBudget
  maxFormulaDepthBudget_upperBound :
    profile.trace.maxFormulaDepth <= profile.maxFormulaDepthBudget

namespace BDRefutationTraceProfile

/-- Every profile carries exactly the supplied upper-bound proofs for its budget
fields. -/
theorem budgetPins {n : Nat} {F : List (BDFormula n)}
    (profile : BDRefutationTraceProfile F) :
    BDRefutationTraceProfileBudgetPins profile := by
  exact {
    sizeBudget_upperBound := profile.size_le_budget
    lineCountBudget_upperBound := profile.lineCount_le_budget
    derivationDepthBudget_upperBound := profile.derivationDepth_le_budget
    maxFormulaDepthBudget_upperBound := profile.maxFormulaDepth_le_budget }

end BDRefutationTraceProfile

end BoundedDepthFrege

namespace GraphIndexedBridge

open BoundedDepthFrege

/-- Fixed concrete S2051 consumer for the `twoCyclePath3` supplied measured
refutation trace.  It records only the existing resource-accessor normalization
facts for this trace; it is not an extraction, lower-bound, or completeness
statement. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_resourceNormalization :
    BDRefutationTraceResourceNormalization
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace := by
  exact BDRefutationTrace.resourceNormalization _

/-- Fixed concrete profile-budget equalities for the `twoCyclePath3` supplied
trace profile.  These are equality pins to the already-supplied accessors, not
minimality claims or proof-complexity lower bounds. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetEqualities :
    let trace := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace
    let profile := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
    And (profile.sizeBudget = trace.size)
      (And (profile.lineCountBudget = trace.lineCount)
        (And (profile.derivationDepthBudget = trace.derivationDepth)
          (profile.maxFormulaDepthBudget = trace.maxFormulaDepth))) := by
  exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

/-- Fixed concrete profile budget pins for the `twoCyclePath3` supplied measured
refutation trace profile. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins :
    BDRefutationTraceProfileBudgetPins
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile := by
  exact BDRefutationTraceProfile.budgetPins _

end GraphIndexedBridge

end PvNP
