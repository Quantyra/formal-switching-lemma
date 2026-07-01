import PvNP.GraphIndexedBridge
import PvNP.RestrictedPHPFloor

/-!
# Profiled route / restricted-PHP search boundary

This module records a conditional finite boundary between the concrete S2042
profiled `twoCyclePath3` route and the fixed `3 x 2` restricted-PHP
falsified-clause search floor.  It does not construct the search tree, prove
search correctness, extract PHP search from a bounded-depth trace, or assert a
Frege/PHP lower bound.
-/

namespace PvNP

open GraphIndexedBridge
open RestrictedPHPFloor

/-- Conditional finite boundary: if a supplied output-valued query tree is correct
for the fixed `3 x 2` PHP falsified-clause search problem, then the existing
finite search-query floor applies, while the concrete profiled route preserves
its erasure, local-unsat, and unresolved-route equality pins. -/
theorem twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute)
    (hroute :
      route =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute)
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hSearchCorrect :
      ∀ a : CNFModel.Assignment (Nat.succ (3 * 2)),
        ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    2 ≤ queryDepth T ∧
      route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation ∧
      (¬ ∃ a : CNFModel.Assignment 6,
        ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
          BoundedDepthFrege.eval a f = true) ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation := by
  subst route
  exact ⟨
    threeTwoPHPFalsifiedClauseSearchDepthFloor T hSearchCorrect,
    rfl,
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTraceProfile,
    rfl⟩

/-- Conditional premise-reduction form of the finite boundary: if a supplied query
tree evaluates to the fixed `3 x 2` PHP semantic selector, selector validity
provides the search-correctness premise consumed by the S2044 boundary. -/
theorem twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_of_evalSelector
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute)
    (hroute :
      route =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute)
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hEval :
      ∀ a : CNFModel.Assignment (Nat.succ (3 * 2)),
        queryEval a T = threeTwoPHPFalsifiedClauseSelector a) :
    2 ≤ queryDepth T ∧
      route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation ∧
      (¬ ∃ a : CNFModel.Assignment 6,
        ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
          BoundedDepthFrege.eval a f = true) ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation := by
  exact
    twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary
      route hroute T
      (threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector T hEval)

/-- Concrete fixed finite instantiation of the profiled-route/search boundary using
the S2047 query tree and its evaluation theorem.  This discharges only the finite
`hEval` premise; it does not extract PHP search from the bounded-depth trace. -/
theorem twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree :
    2 ≤ queryDepth threeTwoPHPFalsifiedClauseQueryTree ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation ∧
      (¬ ∃ a : CNFModel.Assignment 6,
        ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
          BoundedDepthFrege.eval a f = true) ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation := by
  exact
    twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_of_evalSelector
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute
      rfl
      threeTwoPHPFalsifiedClauseQueryTree
      threeTwoPHPFalsifiedClauseQueryTree_evalSelector

/-- Concrete resource-budget pin package for the fixed finite S2047 query tree.
This theorem packages the already-supplied concrete query tree together with its
explicit `BDRefutationTraceProfile` budget equalities; it does not derive budgets
from the query tree, extract search, or prove any lower bound. -/
theorem twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree_resourceBudgetPins :
    2 ≤ queryDepth threeTwoPHPFalsifiedClauseQueryTree ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation ∧
      (¬ ∃ a : CNFModel.Assignment 6,
        ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
          BoundedDepthFrege.eval a f = true) ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.sizeBudget =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_size ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.lineCountBudget =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_lineCount ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.derivationDepthBudget =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_derivationDepth ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.maxFormulaDepthBudget =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_maxFormulaDepth := by
  exact ⟨
    twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree.1,
    twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree.2.1,
    twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree.2.2.1,
    twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree.2.2.2,
    rfl,
    rfl,
    rfl,
    rfl⟩

end PvNP
