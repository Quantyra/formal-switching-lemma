import PvNP.BDResourceNormalization
import PvNP.RestrictedPHPFloor
import PvNP.BDTraceToSearchExtraction

/-!
# Trace/profile to search interface for the fixed `3 x 2` PHP search floor

This module originally named a premise-only interface for trace/profile-to-search
work over the fixed `3 x 2` restricted-PHP falsified-clause search problem.  As of
S2065 the S2052-S2064 obligation placeholders in this file carry real statement
content (realized by `PvNP.BDTraceToSearchExtraction`) and are proved for the
concrete `twoCyclePath3` profile/tree pair; see the S2065 section at the end of
this file.

## HONEST SCOPE STATEMENT (read this)

* The proved statements are a finite concrete-instance extraction bridge for ONE
  fixed six-variable identically-false CNF against ONE fixed `3 x 2` PHP
  falsified-clause search problem.  They are not proof-size/depth lower bounds,
  not Frege/PHP lower bounds, and not P vs NP statements.
* S2065 REDEFINITION DISCLOSURE: before S2065, the obligations converted here
  were deliberately constructorless `inductive ... : Prop` placeholders, which
  are uninhabitable by construction (logically equivalent to `False`).  Nothing
  "previously open" was proved under its old statement; the placeholders were
  given real, explicitly displayed content first, and that content was then
  proved.  The genuine open proof-complexity route obligation
  (`twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation`)
  is untouched and remains an empty non-claim.
* "Family" in this file always means the family of refutation trace profiles of
  the ONE fixed formula; formula-family generalization is not claimed.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace BDTraceToSearchPremise

open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor
open BDTraceToSearchExtraction

/-- Premise-only package indexed by a supplied bounded-depth refutation profile
for the fixed `3 x 2` PHP falsified-clause search problem.

The query tree and its correctness are supplied as fields.  The resource fields
are only the existing S2051 normalization and budget-pin facts for the supplied
profile; no tree extraction or lower-bound claim is made here. -/
structure ThreeTwoPHPSearchPremiseForProfile
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) : Type where
  tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause
  searchCorrect :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a tree)
  traceResourceNormalization :
    BDRefutationTraceResourceNormalization profile.trace
  profileBudgetPins :
    BDRefutationTraceProfileBudgetPins profile

namespace ThreeTwoPHPSearchPremiseForProfile

/-- Build the premise-only package from a supplied query tree and supplied
correctness proof.  This does not construct the tree from the profile. -/
def ofCorrectTree
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hT :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    ThreeTwoPHPSearchPremiseForProfile profile where
  tree := T
  searchCorrect := hT
  traceResourceNormalization := BDRefutationTrace.resourceNormalization profile.trace
  profileBudgetPins := BDRefutationTraceProfile.budgetPins profile

/-- Selector-equality premise constructor: the tree is still supplied; correctness is
derived only from a supplied equality to the fixed finite selector. -/
def ofEvalSelector
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hEval :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        queryEval a T = threeTwoPHPFalsifiedClauseSelector a) :
    ThreeTwoPHPSearchPremiseForProfile profile :=
  ofCorrectTree profile T
    (threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector T hEval)

/-- Fixed finite consequence of the supplied search-correctness premise. -/
theorem depthFloor
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (P : ThreeTwoPHPSearchPremiseForProfile profile) :
    2 <= queryDepth P.tree :=
  threeTwoPHPFalsifiedClauseSearchDepthFloor P.tree P.searchCorrect

end ThreeTwoPHPSearchPremiseForProfile

/-- Fixed `twoCyclePath3` route shell connecting the existing profiled route to a
supplied `3 x 2` PHP search premise.

This is a shell only: it pins the route to the concrete S2042 route and carries a
supplied search premise.  It does not construct the premise from the profile. -/
structure TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell : Type where
  route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute
  route_eq :
    route =
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute
  searchPremise : ThreeTwoPHPSearchPremiseForProfile route.profile

namespace TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell

/-- Build the route shell from a supplied profiled route and supplied correct
query tree.  No trace/profile-to-tree extraction is performed. -/
def ofCorrectTree
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute)
    (hroute :
      route =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute)
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hT :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell where
  route := route
  route_eq := hroute
  searchPremise := ThreeTwoPHPSearchPremiseForProfile.ofCorrectTree route.profile T hT

/-- Build the route shell from a supplied profiled route and a supplied equality
between the query tree and the fixed finite selector. -/
def ofEvalSelector
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute)
    (hroute :
      route =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute)
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hEval :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        queryEval a T = threeTwoPHPFalsifiedClauseSelector a) :
    TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell where
  route := route
  route_eq := hroute
  searchPremise := ThreeTwoPHPSearchPremiseForProfile.ofEvalSelector route.profile T hEval

/-- Consequences of the premise-only shell.  The search floor comes only from the
supplied search premise; route/profile facts are existing profiled-route fields
and S2051 budget pins. -/
theorem boundaryFacts
    (S : TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell) :
    2 <= queryDepth S.searchPremise.tree /\
      S.route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation /\
      (Not (Exists fun a : CNFModel.Assignment 6 =>
        forall f,
          Membership.mem [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] f ->
            BoundedDepthFrege.eval a f = true)) /\
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation /\
      BDRefutationTraceProfileBudgetPins S.route.profile := by
  exact And.intro
    (ThreeTwoPHPSearchPremiseForProfile.depthFloor S.searchPremise)
    (And.intro
      S.route.erases_to_suppliedBDRefutation
      (And.intro
        S.route.localUnsat
        (And.intro
          S.route.remainingUnresolvedProofComplexityRoute_eq
          S.searchPremise.profileBudgetPins)))

end TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell

/-! ## S2054 route-obligation taxonomy -/

/-- Classification labels for trace/profile to search route obligations.  These
labels are bookkeeping only: they do not discharge any obligation. -/
inductive TraceToSearchRouteObligationClass where
  | suppliedProfiledRouteResourceFact
  | suppliedFixedFiniteSearchPremiseFact
  | localFutureBridgeTarget
  | unresolvedProofComplexityBlocker

/-- A named trace/profile to search route obligation together with its planning
classification.  The proposition field is recorded, not proved, by this record. -/
structure TraceToSearchRouteObligation where
  name : String
  proposition : Prop
  classification : TraceToSearchRouteObligationClass

/-- Route-obligation map separating supplied route/resource facts, supplied fixed
finite search-premise facts, a local future bridge target, and the existing
unresolved proof-complexity blocker. -/
structure TraceToSearchRouteObligations where
  suppliedProfiledRouteResourceFacts : TraceToSearchRouteObligation
  suppliedFixedFiniteSearchPremiseFacts : TraceToSearchRouteObligation
  localFutureBridgeTarget : TraceToSearchRouteObligation
  unresolvedProofComplexityBlocker : TraceToSearchRouteObligation
  suppliedProfiledRouteResourceFacts_classification :
    suppliedProfiledRouteResourceFacts.classification =
      TraceToSearchRouteObligationClass.suppliedProfiledRouteResourceFact
  suppliedFixedFiniteSearchPremiseFacts_classification :
    suppliedFixedFiniteSearchPremiseFacts.classification =
      TraceToSearchRouteObligationClass.suppliedFixedFiniteSearchPremiseFact
  localFutureBridgeTarget_classification :
    localFutureBridgeTarget.classification =
      TraceToSearchRouteObligationClass.localFutureBridgeTarget
  unresolvedProofComplexityBlocker_classification :
    unresolvedProofComplexityBlocker.classification =
      TraceToSearchRouteObligationClass.unresolvedProofComplexityBlocker

/-- Conjoin the named route obligations.  This only records the remaining route
work as a proposition. -/
def traceToSearchRouteObligations_remainingRouteObligations
    (obligations : TraceToSearchRouteObligations) : Prop :=
  obligations.suppliedProfiledRouteResourceFacts.proposition /\
    obligations.suppliedFixedFiniteSearchPremiseFacts.proposition /\
      obligations.localFutureBridgeTarget.proposition /\
        obligations.unresolvedProofComplexityBlocker.proposition

/-- Projection of the supplied profiled route/resource facts from the named
route-obligation conjunction. -/
theorem traceToSearchRouteObligations_suppliedProfiledRouteResourceFacts
    (obligations : TraceToSearchRouteObligations) :
    traceToSearchRouteObligations_remainingRouteObligations obligations ->
      obligations.suppliedProfiledRouteResourceFacts.proposition := by
  intro h
  exact h.1

/-- Projection of the supplied fixed finite search-premise facts from the named
route-obligation conjunction. -/
theorem traceToSearchRouteObligations_suppliedFixedFiniteSearchPremiseFacts
    (obligations : TraceToSearchRouteObligations) :
    traceToSearchRouteObligations_remainingRouteObligations obligations ->
      obligations.suppliedFixedFiniteSearchPremiseFacts.proposition := by
  intro h
  exact h.2.1

/-- Projection of the local future bridge target from the named route-obligation
conjunction. -/
theorem traceToSearchRouteObligations_localFutureBridgeTarget
    (obligations : TraceToSearchRouteObligations) :
    traceToSearchRouteObligations_remainingRouteObligations obligations ->
      obligations.localFutureBridgeTarget.proposition := by
  intro h
  exact h.2.2.1

/-- The route-obligation map preserves the intended classification of each named
obligation. -/
theorem traceToSearchRouteObligations_classifications
    (obligations : TraceToSearchRouteObligations) :
    obligations.suppliedProfiledRouteResourceFacts.classification =
        TraceToSearchRouteObligationClass.suppliedProfiledRouteResourceFact /\
      obligations.suppliedFixedFiniteSearchPremiseFacts.classification =
        TraceToSearchRouteObligationClass.suppliedFixedFiniteSearchPremiseFact /\
      obligations.localFutureBridgeTarget.classification =
        TraceToSearchRouteObligationClass.localFutureBridgeTarget /\
      obligations.unresolvedProofComplexityBlocker.classification =
        TraceToSearchRouteObligationClass.unresolvedProofComplexityBlocker := by
  exact And.intro obligations.suppliedProfiledRouteResourceFacts_classification
    (And.intro obligations.suppliedFixedFiniteSearchPremiseFacts_classification
      (And.intro obligations.localFutureBridgeTarget_classification
        obligations.unresolvedProofComplexityBlocker_classification))

/-- Supplied profiled route/resource fact proposition for the concrete route. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts :
    Prop :=
  twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile /\
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.erase =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation /\
    BDRefutationTraceProfileBudgetPins
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile

/-- Supplied fixed finite search-premise fact proposition for the concrete route
interface. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts :
    Prop :=
  forall profile :
    BDRefutationTraceProfile
      [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
    forall P : ThreeTwoPHPSearchPremiseForProfile profile,
      2 <= queryDepth P.tree

/-- The local future bridge target for the trace/profile to fixed finite
search-premise route.  Before S2065 this was a constructorless placeholder; it
now states the actual local bridge content: the fixed `3 x 2` query tree and the
tree extracted from every trace profile of the fixed formula both compute the
fixed finite semantic selector.  Correctness is order-independent at this fixed
instance (the search problem is total), so the logical dependence of
correctness on the trace is nil.  Proved in the S2065 section below; this is a
finite concrete-instance statement only, not a lower bound. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation :
    Prop where
  fixedTreeEvalSelector :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a threeTwoPHPFalsifiedClauseQueryTree =
        threeTwoPHPFalsifiedClauseSelector a
  extractedEvalSelector :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
      (a : CNFModel.Assignment (Nat.succ (3 * 2))),
      queryEval a (extractQueryTree profile) =
        threeTwoPHPFalsifiedClauseSelector a

/-- Supplied profiled route/resource facts named as a route obligation. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsRouteObligation :
    TraceToSearchRouteObligation where
  name := "twoCyclePath3 supplied profiled route and resource facts"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts
  classification :=
    TraceToSearchRouteObligationClass.suppliedProfiledRouteResourceFact

/-- Supplied fixed finite search-premise facts named as a route obligation. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsRouteObligation :
    TraceToSearchRouteObligation where
  name := "twoCyclePath3 supplied fixed finite search-premise facts"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts
  classification :=
    TraceToSearchRouteObligationClass.suppliedFixedFiniteSearchPremiseFact

/-- Local future bridge target named as a route obligation. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligationNamed :
    TraceToSearchRouteObligation where
  name := "twoCyclePath3 local future bridge target"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation
  classification :=
    TraceToSearchRouteObligationClass.localFutureBridgeTarget

/-- Existing unresolved proof-complexity blocker named as a route obligation. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_unresolvedProofComplexityBlockerRouteObligation :
    TraceToSearchRouteObligation where
  name := "twoCyclePath3 unresolved proof-complexity blocker"
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation
  classification :=
    TraceToSearchRouteObligationClass.unresolvedProofComplexityBlocker

/-- Concrete S2054 trace/profile to search route-obligation map. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations :
    TraceToSearchRouteObligations where
  suppliedProfiledRouteResourceFacts :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsRouteObligation
  suppliedFixedFiniteSearchPremiseFacts :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsRouteObligation
  localFutureBridgeTarget :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligationNamed
  unresolvedProofComplexityBlocker :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_unresolvedProofComplexityBlockerRouteObligation
  suppliedProfiledRouteResourceFacts_classification := rfl
  suppliedFixedFiniteSearchPremiseFacts_classification := rfl
  localFutureBridgeTarget_classification := rfl
  unresolvedProofComplexityBlocker_classification := rfl

/-- Classification proposition for the concrete route-obligation map. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligationsClassifications :
    Prop :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations.suppliedProfiledRouteResourceFacts.classification =
      TraceToSearchRouteObligationClass.suppliedProfiledRouteResourceFact /\
    (twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations.suppliedFixedFiniteSearchPremiseFacts.classification =
      TraceToSearchRouteObligationClass.suppliedFixedFiniteSearchPremiseFact /\
    (twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations.localFutureBridgeTarget.classification =
      TraceToSearchRouteObligationClass.localFutureBridgeTarget /\
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations.unresolvedProofComplexityBlocker.classification =
      TraceToSearchRouteObligationClass.unresolvedProofComplexityBlocker))

/-- The concrete route-obligation map preserves the intended classes. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations_classifications :
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligationsClassifications := by
  exact traceToSearchRouteObligations_classifications
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations

/-! ## S2055 local bridge decomposition -/

/-- Explicit fixed finite search-premise inputs for a supplied profile.  The tree
and correctness proof are supplied; this record does not obtain them from the
profile. -/
structure ThreeTwoPHPSearchPremiseInputsForProfile
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) : Type where
  tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause
  searchCorrect :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a tree)

namespace ThreeTwoPHPSearchPremiseInputsForProfile

/-- Build the input record from a supplied tree and supplied correctness proof. -/
def ofCorrectTree
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hT :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    ThreeTwoPHPSearchPremiseInputsForProfile profile where
  tree := T
  searchCorrect := hT

/-- Build the input record from a supplied tree and supplied equality to the fixed
finite selector. -/
def ofEvalSelector
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hEval :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        queryEval a T = threeTwoPHPFalsifiedClauseSelector a) :
    ThreeTwoPHPSearchPremiseInputsForProfile profile :=
  ofCorrectTree profile T
    (threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector T hEval)

/-- Conditional construction of the S2052 premise from explicitly supplied search
inputs. -/
def toSearchPremise
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (inputs : ThreeTwoPHPSearchPremiseInputsForProfile profile) :
    ThreeTwoPHPSearchPremiseForProfile profile :=
  ThreeTwoPHPSearchPremiseForProfile.ofCorrectTree
    profile inputs.tree inputs.searchCorrect

/-- Projection of the fixed finite depth consequence from supplied search inputs. -/
theorem depthFloor
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (inputs : ThreeTwoPHPSearchPremiseInputsForProfile profile) :
    2 <= queryDepth inputs.tree :=
  threeTwoPHPFalsifiedClauseSearchDepthFloor inputs.tree inputs.searchCorrect

/-- The premise constructed from supplied inputs preserves the supplied tree. -/
theorem toSearchPremise_tree
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (inputs : ThreeTwoPHPSearchPremiseInputsForProfile profile) :
    inputs.toSearchPremise.tree = inputs.tree :=
  rfl

end ThreeTwoPHPSearchPremiseInputsForProfile

/-- Explicit local bridge evidence for a supplied profiled route.  It carries the
route pin, the supplied search inputs, and the still-unproved S2054 local bridge
obligation as a field.  No declaration in this module constructs this evidence. -/
structure TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute) : Type where
  route_eq :
    route =
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute
  premiseInputs : ThreeTwoPHPSearchPremiseInputsForProfile route.profile
  localBridgeObligation :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation

namespace TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence

/-- Projection of the supplied local bridge obligation from explicit bridge
evidence. -/
theorem localBridgeObligation_project
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (evidence :
      TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence route) :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation :=
  evidence.localBridgeObligation

/-- Conditional construction of the search premise from explicit bridge evidence. -/
def searchPremise
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (evidence :
      TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence route) :
    ThreeTwoPHPSearchPremiseForProfile route.profile :=
  evidence.premiseInputs.toSearchPremise

/-- Conditional route shell obtained from explicit bridge evidence. -/
def routeShell
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (evidence :
      TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence route) :
    TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell where
  route := route
  route_eq := evidence.route_eq
  searchPremise := evidence.searchPremise

/-- Conditional boundary facts obtained only from explicit bridge evidence. -/
theorem routeShell_boundaryFacts
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (evidence :
      TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence route) :
    2 <= queryDepth (evidence.routeShell.searchPremise.tree) /\
      evidence.routeShell.route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation /\
      (Not (Exists fun a : CNFModel.Assignment 6 =>
        forall f,
          Membership.mem [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] f ->
            BoundedDepthFrege.eval a f = true)) /\
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation /\
      BDRefutationTraceProfileBudgetPins evidence.routeShell.route.profile := by
  exact TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.boundaryFacts
    evidence.routeShell

end TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence

/-- Exact S2055 local future bridge target with explicit route equality and bridge
evidence hypotheses.  This target is named only; it is not proved here. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget :
    Prop :=
  forall route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute,
    route =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute ->
      Nonempty
        (TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence route)

/-- Projection of the concrete-route case from explicitly supplied S2055 target
evidence. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget_concrete
    (h :
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget) :
    Nonempty
      (TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute) :=
  h _ rfl

/-! ## S2056 local bridge antecedent taxonomy -/

/-- Classification labels for antecedents around the local future bridge target.
These labels separate already supplied finite facts from genuinely missing bridge
work; they do not discharge any missing obligation. -/
inductive TraceToSearchLocalBridgeAntecedentClass where
  | suppliedProfiledRouteResourceFact
  | suppliedFixedFiniteSearchPremiseFact
  | missingTraceToSearchExtraction
  | missingSelectorTransfer
  | missingProfileCompatibility

/-- A named local-bridge antecedent together with its planning classification. -/
structure TraceToSearchLocalBridgeAntecedent where
  name : String
  proposition : Prop
  classification : TraceToSearchLocalBridgeAntecedentClass

/-- Local-bridge antecedent taxonomy for the trace/profile-to-search step.  The
record is metadata only: it keeps supplied facts separate from missing extraction,
selector-transfer, and profile-compatibility obligations. -/
structure TraceToSearchLocalBridgeAntecedents where
  suppliedProfiledRouteResourceFacts : TraceToSearchLocalBridgeAntecedent
  suppliedFixedFiniteSearchPremiseFacts : TraceToSearchLocalBridgeAntecedent
  traceToSearchExtraction : TraceToSearchLocalBridgeAntecedent
  selectorTransfer : TraceToSearchLocalBridgeAntecedent
  profileCompatibility : TraceToSearchLocalBridgeAntecedent
  suppliedProfiledRouteResourceFacts_classification :
    suppliedProfiledRouteResourceFacts.classification =
      TraceToSearchLocalBridgeAntecedentClass.suppliedProfiledRouteResourceFact
  suppliedFixedFiniteSearchPremiseFacts_classification :
    suppliedFixedFiniteSearchPremiseFacts.classification =
      TraceToSearchLocalBridgeAntecedentClass.suppliedFixedFiniteSearchPremiseFact
  traceToSearchExtraction_classification :
    traceToSearchExtraction.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction
  selectorTransfer_classification :
    selectorTransfer.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingSelectorTransfer
  profileCompatibility_classification :
    profileCompatibility.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingProfileCompatibility

/-- Conjoin every named antecedent.  Supplying this proposition would provide the
classified inputs; defining it proves none of them. -/
def traceToSearchLocalBridgeAntecedents_remainingAntecedents
    (antecedents : TraceToSearchLocalBridgeAntecedents) : Prop :=
  antecedents.suppliedProfiledRouteResourceFacts.proposition /\
    antecedents.suppliedFixedFiniteSearchPremiseFacts.proposition /\
      antecedents.traceToSearchExtraction.proposition /\
        antecedents.selectorTransfer.proposition /\
          antecedents.profileCompatibility.proposition

/-- Projection of the supplied profiled route/resource facts from the antecedent
conjunction. -/
theorem traceToSearchLocalBridgeAntecedents_suppliedProfiledRouteResourceFacts
    (antecedents : TraceToSearchLocalBridgeAntecedents) :
    traceToSearchLocalBridgeAntecedents_remainingAntecedents antecedents ->
      antecedents.suppliedProfiledRouteResourceFacts.proposition := by
  intro h
  exact h.1

/-- Projection of the supplied fixed finite search-premise facts from the
antecedent conjunction. -/
theorem traceToSearchLocalBridgeAntecedents_suppliedFixedFiniteSearchPremiseFacts
    (antecedents : TraceToSearchLocalBridgeAntecedents) :
    traceToSearchLocalBridgeAntecedents_remainingAntecedents antecedents ->
      antecedents.suppliedFixedFiniteSearchPremiseFacts.proposition := by
  intro h
  exact h.2.1

/-- Projection of the still-missing trace-to-search extraction obligation from
the antecedent conjunction. -/
theorem traceToSearchLocalBridgeAntecedents_traceToSearchExtraction
    (antecedents : TraceToSearchLocalBridgeAntecedents) :
    traceToSearchLocalBridgeAntecedents_remainingAntecedents antecedents ->
      antecedents.traceToSearchExtraction.proposition := by
  intro h
  exact h.2.2.1

/-- Projection of the still-missing selector-transfer obligation from the
antecedent conjunction. -/
theorem traceToSearchLocalBridgeAntecedents_selectorTransfer
    (antecedents : TraceToSearchLocalBridgeAntecedents) :
    traceToSearchLocalBridgeAntecedents_remainingAntecedents antecedents ->
      antecedents.selectorTransfer.proposition := by
  intro h
  exact h.2.2.2.1

/-- Projection of the still-missing profile-compatibility obligation from the
antecedent conjunction. -/
theorem traceToSearchLocalBridgeAntecedents_profileCompatibility
    (antecedents : TraceToSearchLocalBridgeAntecedents) :
    traceToSearchLocalBridgeAntecedents_remainingAntecedents antecedents ->
      antecedents.profileCompatibility.proposition := by
  intro h
  exact h.2.2.2.2

/-- The antecedent taxonomy preserves the intended classification of each named
antecedent. -/
theorem traceToSearchLocalBridgeAntecedents_classifications
    (antecedents : TraceToSearchLocalBridgeAntecedents) :
    antecedents.suppliedProfiledRouteResourceFacts.classification =
        TraceToSearchLocalBridgeAntecedentClass.suppliedProfiledRouteResourceFact /\
      antecedents.suppliedFixedFiniteSearchPremiseFacts.classification =
        TraceToSearchLocalBridgeAntecedentClass.suppliedFixedFiniteSearchPremiseFact /\
      antecedents.traceToSearchExtraction.classification =
        TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction /\
      antecedents.selectorTransfer.classification =
        TraceToSearchLocalBridgeAntecedentClass.missingSelectorTransfer /\
      antecedents.profileCompatibility.classification =
        TraceToSearchLocalBridgeAntecedentClass.missingProfileCompatibility := by
  exact And.intro antecedents.suppliedProfiledRouteResourceFacts_classification
    (And.intro antecedents.suppliedFixedFiniteSearchPremiseFacts_classification
      (And.intro antecedents.traceToSearchExtraction_classification
        (And.intro antecedents.selectorTransfer_classification
          antecedents.profileCompatibility_classification)))

/-- The trace/profile-to-search extraction obligation for the concrete local
bridge route.  Before S2065 this was a constructorless placeholder (named
`..._missingTraceToSearchExtractionObligation`); it now states the actual
extraction content: the tree extracted from every trace profile of the fixed
formula computes the fixed finite semantic selector.  Correctness is
order-independent at this fixed instance (the search problem is total), so the
logical dependence of correctness on the trace is nil.  Proved in the S2065
section below; finite concrete-instance statement only. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation :
    Prop where
  extractedEvalSelector :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
      (a : CNFModel.Assignment (Nat.succ (3 * 2))),
      queryEval a (extractQueryTree profile) =
        threeTwoPHPFalsifiedClauseSelector a

/-- The transfer from extracted search data to the fixed finite
selector/query-tree interface.  Before S2065 this was a constructorless
placeholder (named `..._missingSelectorTransferObligation`); it now states the
actual transfer content.  Proved in the S2065 section below. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation :
    Prop where
  fixedTreeEvalSelector :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a threeTwoPHPFalsifiedClauseQueryTree =
        threeTwoPHPFalsifiedClauseSelector a
  extractedMatchesFixedTree :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
      (a : CNFModel.Assignment (Nat.succ (3 * 2))),
      queryEval a (extractQueryTree profile) =
        queryEval a threeTwoPHPFalsifiedClauseQueryTree

/-- The compatibility between the profiled route data and the
extraction/selector-transfer payload.  Before S2065 this was a constructorless
placeholder (named `..._missingProfileCompatibilityObligation`); it now states
the actual compatibility content.  Proved in the S2065 section below. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation :
    Prop where
  profileErasesToSuppliedBDRefutation :
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile.erase =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation
  profileBudgetPins :
    BDRefutationTraceProfileBudgetPins
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile

/-- Supplied profiled route/resource facts as a local-bridge antecedent. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 supplied profiled route/resource antecedent"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.suppliedProfiledRouteResourceFact

/-- Supplied fixed finite search-premise facts as a local-bridge antecedent. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 supplied fixed finite search-premise antecedent"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.suppliedFixedFiniteSearchPremiseFact

/-- Missing trace/profile-to-search extraction antecedent for the local bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingTraceToSearchExtractionAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 missing trace-to-search extraction antecedent"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction

/-- Missing selector-transfer antecedent for the local bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingSelectorTransferAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 missing selector-transfer antecedent"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.missingSelectorTransfer

/-- Missing profile-compatibility antecedent for the local bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingProfileCompatibilityAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 missing profile-compatibility antecedent"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.missingProfileCompatibility

/-- Concrete S2056 local-bridge antecedent taxonomy. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents :
    TraceToSearchLocalBridgeAntecedents where
  suppliedProfiledRouteResourceFacts :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsAntecedent
  suppliedFixedFiniteSearchPremiseFacts :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsAntecedent
  traceToSearchExtraction :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingTraceToSearchExtractionAntecedent
  selectorTransfer :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingSelectorTransferAntecedent
  profileCompatibility :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingProfileCompatibilityAntecedent
  suppliedProfiledRouteResourceFacts_classification := rfl
  suppliedFixedFiniteSearchPremiseFacts_classification := rfl
  traceToSearchExtraction_classification := rfl
  selectorTransfer_classification := rfl
  profileCompatibility_classification := rfl

/-- Classification proposition for the concrete local-bridge antecedent taxonomy. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedentsClassifications :
    Prop :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents.suppliedProfiledRouteResourceFacts.classification =
      TraceToSearchLocalBridgeAntecedentClass.suppliedProfiledRouteResourceFact /\
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents.suppliedFixedFiniteSearchPremiseFacts.classification =
      TraceToSearchLocalBridgeAntecedentClass.suppliedFixedFiniteSearchPremiseFact /\
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents.traceToSearchExtraction.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction /\
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents.selectorTransfer.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingSelectorTransfer /\
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents.profileCompatibility.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingProfileCompatibility

/-- The concrete local-bridge antecedent taxonomy preserves the intended classes. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents_classifications :
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedentsClassifications := by
  exact traceToSearchLocalBridgeAntecedents_classifications
    twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents

/-! ## S2057 trace-to-search extraction witness contract -/

/-- The local semantic bridge between a bounded-depth refutation trace profile
and a candidate fixed finite query tree.  Before S2065 this was a constructorless
placeholder; it now states the actual bridge content: the tree extracted from the
profile computes the fixed finite semantic selector, agrees with the candidate
tree, inherits the fixed `3 x 2` search depth floor, and the embedded fixed CNF
and the PHP search instance share every ambient assignment as a common falsifying
extension.  Proved for the concrete `twoCyclePath3` profile/tree pair in the
S2065 section below.

The extraction consumes the trace's literal excluded-middle query order, but its
correctness is order-independent because the fixed `3 x 2` search problem is
total; at this fixed instance the logical dependence of correctness on the trace
is nil.  This is a finite concrete-instance bridge only, not a lower bound. -/
structure TraceProfileToQueryExtractionBridgeObligation
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause) : Prop where
  extractedEvalSelector :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a (extractQueryTree profile) =
        threeTwoPHPFalsifiedClauseSelector a
  extractedMatchesTree :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a (extractQueryTree profile) = queryEval a tree
  extractedDepthFloor : 2 <= queryDepth (extractQueryTree profile)
  instanceCompatibility :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      BoundedDepthFrege.eval (fun i => a (phpVarEmbedding i))
          twoCyclePath3GeneratedBridgeWitness_cnfBDFormula = false /\
        ThreeTwoPHPFalsifiedClause.Valid a
          (threeTwoPHPFalsifiedClauseSelector a)

/-- Proof-bearing constructor field that future trace/profile-to-search extraction
must supply between a bounded-depth refutation profile and a candidate fixed
finite query tree.  S2061 decomposes the field into explicit fixed profile/tree
pins, already-audited selector and profile-budget semantics, and one still-
unproved trace/profile-to-query bridge field. -/
structure TraceToSearchExtractionConstructorFieldObligation
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause) : Prop where
  profile_eq :
    profile =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  tree_eq : tree = threeTwoPHPFalsifiedClauseQueryTree
  profileBudgetPins : BDRefutationTraceProfileBudgetPins profile
  selectorEval :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a tree = threeTwoPHPFalsifiedClauseSelector a
  traceProfileToQueryBridge :
    TraceProfileToQueryExtractionBridgeObligation profile tree

namespace TraceToSearchExtractionConstructorFieldObligation

/-- Projection of the concrete-profile identity pin from an explicitly supplied
constructor-field obligation. -/
theorem profile_eq_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (field : TraceToSearchExtractionConstructorFieldObligation profile tree) :
    profile =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile :=
  field.profile_eq

/-- Projection of the fixed query-tree identity pin from an explicitly supplied
constructor-field obligation. -/
theorem tree_eq_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (field : TraceToSearchExtractionConstructorFieldObligation profile tree) :
    tree = threeTwoPHPFalsifiedClauseQueryTree :=
  field.tree_eq

/-- Projection of the already-audited profile budget pins from an explicitly
supplied constructor-field obligation. -/
theorem profileBudgetPins_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (field : TraceToSearchExtractionConstructorFieldObligation profile tree) :
    BDRefutationTraceProfileBudgetPins profile :=
  field.profileBudgetPins

/-- Projection of the fixed selector-evaluation semantics from an explicitly
supplied constructor-field obligation. -/
theorem selectorEval_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (field : TraceToSearchExtractionConstructorFieldObligation profile tree) :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a tree = threeTwoPHPFalsifiedClauseSelector a :=
  field.selectorEval

/-- Projection of the exact remaining trace/profile-to-query extraction bridge
from an explicitly supplied constructor-field obligation. -/
theorem traceProfileToQueryBridge_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (field : TraceToSearchExtractionConstructorFieldObligation profile tree) :
    TraceProfileToQueryExtractionBridgeObligation profile tree :=
  field.traceProfileToQueryBridge

/-- Packaging constructor for the decomposed semantic fields.  This does not
produce the local bridge field; it only packages an explicitly supplied one. -/
def ofSemanticFields
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (profile_eq :
      profile =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile)
    (tree_eq : tree = threeTwoPHPFalsifiedClauseQueryTree)
    (profileBudgetPins : BDRefutationTraceProfileBudgetPins profile)
    (selectorEval :
      forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
        queryEval a tree = threeTwoPHPFalsifiedClauseSelector a)
    (traceProfileToQueryBridge :
      TraceProfileToQueryExtractionBridgeObligation profile tree) :
    TraceToSearchExtractionConstructorFieldObligation profile tree where
  profile_eq := profile_eq
  tree_eq := tree_eq
  profileBudgetPins := profileBudgetPins
  selectorEval := selectorEval
  traceProfileToQueryBridge := traceProfileToQueryBridge

end TraceToSearchExtractionConstructorFieldObligation

/-- Proof-bearing relation contract for future trace/profile-to-search extraction.
The relation now has a constructor, but constructing it requires the explicit
constructor-field obligation above; no declaration in this module supplies that
field for the concrete `twoCyclePath3` profile/tree pair. -/
structure TraceToSearchExtractionRelation
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause) : Prop where
  constructorField : TraceToSearchExtractionConstructorFieldObligation profile tree

namespace TraceToSearchExtractionRelation

/-- Projection of the proof-bearing constructor field from an explicitly supplied
extraction relation. -/
theorem constructorField_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (relation : TraceToSearchExtractionRelation profile tree) :
    TraceToSearchExtractionConstructorFieldObligation profile tree :=
  relation.constructorField

/-- Constructor for the relation from the explicit proof-bearing field.  This is
only a packaging constructor; it does not produce the field. -/
def ofConstructorField
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (field : TraceToSearchExtractionConstructorFieldObligation profile tree) :
    TraceToSearchExtractionRelation profile tree where
  constructorField := field

end TraceToSearchExtractionRelation

/-- Supplied transfer evidence from a candidate extracted tree to the fixed
finite `3 x 2` selector.  This record is supplied evidence only; it does not
extract the tree from the profile. -/
structure TraceToSearchSelectorTransferEvidence
    (tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause) : Prop where
  evalSelector :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a tree = threeTwoPHPFalsifiedClauseSelector a

namespace TraceToSearchSelectorTransferEvidence

/-- Conditional search-correctness consequence of supplied selector-transfer
evidence. -/
theorem searchCorrect
    {tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause}
    (transfer : TraceToSearchSelectorTransferEvidence tree) :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a tree) :=
  threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector tree transfer.evalSelector

end TraceToSearchSelectorTransferEvidence

/-- Profile-level witness contract for future trace-to-search extraction.  It
carries an explicit candidate tree, a still-unproved extraction relation for that
tree, and supplied selector-transfer evidence.  No declaration here constructs
this witness from a bounded-depth profile. -/
structure TraceToSearchExtractionWitnessForProfile
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) : Type where
  tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause
  extractionEvidence : TraceToSearchExtractionRelation profile tree
  selectorTransfer : TraceToSearchSelectorTransferEvidence tree

namespace TraceToSearchExtractionWitnessForProfile

/-- Projection of the unproved extraction relation from an explicitly supplied
witness contract. -/
theorem extractionRelation_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (witness : TraceToSearchExtractionWitnessForProfile profile) :
    TraceToSearchExtractionRelation profile witness.tree :=
  witness.extractionEvidence

/-- Projection of supplied selector-transfer evidence from an explicitly supplied
witness contract. -/
theorem selectorTransfer_project
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (witness : TraceToSearchExtractionWitnessForProfile profile) :
    TraceToSearchSelectorTransferEvidence witness.tree :=
  witness.selectorTransfer

/-- Build S2055 search-premise inputs from an explicitly supplied tree together
with selector-transfer evidence. -/
def toSearchPremiseInputs
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (witness : TraceToSearchExtractionWitnessForProfile profile) :
    ThreeTwoPHPSearchPremiseInputsForProfile profile :=
  ThreeTwoPHPSearchPremiseInputsForProfile.ofEvalSelector
    profile witness.tree witness.selectorTransfer.evalSelector

/-- The input package constructed from an explicit witness preserves the supplied
candidate tree. -/
theorem toSearchPremiseInputs_tree
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (witness : TraceToSearchExtractionWitnessForProfile profile) :
    witness.toSearchPremiseInputs.tree = witness.tree :=
  rfl

/-- Conditional construction of the S2052 search premise from an explicitly
supplied witness contract. -/
def toSearchPremise
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (witness : TraceToSearchExtractionWitnessForProfile profile) :
    ThreeTwoPHPSearchPremiseForProfile profile :=
  witness.toSearchPremiseInputs.toSearchPremise

/-- Fixed finite depth consequence obtained only from the explicitly supplied
witness contract and its selector-transfer evidence. -/
theorem depthFloor
    {profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]}
    (witness : TraceToSearchExtractionWitnessForProfile profile) :
    2 <= queryDepth witness.tree := by
  simpa [toSearchPremiseInputs_tree witness] using
    ThreeTwoPHPSearchPremiseInputsForProfile.depthFloor witness.toSearchPremiseInputs

end TraceToSearchExtractionWitnessForProfile

/-- Supplied profile-compatibility evidence for the concrete `twoCyclePath3`
profiled route and a future extraction witness.  This evidence records only route
and profile pins plus existing budget pins; it does not construct extraction or
selector-transfer evidence. -/
structure TwoCyclePath3TraceToSearchProfileCompatibility
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute) : Prop where
  route_eq :
    route =
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute
  profile_eq :
    route.profile =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  profileBudgetPins : BDRefutationTraceProfileBudgetPins route.profile

/-- Route-level witness contract for future trace-to-search extraction over the
concrete `twoCyclePath3` profiled route.  It keeps profile compatibility separate
from the profile-level extraction witness. -/
structure TwoCyclePath3TraceToSearchExtractionWitnessContract
    (route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute) : Type where
  profileCompatibility : TwoCyclePath3TraceToSearchProfileCompatibility route
  extractionWitness : TraceToSearchExtractionWitnessForProfile route.profile

namespace TwoCyclePath3TraceToSearchExtractionWitnessContract

/-- Projection of supplied profile-compatibility evidence from an explicit
route-level witness contract. -/
theorem profileCompatibility_project
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (contract : TwoCyclePath3TraceToSearchExtractionWitnessContract route) :
    TwoCyclePath3TraceToSearchProfileCompatibility route :=
  contract.profileCompatibility

/-- Projection of the profile-level extraction witness from an explicit
route-level witness contract. -/
def extractionWitness_project
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (contract : TwoCyclePath3TraceToSearchExtractionWitnessContract route) :
    TraceToSearchExtractionWitnessForProfile route.profile :=
  contract.extractionWitness

/-- Conditional S2055 search-input package obtained only from an explicitly
supplied route-level witness contract. -/
def toSearchPremiseInputs
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (contract : TwoCyclePath3TraceToSearchExtractionWitnessContract route) :
    ThreeTwoPHPSearchPremiseInputsForProfile route.profile :=
  contract.extractionWitness.toSearchPremiseInputs

/-- Conditional S2052 search premise obtained only from an explicitly supplied
route-level witness contract. -/
def toSearchPremise
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (contract : TwoCyclePath3TraceToSearchExtractionWitnessContract route) :
    ThreeTwoPHPSearchPremiseForProfile route.profile :=
  contract.toSearchPremiseInputs.toSearchPremise

/-- Conditional route shell obtained only from explicit extraction-witness and
profile-compatibility evidence. -/
def routeShell
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (contract : TwoCyclePath3TraceToSearchExtractionWitnessContract route) :
    TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell where
  route := route
  route_eq := contract.profileCompatibility.route_eq
  searchPremise := contract.toSearchPremise

/-- Conditional route-boundary facts obtained only from explicit witness-contract
evidence. -/
theorem routeShell_boundaryFacts
    {route : TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute}
    (contract : TwoCyclePath3TraceToSearchExtractionWitnessContract route) :
    2 <= queryDepth (contract.routeShell.searchPremise.tree) /\
      contract.routeShell.route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation /\
      (Not (Exists fun a : CNFModel.Assignment 6 =>
        forall f,
          Membership.mem [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] f ->
            BoundedDepthFrege.eval a f = true)) /\
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation /\
      BDRefutationTraceProfileBudgetPins contract.routeShell.route.profile := by
  exact TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.boundaryFacts
    contract.routeShell

end TwoCyclePath3TraceToSearchExtractionWitnessContract

/-- Named future target for a concrete route-level extraction-witness contract.
This proposition is recorded only; it is not proved here. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget :
    Prop :=
  Nonempty
    (TwoCyclePath3TraceToSearchExtractionWitnessContract
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute)

/-! ## S2058 concrete selector/profile compatibility supplied-evidence layer -/

/-- Concrete selector-transfer evidence for the already-audited fixed finite
`3 x 2` PHP query tree.  This supplies only the S2047 evaluation theorem; it does
not extract the tree from a bounded-depth profile. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteSelectorTransferEvidence :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree where
  evalSelector := threeTwoPHPFalsifiedClauseQueryTree_evalSelector

/-- Concrete profile-compatibility evidence for the existing `twoCyclePath3`
profiled route.  This packages reflexive route/profile pins and existing budget
pins only. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteProfileCompatibility :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute where
  route_eq := rfl
  profile_eq := rfl
  profileBudgetPins :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins

/-- Given only an explicitly supplied extraction-relation premise for the concrete
profile/tree pair, package the S2057 profile-level witness shell. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileWitnessShell_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    TraceToSearchExtractionWitnessForProfile
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile where
  tree := threeTwoPHPFalsifiedClauseQueryTree
  extractionEvidence := extraction
  selectorTransfer :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteSelectorTransferEvidence

/-- Conditional concrete route-level contract shell obtained from an explicitly
supplied extraction-relation premise. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    TwoCyclePath3TraceToSearchExtractionWitnessContract
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute where
  profileCompatibility :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteProfileCompatibility
  extractionWitness :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileWitnessShell_of_suppliedConcreteExtractionRelation extraction

/-- The S2057 concrete witness-contract target follows only from a supplied
concrete extraction-relation premise. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget :=
  ⟨twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation
    extraction⟩

/-- Conditional S2055 search-premise inputs obtained from a supplied concrete
extraction-relation premise and the already-available concrete selector-transfer evidence. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    ThreeTwoPHPSearchPremiseInputsForProfile
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile :=
  (twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation
    extraction).toSearchPremiseInputs

/-- The conditional search-premise inputs preserve the concrete S2047 query tree. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_tree_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    (twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_of_suppliedConcreteExtractionRelation
      extraction).tree = threeTwoPHPFalsifiedClauseQueryTree :=
  rfl

/-- Conditional S2052 search premise obtained from a supplied concrete
extraction-relation premise. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremise_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    ThreeTwoPHPSearchPremiseForProfile
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile :=
  (twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation
    extraction).toSearchPremise

/-- Conditional route shell obtained from a supplied concrete extraction-relation
premise. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell :=
  (twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation
    extraction).routeShell

/-- Conditional route-boundary facts obtained from a supplied concrete
extraction-relation premise through the S2057 route-level witness contract. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_boundaryFacts_of_suppliedConcreteExtractionRelation
    (extraction :
      TraceToSearchExtractionRelation
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
        threeTwoPHPFalsifiedClauseQueryTree) :
    2 <= queryDepth
      ((twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation
        extraction).searchPremise.tree) /\
      (twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation
        extraction).route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation /\
      (Not (Exists fun a : CNFModel.Assignment 6 =>
        forall f,
          Membership.mem [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] f ->
            BoundedDepthFrege.eval a f = true)) /\
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation /\
      BDRefutationTraceProfileBudgetPins
        (twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation
          extraction).route.profile := by
  exact
    (twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation
      extraction).routeShell_boundaryFacts

/-! ## S2059 concrete extraction-relation obstruction map -/

/-- Exact concrete relation that S2059 attempts to obtain.  This is only the
named target proposition: after S2060, constructing it still requires the missing
constructor-field obligation. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget :
    Prop :=
  TraceToSearchExtractionRelation
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
    threeTwoPHPFalsifiedClauseQueryTree

/-- Metadata antecedent naming the single still-missing S2059 concrete extraction
relation.  The selector-transfer and profile-compatibility evidence are already
packaged separately by S2058. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 concrete trace-to-search extraction relation target"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction

/-- S2059 obstruction map for the concrete profile/tree pair.  It records the
already-supplied selector-transfer and profile-compatibility evidence next to the
one missing concrete extraction-relation target; it does not construct that
target. -/
structure TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap where
  concreteExtractionRelation : TraceToSearchLocalBridgeAntecedent
  selectorTransferEvidence :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree
  profileCompatibilityEvidence :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute
  concreteExtractionRelation_classification :
    concreteExtractionRelation.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction
  concreteExtractionRelation_target :
    concreteExtractionRelation.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget

/-- The remaining S2059 extraction obligation is exactly the map's named concrete
extraction-relation proposition. -/
def traceToSearchConcreteExtractionObstructionMap_remainingExtractionObligation
    (obstruction : TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap) :
    Prop :=
  obstruction.concreteExtractionRelation.proposition

/-- Projection of the remaining concrete extraction-relation proposition from an
explicit obstruction-map premise. -/
theorem traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation
    (obstruction : TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap) :
    traceToSearchConcreteExtractionObstructionMap_remainingExtractionObligation obstruction ->
      obstruction.concreteExtractionRelation.proposition := by
  intro h
  exact h

/-- Projection of the already-supplied selector-transfer evidence recorded in an
S2059 obstruction map. -/
theorem traceToSearchConcreteExtractionObstructionMap_selectorTransferEvidence
    (obstruction : TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap) :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree :=
  obstruction.selectorTransferEvidence

/-- Projection of the already-supplied profile-compatibility evidence recorded in
an S2059 obstruction map. -/
theorem traceToSearchConcreteExtractionObstructionMap_profileCompatibilityEvidence
    (obstruction : TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap) :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute :=
  obstruction.profileCompatibilityEvidence

/-- Projection of the missing-extraction classification from an S2059 obstruction
map. -/
theorem traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation_classification
    (obstruction : TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap) :
    obstruction.concreteExtractionRelation.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  obstruction.concreteExtractionRelation_classification

/-- Concrete S2059 obstruction map: selector-transfer and profile-compatibility
evidence are filled by S2058; the concrete extraction relation remains only a
named target proposition. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap :
    TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap where
  concreteExtractionRelation :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationAntecedent
  selectorTransferEvidence :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteSelectorTransferEvidence
  profileCompatibilityEvidence :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteProfileCompatibility
  concreteExtractionRelation_classification := rfl
  concreteExtractionRelation_target := rfl

/-- The concrete S2059 obstruction map leaves exactly the concrete
`TraceToSearchExtractionRelation` target as its remaining extraction obligation. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_remainingTarget :
    traceToSearchConcreteExtractionObstructionMap_remainingExtractionObligation
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap =
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget :=
  rfl

/-- Concrete projection showing that S2058 already supplied selector-transfer
evidence for the fixed query tree. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_selectorTransferEvidence :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree :=
  traceToSearchConcreteExtractionObstructionMap_selectorTransferEvidence
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap

/-- Concrete projection showing that S2058 already supplied profile-compatibility
evidence for the fixed profiled route. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_profileCompatibilityEvidence :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute :=
  traceToSearchConcreteExtractionObstructionMap_profileCompatibilityEvidence
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap

/-- Concrete projection showing that the remaining S2059 target is classified as
the missing trace-to-search extraction antecedent. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_classification :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap.concreteExtractionRelation.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation_classification
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap

/-! ## S2060 proof-bearing extraction-relation constructor-field refinement -/

/-- Exact constructor-field obligation for the S2059 concrete relation target.
This is the refined proof-bearing field still missing after S2060; it is not
constructed here. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget :
    Prop :=
  TraceToSearchExtractionConstructorFieldObligation
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
    threeTwoPHPFalsifiedClauseQueryTree

/-- Projection from the S2059 concrete relation target to the refined S2060
constructor-field obligation. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_constructorField
    (relation :
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget) :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget :=
  relation.constructorField

/-- Packaging from the refined constructor-field obligation back into the S2059
concrete relation target.  This does not construct the field. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_constructorField_to_concreteTraceToSearchExtractionRelationTarget
    (field :
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget) :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget :=
  TraceToSearchExtractionRelation.ofConstructorField field

/-- The S2059 concrete relation target is equivalent to the S2060 refined
constructor-field obligation.  The equivalence packages or projects evidence
only; it proves neither side. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_iff_constructorFieldTarget :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget ↔
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget := by
  constructor
  · exact
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_constructorField
  · exact
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_constructorField_to_concreteTraceToSearchExtractionRelationTarget

/-- Metadata antecedent for the exact constructor-field obligation isolated by
S2060. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 concrete trace-to-search extraction constructor-field target"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction

/-- S2060 obstruction map for the refined constructor-field target.  S2061
decomposes that target below; this map remains the historical S2060 pointer to
the relation constructor's required field. -/
structure TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldObstructionMap where
  constructorField : TraceToSearchLocalBridgeAntecedent
  constructorField_classification :
    constructorField.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction
  constructorField_target :
    constructorField.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget

/-- The remaining S2060 constructor-field obligation is exactly the map's named
constructor-field proposition. -/
def traceToSearchConcreteExtractionConstructorFieldObstructionMap_remainingConstructorFieldObligation
    (obstruction :
      TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldObstructionMap) :
    Prop :=
  obstruction.constructorField.proposition

/-- Projection of the missing-extraction classification from an S2060
constructor-field obstruction map. -/
theorem traceToSearchConcreteExtractionConstructorFieldObstructionMap_constructorField_classification
    (obstruction :
      TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldObstructionMap) :
    obstruction.constructorField.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  obstruction.constructorField_classification

/-- Concrete S2060 constructor-field obstruction map. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap :
    TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldObstructionMap where
  constructorField :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldAntecedent
  constructorField_classification := rfl
  constructorField_target := rfl

/-- The concrete S2060 obstruction map leaves exactly the refined constructor-field
target as its remaining obligation. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap_remainingTarget :
    traceToSearchConcreteExtractionConstructorFieldObstructionMap_remainingConstructorFieldObligation
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap =
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget :=
  rfl

/-- Concrete projection showing that the refined constructor-field target remains
classified as the missing trace-to-search extraction antecedent. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap_classification :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap.constructorField.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  traceToSearchConcreteExtractionConstructorFieldObstructionMap_constructorField_classification
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap

/-! ## S2061 semantic constructor-field decomposition -/

/-- Exact remaining local semantic bridge after the S2061 decomposition of the
concrete constructor-field target.  This target is not proved here. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :
    Prop :=
  TraceProfileToQueryExtractionBridgeObligation
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
    threeTwoPHPFalsifiedClauseQueryTree

/-- Projection from the concrete constructor-field target to the exact remaining
trace/profile-to-query bridge target. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_traceProfileToQueryBridge
    (field :
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget) :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :=
  field.traceProfileToQueryBridge

/-- Packaging from the exact remaining local bridge target into the concrete
constructor-field target.  The profile/tree pins, selector semantics, and budget
pins are the already-audited concrete facts; this does not prove the bridge. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceProfileToQueryBridge_to_concreteConstructorFieldTarget
    (bridge :
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget) :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget :=
  TraceToSearchExtractionConstructorFieldObligation.ofSemanticFields
    rfl
    rfl
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins
    threeTwoPHPFalsifiedClauseQueryTree_evalSelector
    bridge

/-- The concrete S2060 constructor-field target is equivalent to the exact S2061
trace/profile-to-query bridge target.  The equivalence packages or projects
evidence only; it proves neither side. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_iff_traceProfileToQueryBridgeTarget :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget ↔
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget := by
  constructor
  · exact
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_traceProfileToQueryBridge
  · exact
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceProfileToQueryBridge_to_concreteConstructorFieldTarget

/-- Metadata antecedent for the exact local bridge isolated by S2061. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeAntecedent :
    TraceToSearchLocalBridgeAntecedent where
  name := "twoCyclePath3 concrete trace/profile-to-query extraction bridge target"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget
  classification :=
    TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction

/-- S2061 semantic decomposition map for the concrete constructor field.  It
records the exact remaining bridge antecedent alongside the selector-transfer and
profile-compatibility evidence already supplied before S2061. -/
structure TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition where
  traceProfileToQueryBridge : TraceToSearchLocalBridgeAntecedent
  selectorTransferEvidence :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree
  profileCompatibilityEvidence :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute
  constructorField_iff_traceProfileToQueryBridge :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget ↔
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget
  traceProfileToQueryBridge_classification :
    traceProfileToQueryBridge.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction
  traceProfileToQueryBridge_target :
    traceProfileToQueryBridge.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget

/-- The remaining S2061 semantic bridge obligation is exactly the map's named
trace/profile-to-query bridge proposition. -/
def traceToSearchConstructorFieldSemanticDecomposition_remainingTraceProfileToQueryBridge
    (decomposition :
      TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition) :
    Prop :=
  decomposition.traceProfileToQueryBridge.proposition

/-- Projection of the selector-transfer evidence recorded in an S2061 semantic
decomposition map. -/
theorem traceToSearchConstructorFieldSemanticDecomposition_selectorTransferEvidence
    (decomposition :
      TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition) :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree :=
  decomposition.selectorTransferEvidence

/-- Projection of the profile-compatibility evidence recorded in an S2061 semantic
decomposition map. -/
theorem traceToSearchConstructorFieldSemanticDecomposition_profileCompatibilityEvidence
    (decomposition :
      TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition) :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute :=
  decomposition.profileCompatibilityEvidence

/-- Projection of the missing-extraction classification from an S2061 semantic
decomposition map. -/
theorem traceToSearchConstructorFieldSemanticDecomposition_traceProfileToQueryBridge_classification
    (decomposition :
      TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition) :
    decomposition.traceProfileToQueryBridge.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  decomposition.traceProfileToQueryBridge_classification

/-- Concrete S2061 semantic decomposition map. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition :
    TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition where
  traceProfileToQueryBridge :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeAntecedent
  selectorTransferEvidence :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteSelectorTransferEvidence
  profileCompatibilityEvidence :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteProfileCompatibility
  constructorField_iff_traceProfileToQueryBridge :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_iff_traceProfileToQueryBridgeTarget
  traceProfileToQueryBridge_classification := rfl
  traceProfileToQueryBridge_target := rfl

/-- The concrete S2061 semantic decomposition leaves exactly the local
trace/profile-to-query bridge target as its remaining obligation. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_remainingTarget :
    traceToSearchConstructorFieldSemanticDecomposition_remainingTraceProfileToQueryBridge
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition =
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :=
  rfl

/-- Concrete projection showing that the S2061 remaining bridge target is still
classified as the missing trace-to-search extraction antecedent. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_classification :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition.traceProfileToQueryBridge.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  traceToSearchConstructorFieldSemanticDecomposition_traceProfileToQueryBridge_classification
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition

/-- Concrete projection showing that the S2061 semantic decomposition reuses the
already-supplied selector-transfer evidence for the fixed query tree. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_selectorTransferEvidence :
    TraceToSearchSelectorTransferEvidence threeTwoPHPFalsifiedClauseQueryTree :=
  traceToSearchConstructorFieldSemanticDecomposition_selectorTransferEvidence
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition

/-- Concrete projection showing that the S2061 semantic decomposition reuses the
already-supplied profile-compatibility evidence for the concrete profiled route. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_profileCompatibilityEvidence :
    TwoCyclePath3TraceToSearchProfileCompatibility
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute :=
  traceToSearchConstructorFieldSemanticDecomposition_profileCompatibilityEvidence
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition

/-! ## S2062 fixed concrete trace/profile-to-query bridge obstruction map -/

/-- Supplied finite semantic fields available for the fixed S2062 profile/tree
pair.  These fields record the concrete trace resource normalization, profile
budget pins and erasure, and the fixed query-tree selector theorem.  They do not
construct a trace/profile-to-query extraction bridge. -/
structure TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics : Prop where
  traceResourceNormalization :
    BDRefutationTraceResourceNormalization
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace
  profileBudgetPins :
    BDRefutationTraceProfileBudgetPins
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  profileErasesToSuppliedBDRefutation :
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile.erase =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation
  selectorEval :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      queryEval a threeTwoPHPFalsifiedClauseQueryTree =
        threeTwoPHPFalsifiedClauseSelector a

/-- Concrete supplied finite fields for the fixed S2062 profile/tree pair. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics :
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics where
  traceResourceNormalization :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_resourceNormalization
  profileBudgetPins :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins
  profileErasesToSuppliedBDRefutation := rfl
  selectorEval := threeTwoPHPFalsifiedClauseQueryTree_evalSelector

/-- S2062 obstruction map for the fixed concrete trace/profile-to-query bridge.
It records every currently available fixed finite semantic field next to the exact
remaining bridge antecedent isolated by S2061. -/
structure TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap where
  suppliedFiniteSemantics :
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics
  traceProfileToQueryBridge : TraceToSearchLocalBridgeAntecedent
  traceProfileToQueryBridge_classification :
    traceProfileToQueryBridge.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction
  traceProfileToQueryBridge_target :
    traceProfileToQueryBridge.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget

/-- The remaining S2062 obstruction is exactly the map's named bridge
proposition. -/
def traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation
    (obstruction :
      TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap) :
    Prop :=
  obstruction.traceProfileToQueryBridge.proposition

/-- Projection of the supplied finite semantics from an S2062 obstruction map. -/
theorem traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics
    (obstruction :
      TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap) :
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics :=
  obstruction.suppliedFiniteSemantics

/-- Projection of the missing-extraction classification from an S2062 obstruction
map. -/
theorem traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_traceProfileToQueryBridge_classification
    (obstruction :
      TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap) :
    obstruction.traceProfileToQueryBridge.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  obstruction.traceProfileToQueryBridge_classification

/-- Concrete S2062 semantic-field obstruction map. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap :
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap where
  suppliedFiniteSemantics :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics
  traceProfileToQueryBridge :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeAntecedent
  traceProfileToQueryBridge_classification := rfl
  traceProfileToQueryBridge_target := rfl

/-- The concrete S2062 obstruction map leaves exactly the S2061 bridge target as
its remaining obligation. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingTarget :
    traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap =
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :=
  rfl

/-- Concrete projection showing that S2062 has only supplied finite semantic
fields, not the trace/profile-to-query bridge. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics :
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics :=
  traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap

/-- Concrete projection showing that the S2062 remaining bridge target remains
classified as the missing trace-to-search extraction antecedent. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_classification :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap.traceProfileToQueryBridge.classification =
      TraceToSearchLocalBridgeAntecedentClass.missingTraceToSearchExtraction :=
  traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_traceProfileToQueryBridge_classification
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap

/-! ## S2063 trace/profile-to-query bridge requirement decomposition -/

/-- Classification labels for the post-S2062 trace/profile-to-query bridge
requirements.  These labels are bookkeeping only; they do not discharge any
requirement or prove the bridge. -/
inductive TraceProfileToQueryBridgeRequirementClass where
  | suppliedFiniteSemantics
  | remainingBridgeTarget
  | missingInstanceCompatibility
  | missingExtractionProcedure
  | missingResourcePreservation
  | missingFamilyGeneralization

/-- A named post-S2062 bridge requirement together with its classification.  The
proposition field is recorded, not proved, by this record. -/
structure TraceProfileToQueryBridgeRequirement where
  name : String
  proposition : Prop
  classification : TraceProfileToQueryBridgeRequirementClass

/-- The compatibility statement relating the supplied bounded-depth CNF/profile
instance to the fixed `3 x 2` PHP falsified-clause query instance.  Before S2065
this was a constructorless placeholder (named
`..._missingInstanceCompatibilityObligation`); it now states the actual
compatibility content: an injective variable embedding hitting exactly the six
named PHP variables, everywhere-falseness of the fixed CNF, and the
common-extension property.  Proved in the S2065 section below. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation :
    Prop where
  varEmbedding_injective : Function.Injective phpVarEmbedding
  embed00 : phpVarEmbedding 0 = threeTwoPHPVar00
  embed01 : phpVarEmbedding 1 = threeTwoPHPVar01
  embed10 : phpVarEmbedding 2 = threeTwoPHPVar10
  embed11 : phpVarEmbedding 3 = threeTwoPHPVar11
  embed20 : phpVarEmbedding 4 = threeTwoPHPVar20
  embed21 : phpVarEmbedding 5 = threeTwoPHPVar21
  cnfEverywhereFalse :
    forall b : CNFModel.Assignment 6,
      BoundedDepthFrege.eval b twoCyclePath3GeneratedBridgeWitness_cnfBDFormula =
        false
  commonExtension :
    forall a : CNFModel.Assignment (Nat.succ (3 * 2)),
      BoundedDepthFrege.eval (fun i => a (phpVarEmbedding i))
          twoCyclePath3GeneratedBridgeWitness_cnfBDFormula = false /\
        ThreeTwoPHPFalsifiedClause.Valid a
          (threeTwoPHPFalsifiedClauseSelector a)

/-- The procedure extracting a query/search object from a supplied bounded-depth
trace profile.  Before S2065 this was a constructorless placeholder (named
`..._missingExtractionProcedureObligation`); it now states the actual procedure
content for `extractQueryTree`, whose query schedule is seeded by the trace's
literal excluded-middle order.  Correctness is order-independent at this fixed
instance (the fixed `3 x 2` search problem is total), so the logical dependence
of correctness on the trace is nil; this is disclosed, not hidden.  Proved in
the S2065 section below. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation :
    Prop where
  extractedEvalSelector :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
      (a : CNFModel.Assignment (Nat.succ (3 * 2))),
      queryEval a (extractQueryTree profile) =
        threeTwoPHPFalsifiedClauseSelector a
  extractedMatchesFixedTree :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
      (a : CNFModel.Assignment (Nat.succ (3 * 2))),
      queryEval a (extractQueryTree profile) =
        queryEval a threeTwoPHPFalsifiedClauseQueryTree

/-- The preservation statement connecting bounded-depth trace/profile resources
to the extracted query/search resource accounting.  Before S2065 this was a
constructorless placeholder (named `..._missingResourcePreservationObligation`);
it now states the actual resource content: the extracted tree inherits the fixed
`3 x 2` search depth floor, the fixed tree queries all six PHP variables, and
the supplied profile carries its budget pins.  No field derives tree query
depth from trace budgets; the floor is a property of the fixed search problem,
not of the trace.  Proved in the S2065 section below. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation :
    Prop where
  extractedDepthFloor :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]),
      2 <= queryDepth (extractQueryTree profile)
  fixedTreeQueryDepth : queryDepth threeTwoPHPFalsifiedClauseQueryTree = 6
  profileBudgetPins :
    BDRefutationTraceProfileBudgetPins
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile

/-- The trace-family generalization statement for the fixed `twoCyclePath3`
formula.  Before S2065 this was a constructorless placeholder (named
`..._missingFamilyGeneralizationObligation`).  IMPORTANT SCOPE: "family" here
means the family of ALL bounded-depth refutation trace profiles of the ONE fixed
six-variable formula; generalization over formula families (for example PHP over
growing rectangles) is NOT stated, NOT implied, and NOT claimed.  Proved in the
S2065 section below. -/
structure twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation :
    Prop where
  traceFamilySearchCorrect :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
      (a : CNFModel.Assignment (Nat.succ (3 * 2))),
      ThreeTwoPHPFalsifiedClause.Valid a
        (queryEval a (extractQueryTree profile))
  traceFamilyDepthFloor :
    forall
      (profile :
        BDRefutationTraceProfile
          [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]),
      2 <= queryDepth (extractQueryTree profile)

/-- The supplied finite semantics from S2062 as a bridge requirement entry. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFiniteSemanticsBridgeRequirement :
    TraceProfileToQueryBridgeRequirement where
  name := "twoCyclePath3 supplied finite trace/profile and query-tree semantics"
  proposition :=
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics
  classification :=
    TraceProfileToQueryBridgeRequirementClass.suppliedFiniteSemantics

/-- The exact remaining S2062 bridge target as a bridge requirement entry. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_remainingTraceProfileToQueryBridgeRequirement :
    TraceProfileToQueryBridgeRequirement where
  name := "twoCyclePath3 remaining trace/profile-to-query bridge target"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget
  classification :=
    TraceProfileToQueryBridgeRequirementClass.remainingBridgeTarget

/-- Missing instance-compatibility requirement entry for the concrete bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityBridgeRequirement :
    TraceProfileToQueryBridgeRequirement where
  name := "twoCyclePath3 missing CNF/profile to PHP-query instance compatibility"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation
  classification :=
    TraceProfileToQueryBridgeRequirementClass.missingInstanceCompatibility

/-- Missing extraction-procedure requirement entry for the concrete bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureBridgeRequirement :
    TraceProfileToQueryBridgeRequirement where
  name := "twoCyclePath3 missing trace/profile-to-query extraction procedure"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation
  classification :=
    TraceProfileToQueryBridgeRequirementClass.missingExtractionProcedure

/-- Missing resource-preservation requirement entry for the concrete bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationBridgeRequirement :
    TraceProfileToQueryBridgeRequirement where
  name := "twoCyclePath3 missing trace/profile-to-query resource preservation"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation
  classification :=
    TraceProfileToQueryBridgeRequirementClass.missingResourcePreservation

/-- Missing family-generalization requirement entry for the concrete bridge. -/
def twoCyclePath3TraceToThreeTwoPHPSearchPremise_familyGeneralizationBridgeRequirement :
    TraceProfileToQueryBridgeRequirement where
  name := "twoCyclePath3 missing family-level bridge generalization"
  proposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation
  classification :=
    TraceProfileToQueryBridgeRequirementClass.missingFamilyGeneralization

/-- S2063 decomposition of the S2062 bridge obstruction into the supplied finite
semantics, the exact remaining bridge target, and the four semantic requirements
missing from a real trace/profile-to-query extraction bridge.  This record is
metadata only and proves none of the missing requirements. -/
structure TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition where
  s2062ObstructionMap :
    TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap
  suppliedFiniteSemantics : TraceProfileToQueryBridgeRequirement
  remainingBridgeTarget : TraceProfileToQueryBridgeRequirement
  instanceCompatibility : TraceProfileToQueryBridgeRequirement
  extractionProcedure : TraceProfileToQueryBridgeRequirement
  resourcePreservation : TraceProfileToQueryBridgeRequirement
  familyGeneralization : TraceProfileToQueryBridgeRequirement
  s2062_remainingTarget :
    traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation
        s2062ObstructionMap =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget
  suppliedFiniteSemantics_classification :
    suppliedFiniteSemantics.classification =
      TraceProfileToQueryBridgeRequirementClass.suppliedFiniteSemantics
  remainingBridgeTarget_classification :
    remainingBridgeTarget.classification =
      TraceProfileToQueryBridgeRequirementClass.remainingBridgeTarget
  instanceCompatibility_classification :
    instanceCompatibility.classification =
      TraceProfileToQueryBridgeRequirementClass.missingInstanceCompatibility
  extractionProcedure_classification :
    extractionProcedure.classification =
      TraceProfileToQueryBridgeRequirementClass.missingExtractionProcedure
  resourcePreservation_classification :
    resourcePreservation.classification =
      TraceProfileToQueryBridgeRequirementClass.missingResourcePreservation
  familyGeneralization_classification :
    familyGeneralization.classification =
      TraceProfileToQueryBridgeRequirementClass.missingFamilyGeneralization
  suppliedFiniteSemantics_target :
    suppliedFiniteSemantics.proposition =
      TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics
  remainingBridgeTarget_target :
    remainingBridgeTarget.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget
  instanceCompatibility_target :
    instanceCompatibility.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation
  extractionProcedure_target :
    extractionProcedure.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation
  resourcePreservation_target :
    resourcePreservation.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation
  familyGeneralization_target :
    familyGeneralization.proposition =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation

/-- Conjoin the four missing semantic requirements isolated by S2063.  Supplying
this conjunction would still not by itself prove the bridge; it records only the
named missing fields. -/
def traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements
    (decomposition :
      TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition) :
    Prop :=
  decomposition.instanceCompatibility.proposition /\
    decomposition.extractionProcedure.proposition /\
      decomposition.resourcePreservation.proposition /\
        decomposition.familyGeneralization.proposition

/-- Projection of missing instance-compatibility from an S2063 requirements
conjunction. -/
theorem traceProfileToQueryBridgeRequirementsDecomposition_instanceCompatibility
    (decomposition :
      TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition) :
    traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements decomposition ->
      decomposition.instanceCompatibility.proposition := by
  intro h
  exact h.1

/-- Projection of missing extraction-procedure evidence from an S2063 requirements
conjunction. -/
theorem traceProfileToQueryBridgeRequirementsDecomposition_extractionProcedure
    (decomposition :
      TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition) :
    traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements decomposition ->
      decomposition.extractionProcedure.proposition := by
  intro h
  exact h.2.1

/-- Projection of missing resource-preservation evidence from an S2063 requirements
conjunction. -/
theorem traceProfileToQueryBridgeRequirementsDecomposition_resourcePreservation
    (decomposition :
      TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition) :
    traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements decomposition ->
      decomposition.resourcePreservation.proposition := by
  intro h
  exact h.2.2.1

/-- Projection of missing family-generalization evidence from an S2063 requirements
conjunction. -/
theorem traceProfileToQueryBridgeRequirementsDecomposition_familyGeneralization
    (decomposition :
      TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition) :
    traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements decomposition ->
      decomposition.familyGeneralization.proposition := by
  intro h
  exact h.2.2.2

/-- The S2063 requirements decomposition preserves the intended classification of
every entry. -/
theorem traceProfileToQueryBridgeRequirementsDecomposition_classifications
    (decomposition :
      TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition) :
    decomposition.suppliedFiniteSemantics.classification =
        TraceProfileToQueryBridgeRequirementClass.suppliedFiniteSemantics /\
      decomposition.remainingBridgeTarget.classification =
        TraceProfileToQueryBridgeRequirementClass.remainingBridgeTarget /\
      decomposition.instanceCompatibility.classification =
        TraceProfileToQueryBridgeRequirementClass.missingInstanceCompatibility /\
      decomposition.extractionProcedure.classification =
        TraceProfileToQueryBridgeRequirementClass.missingExtractionProcedure /\
      decomposition.resourcePreservation.classification =
        TraceProfileToQueryBridgeRequirementClass.missingResourcePreservation /\
      decomposition.familyGeneralization.classification =
        TraceProfileToQueryBridgeRequirementClass.missingFamilyGeneralization := by
  exact ⟨decomposition.suppliedFiniteSemantics_classification,
    decomposition.remainingBridgeTarget_classification,
    decomposition.instanceCompatibility_classification,
    decomposition.extractionProcedure_classification,
    decomposition.resourcePreservation_classification,
    decomposition.familyGeneralization_classification⟩

/-- Concrete S2063 requirement decomposition for the fixed `twoCyclePath3`
profile and fixed `3 x 2` PHP query tree. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition :
    TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition where
  s2062ObstructionMap :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap
  suppliedFiniteSemantics :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFiniteSemanticsBridgeRequirement
  remainingBridgeTarget :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_remainingTraceProfileToQueryBridgeRequirement
  instanceCompatibility :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityBridgeRequirement
  extractionProcedure :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureBridgeRequirement
  resourcePreservation :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationBridgeRequirement
  familyGeneralization :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_familyGeneralizationBridgeRequirement
  s2062_remainingTarget :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingTarget
  suppliedFiniteSemantics_classification := rfl
  remainingBridgeTarget_classification := rfl
  instanceCompatibility_classification := rfl
  extractionProcedure_classification := rfl
  resourcePreservation_classification := rfl
  familyGeneralization_classification := rfl
  suppliedFiniteSemantics_target := rfl
  remainingBridgeTarget_target := rfl
  instanceCompatibility_target := rfl
  extractionProcedure_target := rfl
  resourcePreservation_target := rfl
  familyGeneralization_target := rfl

/-- The concrete S2063 decomposition keeps the S2062 remaining bridge target
unchanged. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingBridgeTarget :
    traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.s2062ObstructionMap =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.s2062_remainingTarget

/-- The concrete S2063 decomposition records the intended classification of every
bridge-requirement entry. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_classifications :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.suppliedFiniteSemantics.classification =
        TraceProfileToQueryBridgeRequirementClass.suppliedFiniteSemantics /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.remainingBridgeTarget.classification =
        TraceProfileToQueryBridgeRequirementClass.remainingBridgeTarget /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.instanceCompatibility.classification =
        TraceProfileToQueryBridgeRequirementClass.missingInstanceCompatibility /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.extractionProcedure.classification =
        TraceProfileToQueryBridgeRequirementClass.missingExtractionProcedure /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.resourcePreservation.classification =
        TraceProfileToQueryBridgeRequirementClass.missingResourcePreservation /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition.familyGeneralization.classification =
        TraceProfileToQueryBridgeRequirementClass.missingFamilyGeneralization :=
  traceProfileToQueryBridgeRequirementsDecomposition_classifications
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition

/-- The concrete S2063 decomposition leaves exactly the four named semantic
requirements as missing requirements; it does not prove any of them. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements :
    traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition =
      (twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation /\
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation /\
          twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation /\
            twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation) :=
  rfl

/-! ## S2064 trace/profile-to-query bridge interface contract -/

/-- Required statement fields for a future trace/profile-to-query extraction
bridge over a fixed source profile and candidate query tree.  The fields are
propositions to be supplied by future work; this structure carries no proofs of
those propositions and performs no extraction. -/
structure TraceProfileToQueryBridgeInterfaceContractFields
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause) where
  instanceCompatibilityStatement : Prop
  extractionProcedureShapeStatement : Prop
  resourcePreservationStatement : Prop
  familyGeneralizationTargetStatement : Prop

/-- No-claims interface contract tying the S2063 missing-requirements
decomposition to the four statement fields a future real bridge would have to
provide.  The contract records field names and target propositions only; it does
not provide any of those propositions. -/
structure TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract where
  requirementsDecomposition :
    TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition
  profile :
    BDRefutationTraceProfile
      [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]
  tree : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause
  profile_eq :
    profile =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  tree_eq : tree = threeTwoPHPFalsifiedClauseQueryTree
  fields : TraceProfileToQueryBridgeInterfaceContractFields profile tree
  requirements_remainingTarget :
    traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation
        requirementsDecomposition.s2062ObstructionMap =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget
  instanceCompatibility_statement :
    fields.instanceCompatibilityStatement =
      requirementsDecomposition.instanceCompatibility.proposition
  extractionProcedureShape_statement :
    fields.extractionProcedureShapeStatement =
      requirementsDecomposition.extractionProcedure.proposition
  resourcePreservation_statement :
    fields.resourcePreservationStatement =
      requirementsDecomposition.resourcePreservation.proposition
  familyGeneralizationTarget_statement :
    fields.familyGeneralizationTargetStatement =
      requirementsDecomposition.familyGeneralization.proposition
  instanceCompatibility_target :
    fields.instanceCompatibilityStatement =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation
  extractionProcedureShape_target :
    fields.extractionProcedureShapeStatement =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation
  resourcePreservation_target :
    fields.resourcePreservationStatement =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation
  familyGeneralizationTarget_target :
    fields.familyGeneralizationTargetStatement =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation

/-- Conjoin the four statement fields required by the S2064 interface contract.
Supplying this proposition would still be only field evidence; S2064 does not
prove it or derive the bridge from it. -/
def traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements
    (contract : TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract) :
    Prop :=
  contract.fields.instanceCompatibilityStatement /\
    contract.fields.extractionProcedureShapeStatement /\
      contract.fields.resourcePreservationStatement /\
        contract.fields.familyGeneralizationTargetStatement

/-- Projection of the required instance-compatibility statement from an explicitly
supplied S2064 required-field conjunction. -/
theorem traceProfileToQueryBridgeInterfaceContract_instanceCompatibilityStatement
    (contract : TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract) :
    traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements contract ->
      contract.fields.instanceCompatibilityStatement := by
  intro h
  exact h.1

/-- Projection of the required extraction-procedure-shape statement from an
explicitly supplied S2064 required-field conjunction. -/
theorem traceProfileToQueryBridgeInterfaceContract_extractionProcedureShapeStatement
    (contract : TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract) :
    traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements contract ->
      contract.fields.extractionProcedureShapeStatement := by
  intro h
  exact h.2.1

/-- Projection of the required resource-preservation statement from an explicitly
supplied S2064 required-field conjunction. -/
theorem traceProfileToQueryBridgeInterfaceContract_resourcePreservationStatement
    (contract : TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract) :
    traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements contract ->
      contract.fields.resourcePreservationStatement := by
  intro h
  exact h.2.2.1

/-- Projection of the required family-generalization target statement from an
explicitly supplied S2064 required-field conjunction. -/
theorem traceProfileToQueryBridgeInterfaceContract_familyGeneralizationTargetStatement
    (contract : TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract) :
    traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements contract ->
      contract.fields.familyGeneralizationTargetStatement := by
  intro h
  exact h.2.2.2

/-- The S2064 interface contract preserves the S2063 missing-requirement
classifications for the four required fields. -/
theorem traceProfileToQueryBridgeInterfaceContract_requirementClassifications
    (contract : TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract) :
    contract.requirementsDecomposition.instanceCompatibility.classification =
        TraceProfileToQueryBridgeRequirementClass.missingInstanceCompatibility /\
      contract.requirementsDecomposition.extractionProcedure.classification =
        TraceProfileToQueryBridgeRequirementClass.missingExtractionProcedure /\
      contract.requirementsDecomposition.resourcePreservation.classification =
        TraceProfileToQueryBridgeRequirementClass.missingResourcePreservation /\
      contract.requirementsDecomposition.familyGeneralization.classification =
        TraceProfileToQueryBridgeRequirementClass.missingFamilyGeneralization := by
  exact And.intro contract.requirementsDecomposition.instanceCompatibility_classification
    (And.intro contract.requirementsDecomposition.extractionProcedure_classification
      (And.intro contract.requirementsDecomposition.resourcePreservation_classification
        contract.requirementsDecomposition.familyGeneralization_classification))

/-- Concrete S2064 no-claims interface contract for the fixed `twoCyclePath3`
profile and fixed `3 x 2` PHP query tree. -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract :
    TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract where
  requirementsDecomposition :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition
  profile :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  tree := threeTwoPHPFalsifiedClauseQueryTree
  profile_eq := rfl
  tree_eq := rfl
  fields :=
    { instanceCompatibilityStatement :=
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation
      extractionProcedureShapeStatement :=
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation
      resourcePreservationStatement :=
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation
      familyGeneralizationTargetStatement :=
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation }
  requirements_remainingTarget :=
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingBridgeTarget
  instanceCompatibility_statement := rfl
  extractionProcedureShape_statement := rfl
  resourcePreservation_statement := rfl
  familyGeneralizationTarget_statement := rfl
  instanceCompatibility_target := rfl
  extractionProcedureShape_target := rfl
  resourcePreservation_target := rfl
  familyGeneralizationTarget_target := rfl

/-- The concrete S2064 contract keeps the S2062 remaining bridge target unchanged. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_remainingBridgeTarget :
    traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract.requirementsDecomposition.s2062ObstructionMap =
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract.requirements_remainingTarget

/-- The concrete S2064 contract records exactly the four S2063 missing field
statements; it does not prove any of them. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements :
    traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract =
      (twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation /\
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation /\
          twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation /\
            twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation) :=
  rfl

/-- The concrete S2064 contract preserves the intended S2063 classification of
every required field. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requirementClassifications :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract.requirementsDecomposition.instanceCompatibility.classification =
        TraceProfileToQueryBridgeRequirementClass.missingInstanceCompatibility /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract.requirementsDecomposition.extractionProcedure.classification =
        TraceProfileToQueryBridgeRequirementClass.missingExtractionProcedure /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract.requirementsDecomposition.resourcePreservation.classification =
        TraceProfileToQueryBridgeRequirementClass.missingResourcePreservation /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract.requirementsDecomposition.familyGeneralization.classification =
        TraceProfileToQueryBridgeRequirementClass.missingFamilyGeneralization :=
  traceProfileToQueryBridgeInterfaceContract_requirementClassifications
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract

/-! ## S2065 proved concrete extraction bridge

This section proves the S2052-S2064 obligation content realized above, using the
extraction procedure and correctness theorems from
`PvNP.BDTraceToSearchExtraction`.

HONEST SCOPE: every theorem below is a finite concrete-instance statement about
the ONE fixed six-variable identically-false CNF and the ONE fixed `3 x 2` PHP
falsified-clause search problem.  None of them is a lower bound, a Frege/PHP
statement, or a P vs NP statement.  The S2054 route-obligation conjunction
(`traceToSearchRouteObligations_remainingRouteObligations`) is deliberately NOT
proved here: it contains
`twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation`,
which is the genuine open proof-complexity route and remains an empty non-claim.
-/

/-- The S2061 local bridge holds for EVERY trace profile of the fixed formula
against the fixed `3 x 2` query tree. -/
theorem traceProfileToQueryExtractionBridge_toFixedTree
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) :
    TraceProfileToQueryExtractionBridgeObligation profile
      threeTwoPHPFalsifiedClauseQueryTree where
  extractedEvalSelector := extractQueryTree_evalSelector profile
  extractedMatchesTree := extractQueryTree_matchesFixedTree profile
  extractedDepthFloor := extractQueryTree_depthFloor profile
  instanceCompatibility := twoCyclePath3ThreeTwoPHP_commonExtension

/-- **S2061/S2062 bridge target, proved** (under its S2065-redefined content).
The bridge target named by S2061-S2064 for the concrete profile/tree pair,
where the target Prop was a constructorless placeholder until S2065 gave it the
explicitly displayed content above; nothing was proved under the old
uninhabitable statement. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget :=
  traceProfileToQueryExtractionBridge_toFixedTree _

/-- **S2060 constructor-field target, proved**, via the existing S2061
packaging. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceProfileToQueryBridge_to_concreteConstructorFieldTarget
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget_proved

/-- **S2059 concrete extraction-relation target, proved**, via the existing
S2060 packaging. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremise_constructorField_to_concreteTraceToSearchExtractionRelationTarget
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget_proved

/-- **S2057 extraction witness contract target, proved unconditionally** (the
supplied-relation premise of the S2058 conditional theorem is now discharged). -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_of_suppliedConcreteExtractionRelation
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_proved

/-- The proved concrete route shell (no supplied-relation premise remains). -/
noncomputable def twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell :
    TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell :=
  twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_proved

/-- **Unconditional route-boundary facts** for the proved route shell.  The
depth floor is the existing fixed `3 x 2` search floor; the remaining
unresolved proof-complexity route equality is a pin to the untouched empty
non-claim, not a proof of it. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell_boundaryFacts :
    2 <= queryDepth
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell.searchPremise.tree /\
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell.route.profile.erase =
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation /\
      (Not (Exists fun a : CNFModel.Assignment 6 =>
        forall f,
          Membership.mem [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] f ->
            BoundedDepthFrege.eval a f = true)) /\
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation /\
      BDRefutationTraceProfileBudgetPins
        twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell.route.profile :=
  TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.boundaryFacts
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell

/-! ### S2054/S2055/S2056 obligations, proved -/

/-- The S2054/S2055 local future bridge route obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation where
  fixedTreeEvalSelector := threeTwoPHPFalsifiedClauseQueryTree_evalSelector
  extractedEvalSelector := extractQueryTree_evalSelector

/-- The exact S2055 explicit local future bridge target, proved: every route
pinned to the concrete profiled route carries local bridge evidence. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget := by
  intro route hroute
  exact ⟨{ route_eq := hroute
           premiseInputs :=
             ThreeTwoPHPSearchPremiseInputsForProfile.ofEvalSelector
               route.profile threeTwoPHPFalsifiedClauseQueryTree
               threeTwoPHPFalsifiedClauseQueryTree_evalSelector
           localBridgeObligation :=
             twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation_proved }⟩

/-- The S2056 trace-to-search extraction obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation where
  extractedEvalSelector := extractQueryTree_evalSelector

/-- The S2056 selector-transfer obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation where
  fixedTreeEvalSelector := threeTwoPHPFalsifiedClauseQueryTree_evalSelector
  extractedMatchesFixedTree := extractQueryTree_matchesFixedTree

/-- The S2056 profile-compatibility obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation where
  profileErasesToSuppliedBDRefutation := rfl
  profileBudgetPins :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins

/-- The supplied profiled route/resource facts proposition, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts :=
  ⟨rfl, rfl,
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins⟩

/-- The supplied fixed finite search-premise facts proposition, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts :=
  fun _profile P => ThreeTwoPHPSearchPremiseForProfile.depthFloor P

/-- The full S2056 local-bridge antecedent conjunction, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents_remainingAntecedents_proved :
    traceToSearchLocalBridgeAntecedents_remainingAntecedents
      twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents := by
  exact ⟨twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation_proved⟩

/-! ### S2063 requirement fields, proved -/

/-- The S2063 instance-compatibility obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation where
  varEmbedding_injective := phpVarEmbedding_injective
  embed00 := phpVarEmbedding_eq_var00
  embed01 := phpVarEmbedding_eq_var01
  embed10 := phpVarEmbedding_eq_var10
  embed11 := phpVarEmbedding_eq_var11
  embed20 := phpVarEmbedding_eq_var20
  embed21 := phpVarEmbedding_eq_var21
  cnfEverywhereFalse := twoCyclePath3_cnfBDFormula_eval_false
  commonExtension := twoCyclePath3ThreeTwoPHP_commonExtension

/-- The S2063 extraction-procedure obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation where
  extractedEvalSelector := extractQueryTree_evalSelector
  extractedMatchesFixedTree := extractQueryTree_matchesFixedTree

/-- The S2063 resource-preservation obligation, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation where
  extractedDepthFloor := extractQueryTree_depthFloor
  fixedTreeQueryDepth := fixedTree_queryDepth_eq_six
  profileBudgetPins :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins

/-- The S2063 trace-family generalization obligation, proved.  Trace-profile
family of the ONE fixed formula only; formula-family generalization is not
claimed. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation_proved :
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation where
  traceFamilySearchCorrect := extractQueryTree_searchCorrect
  traceFamilyDepthFloor := extractQueryTree_depthFloor

/-- The full S2063 missing-requirements conjunction, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements_proved :
    traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition := by
  rw [twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements]
  exact ⟨twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation_proved⟩

/-- The full S2064 required-field-statement conjunction, proved. -/
theorem twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements_proved :
    traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements
      twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract := by
  rw [twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements]
  exact ⟨twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation_proved,
    twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation_proved⟩

end BDTraceToSearchPremise
end PvNP
