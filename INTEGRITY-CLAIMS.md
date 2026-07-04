# Integrity & Claims Ledger

**Scope:** this document states what this repository proves and what it does not.
The audit surface is `lean/PvNP/Audit.lean`, which pins selected kernel axiom
profiles with `#guard_msgs`.

## Non-Claims

This repository does **not** establish or imply:

- `P != NP` or `P = NP`;
- an NP or circuit lower bound;
- a Frege/PHP lower bound;
- a proved PHP decision-tree floor beyond the Lean-checked records listed
  below, such as the tiny `1 × 1` restricted view, the bounded `2 × 1` and
  `3 × 2` and parameterized `p × h` falsified-clause search floors, and the
  satisfiable `p = h` evasiveness/partial-matching family floors;
- a positive Boolean decision-tree depth floor for the full `2 × 1` PHP formula
  (the formula is identically false, so a constant-false Boolean tree has depth
  `0`);
- any positive Boolean decision-tree depth floor for an unsatisfiable PHP formula
  merely from the bounded falsified-clause search floors;
- arbitrary AC0 collapse or arbitrary bounded-depth formula collapse;
- a general CNF switching lemma independent of the explicit dualization bridge;
- a proof-size or proof-depth lower bound for any proof system WITH CUT: the
  variable-coverage and trace-size floors concern only this repository's local
  cut-free bounded-depth Tait trace system and are linear in the number of PHP variables (the stated `(h+1)*h` / `2*h` variable-query floors);
- tightness of the parameterized `2*h` search floor beyond the fixed `3 x 2`
  instance (family tightness is informal only);
- any proof-complexity content of the S2065 extraction bridge at its fixed
  instance (the fixed search problem is total, so correctness there is
  order-independent; the genuine open route obligation
  `twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation`
  remains an explicitly uninhabited `Prop`);
- any strength, efficiency, or size/depth-optimality claim for the local
  cut-free system from its completeness theorem (completeness alone proves no
  hardness; the naive constructed refutations are exponential-size).
- a PHP switching lemma: no collapse-probability upper bound for restricted
  formulas over the matching-restriction space is stated or proved;
- a probability measure or expectation statement over restriction
  distributions (the matching-distribution layer proves exact finite
  counting identities and every-point floor transfer only, over the
  identity-matching subfamily);
- a positive Boolean decision-tree depth floor for any unsatisfiable PHP
  formula (`p > h`);
- a discharge of the full frozen-form B4 goal (single upfront depth-`d`
  layered view, an internally derived product-of-stages counting hypothesis
  `B(m, w, s, d)`, and a final global `t(d, s)` tree bound): the
  `FrozenProductSchedule` bridge derives `ValidFrom` only from an explicitly
  supplied product-bound family and supplied tree-budget facts; the start
  layer and numeric schedule remain supplied, no arbitrary AC0/layered
  decomposition is proved, and `GeneratedIteratedCollapse.openObligations`
  intentionally remains nonempty;
- satisfiability of the original consistent-route stage beats (full-space
  bad-set count against consistent-subspace cardinality) with nonempty gates
  at two or more stages — the disclosed satisfiability gap, closed only by
  re-basing on the refinement subspace — nor any
  merely-consistent-subspace-relative renormalized bad-set bound (the proved
  renormalized bound is refinement-subspace-relative) or closed-form
  cardinality for consistent subspaces over nonfree bases;
- an asymptotic family of renormalized multi-stage instances: one concrete
  finite depth-2 instance over `n = 306` with width BUDGET `1` at both stages
  ("nonempty-gate" means a nonempty gate LIST; realized stage-2 width `≥ 1` is
  not certified).
- automatic many-round collapse beyond what `autoIteratedCollapse` literally
  states: the pinned STATEMENT records only the stage bookkeeping lists (gate
  counts, budgets, star counts); the `nextLayer` re-viewing is a property of
  the constructed witness only, and the theorem must not be cited for the
  re-viewing property of an arbitrary witness;
- unsupplied or automatically synthesized product hypotheses for the scheduled
  route: `FrozenProductSchedule` proves only that an explicit
  `FrozenProductHypothesis` over a supplied `B` and `t` yields `ValidFrom` and
  preserves per-stage tree-budget facts; it does not synthesize `B` from an
  arbitrary formula family, derive a final global `t(d,s)` theorem, or close
  full frozen-form B4;
- realized-width claims for auto re-viewed gates: stated widths are BUDGET
  claims (generated trees may be constants), and after any `s = 1` stage the
  schedule's tail degenerates to width-budget-0 stages with near-free beats,
  so schedule length alone is not a strength measure;
- an asymptotic family for the scheduled route: the budget-3 demo is one
  concrete finite instance, and its "first counting-beat-backed stage budget
  `s > 2`" status is relative to the `GraphIndexedBridge` `s = 49`
  `GeneratedCNFLayerStage` record, which used a directly supplied good
  restriction for a constant leaf tree rather than a counting beat.

Note on naming: the Lean namespace `BoundedDepthFrege` names this repository's
bounded-depth formula and trace INFRASTRUCTURE; no lower bound for the
bounded-depth Frege proof system is proved here.

## Pinned Declarations

| Declaration | Axioms | Classification |
|---|---|---|
| `PvNP.SwitchingClose2.switchingLemmaTermSimple_proved` | `propext`, `Classical.choice`, `Quot.sound` | proven-standard |
| `PvNP.BoundedDepthFregeSwitchingBridge.bdDNF_switching_bridge` | `propext`, `Classical.choice`, `Quot.sound` | proven-standard |
| `PvNP.BoundedDepthLayerView.bdFormula_dnfView_switching_collapse` | `propext`, `Classical.choice`, `Quot.sound` | proven-standard |
| `PvNP.BoundedDepthLayerView.emptyDNFView_switching_collapse` | `propext`, `Classical.choice`, `Quot.sound` | proven-standard witness |
| `PvNP.BoundedDepthIteratedCollapse.twoLayerCollapse_exists_from_stagePremises` | `propext`, `Quot.sound` | proven-elementary |
| `PvNP.BoundedDepthIteratedCollapse.oneLitTwoLayerCollapse_example` | `propext`, `Quot.sound` | proven-elementary witness |
| `PvNP.BoundedDepthIteratedCollapse.dnfEval_cnfDualDNF` | `propext` | proven-elementary duality |
| `PvNP.BoundedDepthIteratedCollapse.simpleDNF_cnfDualDNF_of_simpleCNF` | `propext`, `Quot.sound` | proven-elementary duality |
| `PvNP.BoundedDepthIteratedCollapse.bdFormula_cnfView_dual_switching_collapse` | `propext`, `Classical.choice`, `Quot.sound` | proven-standard CNF-dual bridge |
| `PvNP.BoundedDepthIteratedCollapse.threeLayerCollapse_exists_from_stagePremises` | `propext`, `Quot.sound` | proven-elementary schedule certificate |
| `PvNP.BoundedDepthIteratedCollapse.oneLitThreeLayerCollapse_example_nonvacuous` | `propext`, `Quot.sound` | proven-elementary witness |
| `PvNP.BoundedDepthIteratedCollapse.kLayerCollapse_exists_from_schedule` | `propext`, `Quot.sound` | proven-elementary schedule certificate |
| `PvNP.BoundedDepthIteratedCollapse.oneLitKLayerSchedule3_nonempty` | `propext`, `Quot.sound` | proven-elementary witness |
| `PvNP.BoundedDepthIteratedCollapse.GeneratedDNFLayerStage` / `generatedDNFStage_exists` | `propext`, `Classical.choice`, `Quot.sound` | generated-stage theorem |
| `PvNP.BoundedDepthIteratedCollapse.GeneratedCNFLayerStage` / `generatedCNFStage_exists` | `propext`, `Classical.choice`, `Quot.sound` | generated-stage theorem |
| `PvNP.BoundedDepthIteratedCollapse.dnfPremiseOfGenerated` / `cnfPremiseOfGenerated` | (inherited) | conversion helpers |
| `PvNP.BoundedDepthIteratedCollapse.generatedTwoLayerCollapse_exists` | `propext`, `Classical.choice`, `Quot.sound` | generated-stage theorem |
| `PvNP.BoundedDepthIteratedCollapse.generatedThreeLayerCollapse_exists` | `propext`, `Classical.choice`, `Quot.sound` | generated-stage theorem |
| `PvNP.BoundedDepthIteratedCollapse.GeneratedExplicitLayerStage.toExplicit_depthBound_eq_stageS` | `propext`, `Classical.choice`, `Quot.sound` | generated-stage conversion helper |
| `PvNP.BoundedDepthIteratedCollapse.generatedKLayerCollapse_exists` | `propext`, `Classical.choice`, `Quot.sound` | generated k-layer schedule certificate |
| `PvNP.BoundedDepthIteratedCollapse.generatedNonemptyKLayerCollapse_exists` | `propext`, `Classical.choice`, `Quot.sound` | nonempty generated k-layer schedule certificate |
| `PvNP.BoundedDepthIteratedCollapse.emptyGeneratedKLayerSchedule3_nonempty` | `propext`, `Classical.choice`, `Quot.sound` | generated k-layer witness |
| `PvNP.BoundedDepthIteratedCollapse.emptyGeneratedKLayerSchedule4_nonempty` | `propext`, `Classical.choice`, `Quot.sound` | generated k-layer witness |
| `PvNP.CertifiedAffine.incidentExtractor_completeOn` | none | proven extractor interface |
| `PvNP.CertifiedAffine.incident_collision_endpoints` | none | proven collision-handling lemma |
| `PvNP.CertifiedAffine.certifiedAffineExtraction_completeOn` | none | proven extractor certificate connection |
| `PvNP.RestrictedPHPFloor.phpBoundary_formula_eq` | `propext`, `Quot.sound` | proven restricted-PHP boundary identity |
| `PvNP.RestrictedPHPFloor.eval_tinyOneOneRestrictedPHPFormula` | `propext`, `Quot.sound` | proven tiny restricted-PHP semantic witness |
| `PvNP.RestrictedPHPFloor.tinyOneOnePHPDepthFloor` | `propext`, `Quot.sound` | proven tiny bounded decision-tree floor |
| `PvNP.RestrictedPHPFloor.twoOnePHPFalsifiedClauseSearchDepthFloor` | `propext` | proven bounded `2 × 1` falsified-clause search floor |
| `PvNP.RestrictedPHPFloor.queryTree_depth_ge_two_of_two_unqueried_ambiguity` | `propext` | reusable bounded certificate-search ambiguity lemma |
| `PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor` | `propext` | proven bounded `3 × 2` falsified-clause search floor |
| `PvNP.RestrictedPHPFloor.queryTree_depth_ge_three_of_adversary` | `propext`, `Classical.choice`, `Quot.sound` | reusable generic adversary depth-3 floor lemma |
| `PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_three` | `propext`, `Classical.choice`, `Quot.sound` | proven bounded `3 × 2` search floor of three |
| `PvNP.PHPSearchFloor.queryTree_depth_floor_of_stateful_adversary` | `propext`, `Quot.sound` | reusable generic STATEFUL adversary floor lemma |
| `PvNP.PHPSearchFloor.phpFalsifiedClauseSearchDepthFloor` | `propext`, `Classical.choice`, `Quot.sound` | parameterized `p x h` search floor of `2*h` (family) |
| `PvNP.PHPSearchFloor.phpFalsifiedClause32_correctTree_exists` | `propext`, `Quot.sound` | non-vacuity witness at `3 x 2` |
| `PvNP.PHPSearchFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_four` | `propext`, `Classical.choice`, `Quot.sound` | bespoke `3 x 2` floor strengthened to four |
| `PvNP.PHPSearchFloorTightness.threeTwoPHPFalsifiedClauseSearch_optimal_depth_eq_four` | `propext`, `Classical.choice`, `Quot.sound` | formalized tightness at `3 x 2` (optimal = four) |
| `PvNP.BDVariableCoverage.bdProofTrace_sound_nonstandard` | `propext`, `Quot.sound` | non-standard-semantics soundness (proof device) |
| `PvNP.BDVariableCoverage.refutationTrace_queries_var` | `propext`, `Quot.sound` | variable-coverage theorem (local cut-free system) |
| `PvNP.PHPCNFCoverage.phpCNF32_traceSize_ge_six` | `propext`, `Quot.sound` | concrete `3 x 2` coverage trace-size floor |
| `PvNP.PHPFamilyCoverage.phpCNF_family_traceSize` | `propext`, `Classical.choice`, `Quot.sound` | growing-family coverage trace-size floor `(h+1)*h` |
| `PvNP.BDTaitCompleteness.bdTait_complete` | `propext`, `Classical.choice`, `Quot.sound` | completeness of the local cut-free Tait system |
| `PvNP.BDTaitCompleteness.phpCNF_family_unsat` | `propext`, `Classical.choice`, `Quot.sound` | `PHP(h+1,h)` unsatisfiability (finite pigeonhole) |
| `PvNP.BDTaitCompleteness.phpCNF_family_refutationTrace_nonempty` | `propext`, `Classical.choice`, `Quot.sound` | non-vacuity of the coverage-floor trace types |
| `PvNP.TraceSearchConnection.extractQueryTreeUnpadded_evalSelector` | `propext`, `Classical.choice`, `Quot.sound` | trace-dependent unpadded extraction correctness |
| `PvNP.PHPFamilyTraceSearchRoute.phpCNF_family_traceSize_ge_two_h_via_search` | `propext`, `Classical.choice`, `Quot.sound` | composed family route bound `2*h` via search floor |
| `PvNP.BDTraceToSearchExtraction.extractQueryTree_evalSelector` | `propext`, `Classical.choice`, `Quot.sound` | S2065 fixed-instance extraction correctness |

| `PvNP.PHPBooleanDepthFloor.fullPHPBoundary_depthFloor` | `propext`, `Classical.choice`, `Quot.sound` | proven family Boolean depth floor (satisfiable `p = h` evasiveness, empty restriction) |
| `PvNP.PHPRestrictedDepthFloor.matchingRestriction_depthFloor` | `propext`, `Classical.choice`, `Quot.sound` | proven per-restriction master floor (partial-matching class) |
| `PvNP.PHPRestrictedDepthFloor.matchingBoundary_depthFloor` | `propext`, `Classical.choice`, `Quot.sound` | proven two-parameter boundary family floor `(h - s) * h` |
| `PvNP.PHPMatchingDistribution.star_ratio` | `propext` | proven exact star-ratio counting identity |
| `PvNP.PHPMatchingDistribution.subsetSpace_depthFloor` | `propext`, `Classical.choice`, `Quot.sound` | proven probability-one floor transfer (identity-matching subset space) |
| `PvNP.GeneratedGoodRestriction.simultaneousCollapse_exists` | `propext`, `Classical.choice`, `Quot.sound` | proven B1/B2 generated simultaneous collapse (supplied counting beat) |
| `PvNP.GeneratedIteratedCollapse.openObligations_nonempty` | none | openness certificate (intentionally nonempty frozen-form obstruction map) |
| `PvNP.GeneratedOneStepDepthReduction.generatedOneStepDepthReduction_exists` | `propext`, `Classical.choice`, `Quot.sound` | proven B3 one-step generated depth reduction (supplied minimal layered view) |
| `PvNP.RestrictionComposition.restrictionsWithStars_card` | `propext`, `Classical.choice`, `Quot.sound` | proven closed-form full-star-space cardinality |
| `PvNP.RestrictionComposition.simultaneousCollapse_exists_consistent` | `propext`, `Classical.choice`, `Quot.sound` | proven consistent-subspace counting beat (supplied side conditions) |
| `PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse` | `propext`, `Classical.choice`, `Quot.sound` | proven B4 route certificate theorem (supplied per-stage side conditions) |
| `PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse_twoStage_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | degenerate (empty-gate) two-stage route-shape witness, not gate collapse |
| `PvNP.RefinedSubspace.refinesSubspace_card` | `propext`, `Classical.choice`, `Quot.sound` | proven refinement-subspace closed-form cardinality |
| `PvNP.GeneratedRefinedCollapse.badSetTerm_refines_card_le` | `propext`, `Classical.choice`, `Quot.sound` | proven renormalized (refinement-subspace-relative) bad-set bound |
| `PvNP.GeneratedRefinedCollapse.generatedRefinedIteratedCollapse` | `propext`, `Classical.choice`, `Quot.sound` | proven refined iterated-collapse certificate theorem (supplied per-stage side conditions) |
| `PvNP.RefinedTwoStageInstance.refinedTwoStage_nonemptyGates_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | proven width-budget-1 nonempty-gate-list two-stage instance (realized stage-2 width not certified) |
| `PvNP.TreePathViews.treeCNFView` | `propext`, `Quot.sound` | proven decision-tree CNF re-viewing (representation only) |
| `PvNP.AutoReviewedIteration.nextLayer_width` | `propext`, `Classical.choice`, `Quot.sound` | proven auto next-layer width-budget lemma |
| `PvNP.ScheduledAutoCollapse.autoIteratedCollapse` | `propext`, `Classical.choice`, `Quot.sound` | proven schedule-driven many-round certificate theorem (statement records bookkeeping lists; supplied arithmetic beats) |
| `PvNP.FrozenProductSchedule.productValidFrom_validFrom` | `propext` | proven product-bound-to-`ValidFrom` bridge |
| `PvNP.FrozenProductSchedule.autoIteratedCollapse_of_frozenProduct` | `propext`, `Classical.choice`, `Quot.sound` | proven frozen-product schedule synthesis theorem (supplied `B`/`t`; start layer and schedule still supplied) |
| `PvNP.FrozenProductSchedule.frozenProductSchedule_oneStage_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | tiny one-stage width-0 non-vacuity witness for the product-schedule interface |
| `PvNP.FrozenProductScheduleDemo.frozenProductSchedule_seventeenTwoStage_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | finite `n = 17` width-1/two-stage product-bound instantiation; second stage is width-budget-0 tail |
| `PvNP.ScheduledCollapseDemo.scheduledThreeStage_budget3_nonvacuous` | `propext`, `Classical.choice`, `Quot.sound` | proven concrete budget-3 scheduled instance (single finite demo) |

No declaration above depends on `sorryAx`.

**S2065 redefinition disclosure.** The S2052-S2064 interface-contract
"obligation" `Prop`s in `PvNP.BDTraceToSearchPremise` were deliberately
constructorless placeholders (uninhabitable, logically equivalent to `False`)
until S2065 gave them explicitly displayed content, which was then proved.
Nothing previously open was proved under its old statement.  The genuine open
proof-complexity route obligation remains an explicitly uninhabited `Prop`.

**Scope of the coverage/trace floors.** All variable-coverage and trace-size
floors (`BDVariableCoverage`, `PHPCNFCoverage`, `PHPFamilyCoverage`,
`TraceSearchConnection`, `PHPFamilyTraceSearchRoute`; the family statements
are for every `h > 0`) concern the LOCAL
cut-free bounded-depth Tait trace system defined in this repository and are
linear in the number of PHP variables (the stated `(h+1)*h` / `2*h` variable-query floors).  The parameterized `2*h` search floor is a
decision-tree bound for the falsified-clause SEARCH problem, vacuous for
`p <= h` (informal, not formalized; non-vacuity is witnessed at `3 x 2`), and
its family tightness is informal only.  Completeness (`bdTait_complete`) alone proves no hardness and
carries no size/depth optimality claim. The CNF-facing bridge dualizes simple
CNF views into simple DNF views and reuses the proved DNF switching bridge. The
two-layer, three-layer, and k-layer theorems are schedule-composition results
under explicit hypotheses; they are not arbitrary bounded-depth collapse
theorems.


**Scope of the v0.5.0 Gate A / Gate B additions.** The satisfiable-PHP depth
floors are elementary evasiveness/sensitivity results for the `p = h` Boolean
function and its partial-matching restrictions; the matching-distribution
layer is exact finite counting (no probability measure; identity-matching
subfamily only). The Gate B route theorems are certificate theorems whose
per-stage layered views and counting/arithmetic beats are SUPPLIED side
conditions (restrictions are counting-generated, never supplied); the
consistent-route satisfiability gap is disclosed and closed only for the
refinement route; `autoIteratedCollapse`'s pinned statement records only
stage gate counts, budgets, and star counts (the `nextLayer` re-viewing is a
property of the constructed witness); realized widths of automatically
re-viewed gates are budget claims; the exhibited instances are single finite
instances. The post-v0.5.0 `FrozenProductSchedule` bridge narrows the scheduled
route by deriving `ValidFrom` from a supplied product-bound family `B` plus
supplied `t(d,s)` tree-budget facts, with a tiny one-stage width-0 witness; it
also includes one explicit `n = 17` width-1/two-stage product-bound
instantiation whose second stage is the width-budget-0 tail.  It does not
synthesize `B` from arbitrary formulas, prove an asymptotic product-bound
family, or close full frozen-form B4.
The PHP switching lemma (Gate A rung 4) remains open.

## Re-Verification

```bash
lake env lean lean/PvNP/Audit.lean
```

Release-candidate audit helper:

```powershell
./scripts/audit-release.ps1
```
