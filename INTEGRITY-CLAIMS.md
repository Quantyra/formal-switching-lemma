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
- arbitrary raw-formula synthesis from all `BDFormula` syntax into full
  generated-collapse inputs: the formula-family synthesis covers only parent
  merges of embedded simple DNF/CNF children whose bottom-layer raw syntax is
  supplied, and `FormulaSyntacticDNF` gives a semantic DNF expansion for every
  raw formula only under a supplied simplicity proof for packaged `DNFView`
  use; neither is a decomposition of general depth-`d` formulas into efficient
  generated-collapse layers;
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
- a PHP switching lemma: beyond the depth-1 single-literal and
  single-conjunctive-term collapse bounds of `PHPFullMatchingCollapseBound`
  (made exact for the single-literal event in
  `PHPFullMatchingCollapseExact`) and the depth-1 multi-term DNF total-size
  union bound of `PHPFullMatchingDNFBound`, plus the deterministic restricted
  DNF canonical-tree skeleton of `PHPFullMatchingCanonicalDT`, plus the
  conservative optional-code bad-path count of
  `PHPFullMatchingBadPathEncoding`, plus the free-variable, row-level
  multiplicity, and conditional compressed-target scaffold of
  `PHPFullMatchingCompressedBadPathCount`,
  no collapse-probability upper bound for restricted formulas over the
  matching-restriction space is stated or proved — in particular no
  multi-term DNF bad-set bound beyond the depth-1 total-size union bound of
  `PHPFullMatchingDNFBound`, no constructed compressed matching-space bad-set
  encoding/counting theorem, and no geometric `(8w)^s`-style depth-`t`
  collapse-probability bound (term-count-independent) over matchings;
- a measure-theoretic probability measure, expectation, or
  with-high-probability theorem over restriction distributions.  The
  matching-distribution/probability layers prove exact finite counting,
  cross-multiplied event-probability equalities/inequalities, and
  every-point floor transfer only, over the identity-subset and
  square-permutation matching spaces; rectangular `p > h` injection spaces are
  not formalized;
- a positive Boolean decision-tree depth floor for any unsatisfiable PHP
  formula (`p > h`);
- a discharge of the full frozen-form B4 goal: supplied `FrozenDepthView`
  views now have checked global final-tree budget theorems for the fixed
  geometric schedule and for arbitrary nonempty ratio-regime schedules, and
  positive-depth raw formulas can be routed through the same ratio-regime
  interface after top-constructor synthesis.  The top synthesis is now audited
  as a one-step depth decrease for every exposed child, recursive frontiers have
  a checked raw-depth budget, and full-depth frontier members now have exact
  width-one-or-less bottom DNF gates.  Recursive frontier gate layers also
  carry explicit per-level count, width-budget, successor-count, and
  tree-budget profile facts, and the recursive global-schedule wrapper packages
  those synthesized frontier and terminal layers under one formula-local
  max-frontier `t_F` budget for the existing frozen-product schedule consumer.
  The recursive ratio-schedule wrapper also lets those layers consume supplied
  ratio-regime schedules, and named geometric schedules only under explicit
  entry-size inequalities.
  But no arbitrary `BDFormula`/AC0 depth-`d` decomposition or internally
  synthesized `B(m, w, s, d)` product hypothesis is proved.  The start view and
  geometric, ratio-regime, or product-beat entry hypotheses remain supplied or
  reduced to explicit numeric entry bounds, syntactically exposed by the
  bottom-layer class, conditionally available through syntactic DNF simplicity,
  satisfied by the truth-table fallback, available only at the terminal
  full-depth frontier, or local to the formula's max-frontier profile, and
  `GeneratedIteratedCollapse.openObligations` intentionally remains nonempty;
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
| `PvNP.PHPFullMatchingDistribution.card_fullMatchingSpace` | `propext`, `Classical.choice`, `Quot.sound` | proven exact cardinality for `subsetSpace h s x Equiv.Perm (Fin h)` |
| `PvNP.PHPFullMatchingDistribution.phpVar_star_ratio_full` | `propext`, `Classical.choice`, `Quot.sound` | proven full square-matching star-ratio counting identity |
| `PvNP.PHPFullMatchingDistribution.fullMatchingSpace_depthFloor` | `propext`, `Classical.choice`, `Quot.sound` | proven probability-one floor transfer (full square-permutation matching space) |
| `PvNP.PHPFullMatchingProbability.fullStarEvent_probability_eq` | `propext`, `Classical.choice`, `Quot.sound` | proven finite event-probability form of the full square star ratio |
| `PvNP.PHPFullMatchingProbability.fullStarEvent_probability_le` | `propext`, `Classical.choice`, `Quot.sound` | proven finite event-probability upper-bound wrapper for the full square star event |
| `PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_probability_one` | `propext`, `Classical.choice`, `Quot.sound` | proven probability-one finite event form of the square-PHP depth-floor obstruction |
| `PvNP.PHPFullMatchingCollapseBound.matchingCollapseBad_lit_probability_le` | `propext`, `Classical.choice`, `Quot.sound` | proven depth-1 single-literal collapse-probability upper bound `(h - s)/h` over the full square matching space (NOT a PHP switching lemma) |
| `PvNP.PHPFullMatchingCollapseBound.matchingCollapseBad_term_probability_le` | `propext`, `Classical.choice`, `Quot.sound` | proven depth-1 single-conjunctive-term union-bound collapse-probability upper bound `w*(h - s)/h` (weak, NOT the switching-lemma ratio regime) |
| `PvNP.PHPFullMatchingCollapseBound.matchingCollapseBad_lit_three_two_strict` | `propext`, `Classical.choice`, `Quot.sound` | proven strictly-below-one literal instance `1/3` at `h = 3`, `s = 2` over a nonempty space |
| `PvNP.PHPFullMatchingCollapseBound.matchingCollapseBad_term_three_two_strict` | `propext`, `Classical.choice`, `Quot.sound` | proven strictly-below-one width-2 term instance `2/3` at `h = 3`, `s = 2` over a nonempty space |
| `PvNP.PHPFullMatchingCollapseExact.matchingCollapseBad_lit_of_fullStarEvent` | `propext`, `Quot.sound` | proven converse containment: a free literal variable makes the point collapse-bad at depth 1 |
| `PvNP.PHPFullMatchingCollapseExact.matchingCollapseBad_lit_iff_fullStarEvent` | `propext`, `Quot.sound` | proven pointwise identity of the depth-1 single-literal collapse-bad event with the star event |
| `PvNP.PHPFullMatchingCollapseExact.matchingCollapseBad_lit_probability_eq` | `propext`, `Classical.choice`, `Quot.sound` | proven EXACT depth-1 single-literal collapse probability `(h - s)/h` (single-literal event only; NOT a PHP switching lemma) |
| `PvNP.PHPFullMatchingCollapseExact.matchingCollapseBad_lit_three_two_count_pos` | `propext`, `Classical.choice`, `Quot.sound` | proven positive bad-event count at `h = 3`, `s = 2` (realizability of the literal collapse-bad event) |
| `PvNP.PHPFullMatchingDNFBound.exists_fullStarEvent_of_matchingCollapseBad_dnf` | `propext`, `Quot.sound` | proven containment of the multi-term DNF depth-1 collapse-bad event in the union of the star events of all literal occurrences |
| `PvNP.PHPFullMatchingDNFBound.matchingCollapseBad_dnf_probability_le` | `propext`, `Classical.choice`, `Quot.sound` | proven depth-1 multi-term DNF union-bound collapse probability `\|tvs.join\|*(h - s)/h`, linear in TOTAL DNF size (weak, NOT the switching-lemma regime) |
| `PvNP.PHPFullMatchingDNFBound.matchingCollapseBad_nil_dnf_count` | `propext`, `Classical.choice`, `Quot.sound` | proven exactly empty bad event for the empty DNF (`.or []` is constantly false) |
| `PvNP.PHPFullMatchingDNFBound.matchingCollapseBad_dnf_three_two_strict` | `propext`, `Classical.choice`, `Quot.sound` | proven strictly-below-one two-term DNF instance `2/3` at `h = 3`, `s = 2` over a nonempty space |
| `PvNP.PHPFullMatchingCanonicalDT.eval_phpDNFFormula_eq_dnfEval` | `propext`, `Quot.sound` | proven semantic bridge from the PHP DNF formula syntax to the generic DNF semantics |
| `PvNP.PHPFullMatchingCanonicalDT.canonicalRestrictedDNFTree_correct` | `propext`, `Quot.sound` | proven deterministic restricted-DNF term-canonical decision tree computes the restricted PHP DNF under agreeing assignments |
| `PvNP.PHPFullMatchingCanonicalDT.treeVarsIn_canonicalRestrictedDNFTree` | `propext`, `Classical.choice`, `Quot.sound` | proven every decision-node variable queried by the restricted canonical tree is among the original PHP DNF variables |
| `PvNP.PHPFullMatchingCanonicalDT.canonicalRestrictedDNFTree_depth_le_total` | `propext`, `Quot.sound` | proven deterministic worst-case depth bound by total literal occurrences `tvs.join.length` (not probabilistic) |
| `PvNP.PHPFullMatchingCanonicalDT.canonicalRestrictedDNFTree_path_length_le_total` | `propext`, `Quot.sound` | proven every assignment path has at most `tvs.join.length` queries |
| `PvNP.PHPFullMatchingBadPathEncoding.deepestPath_treeVarsIn` | `propext`, `Quot.sound` | proven deepest-path query variables stay inside any supplied tree support set |
| `PvNP.PHPFullMatchingBadPathEncoding.canonicalDepthBad_pathCode_exists` | `propext`, `Classical.choice`, `Quot.sound` | proven every depth-`t` bad matching point has a certified path code over the original PHP DNF variable set |
| `PvNP.PHPFullMatchingBadPathEncoding.canonicalDepthBadEncoding_injective_on` | `propext`, `Classical.choice`, `Quot.sound` | proven conservative bad-point encoder is injective on the filtered full matching space because it retains the original matching point |
| `PvNP.PHPFullMatchingBadPathEncoding.canonicalDepthBad_count_le_space_mul_optional_pathCode` | `propext`, `Classical.choice`, `Quot.sound` | proven first finite bad-path count over `fullMatchingSpace`, bounded by space size times optional path-code count (not geometric/compressed) |
| `PvNP.PHPFullMatchingCompressedBadPathCount.termRestrict_mem_free` | `propext` | proven every surviving restricted-term literal has a free variable under the restriction |
| `PvNP.PHPFullMatchingCompressedBadPathCount.dnfVarsIn_dnfRestrict_free` | `propext`, `Classical.choice`, `Quot.sound` | proven every variable in a restricted DNF is free under the restriction |
| `PvNP.PHPFullMatchingCompressedBadPathCount.treeVarsIn_free_canonicalRestrictedDNFTree` | `propext`, `Classical.choice`, `Quot.sound` | proven every restricted canonical PHP DNF tree query is free under `fullRestrictionOf P` |
| `PvNP.PHPFullMatchingCompressedBadPathCount.deepestPath_canonicalRestrictedDNFTree_free` | `propext`, `Classical.choice`, `Quot.sound` | proven every deepest-path query in the restricted canonical PHP DNF tree is free under `fullRestrictionOf P` |
| `PvNP.PHPFullMatchingCompressedBadPathCount.canonicalDepthBad_freePathCode_exists` | `propext`, `Classical.choice`, `Quot.sound` | proven every depth-`t` bad matching point has a `P`-dependent path code certified free under `fullRestrictionOf P` |
| `PvNP.PHPFullMatchingCompressedBadPathCount.canonicalDepthBad_count_le_target_mul_pathCode_of_injOn` | `propext`, `Classical.choice`, `Quot.sound` | conditional scaffold: any future compressed-target injection paired with `BadPathCode` gives the corresponding finite bad-event count bound; no encoder or fiber bound is constructed here |
| `PvNP.PHPFullMatchingCompressedBadPathCount.fullRowsFree_count` | `propext`, `Classical.choice`, `Quot.sound` | exact count of full matching points that leave a specified row set free; row-level multiplicity scaffold only, not a path-code fiber theorem |
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
| `PvNP.FormulaFamilyCollapse.formulaFamilyCollapse` | `propext`, `Classical.choice`, `Quot.sound` | proven parent-merged embedded-DNF family theorem (bottom-layer synthesis only) |
| `PvNP.MixedFormulaFamilyCollapse.mixedFormulaFamilyCollapse` | `propext`, `Classical.choice`, `Quot.sound` | proven parent-merged mixed embedded-DNF/CNF family theorem (full `GateSpec` constructor synthesis from raw bottom syntax only) |
| `PvNP.MixedFormulaFamilyCollapse.cnfFormulaFamilyCollapse` | `propext`, `Classical.choice`, `Quot.sound` | proven all-CNF child corollary via constructed `GateSpec.cnf` views |
| `PvNP.MixedFormulaFamilyCollapse.mixedFamily_dnfCnf_twoStage` | `propext`, `Classical.choice`, `Quot.sound` | finite mixed DNF/CNF witness exercising both `GateSpec` constructors |
| `PvNP.FrozenDepthView.geometricSchedule_frozenGlobalTreeBudget` | `propext`, `Quot.sound` | proven geometric-schedule budget fact for `t(d,s)=gateCount*(s-1)` |
| `PvNP.FrozenDepthView.lastStage_gateCount_of_stageGateCounts_replicate` | `propext`, `Classical.choice`, `Quot.sound` | proven final-stage gate-count helper for constant generated-stage bookkeeping |
| `PvNP.FrozenDepthView.frozenDepthView_geometricCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven supplied-`FrozenDepthView` consumer with actual final-tree global budget |
| `PvNP.FrozenDepthView.mixedBottomFrozenDepthView_geometricCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven mixed raw DNF/CNF bottom-layer class routed through the depth-view interface |
| `PvNP.FormulaStructuralSchedule.constantGateTreeBudget` | `propext` | proven schedule-independent constant gate-count budget fact |
| `PvNP.FormulaStructuralSchedule.schedule_frozenGlobalTreeBudget` | `propext`, `Quot.sound` | proven supplied-view budget fact for arbitrary schedules |
| `PvNP.FormulaStructuralSchedule.frozenDepthView_ratioRegimeCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven supplied-`FrozenDepthView` ratio-regime consumer with actual final-tree global budget |
| `PvNP.FormulaStructuralSchedule.positiveDepthFrozenDepthView_width_of_children` | `propext`, `Quot.sound` | proven child-width transfer for positive-depth raw-formula synthesized views |
| `PvNP.FormulaStructuralSchedule.positiveDepthFormula_ratioRegimeCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven positive-depth raw-formula ratio-regime consumer with global last-tree budget |
| `PvNP.FormulaDepthDecomposition.mem_le_foldr_max` | `propext` | proven public list-max membership helper for depth peeling |
| `PvNP.FormulaDepthDecomposition.child_depth_le_foldr_depths` | `propext`, `Quot.sound` | proven child-depth bound against the top formula depth aggregate |
| `PvNP.FormulaDepthDecomposition.topChildren_depth_lt` | `propext`, `Quot.sound` | proven exposed top children are strictly shallower than the raw formula |
| `PvNP.FormulaDepthDecomposition.topChildren_depth_le_pred` | `propext`, `Quot.sound` | proven predecessor-budget form of the top-child depth decrease |
| `PvNP.FormulaDepthDecomposition.positiveDepthFrozenDepthView_gate_formula_depth_lt` | `propext`, `Quot.sound` | proven synthesized positive-depth frozen-view gate formulas are strictly shallower |
| `PvNP.FormulaDepthDecomposition.positiveDepthFrozenDepthView_gate_formula_depth_le_pred` | `propext`, `Quot.sound` | proven predecessor-budget form for synthesized-view gate formulas |
| `PvNP.FormulaDepthDecomposition.PositiveDepthPeel` | `propext`, `Quot.sound` | audited one-step positive-depth peel package |
| `PvNP.FormulaDepthDecomposition.positiveDepthPeel` | `propext`, `Quot.sound` | constructed positive-depth peel from raw syntax |
| `PvNP.FormulaDepthDecomposition.positiveDepthPeel_gateCount` | `propext`, `Quot.sound` | proven peel gate count equals detected top child count |
| `PvNP.FormulaDepthDecomposition.positiveDepthPeel_gateFormulaDepth_le_pred` | `propext`, `Quot.sound` | proven packaged peel gate formulas satisfy the predecessor depth budget |
| `PvNP.FormulaRecursiveDepth.depthFrontier` | none | axiom-free repeated top-child frontier definition |
| `PvNP.FormulaRecursiveDepth.formulaDepthFrontier` | none | axiom-free single-root frontier definition |
| `PvNP.FormulaRecursiveDepth.depthFrontier_depth_add_le` | `propext`, `Quot.sound` | proven multi-root recursive frontier raw-depth budget |
| `PvNP.FormulaRecursiveDepth.formulaDepthFrontier_depth_add_le` | `propext`, `Quot.sound` | proven single-root recursive frontier raw-depth budget |
| `PvNP.FormulaRecursiveDepth.formulaDepthFrontier_depth_le_sub` | `propext`, `Quot.sound` | proven subtraction form of the recursive frontier depth budget |
| `PvNP.FormulaRecursiveDepth.formulaDepthFrontier_member_level_le_depth` | `propext`, `Quot.sound` | proven nonempty frontier level cannot exceed root depth |
| `PvNP.FormulaRecursiveDepth.formulaDepthFrontier_fullDepth_zero` | `propext`, `Quot.sound` | proven full-depth frontier members have raw formula depth zero |
| `PvNP.FormulaRecursiveDepth.RecursiveDepthFrontier` | `propext`, `Quot.sound` | audited packaged recursive frontier surface |
| `PvNP.FormulaRecursiveDepth.recursiveDepthFrontier` | `propext`, `Quot.sound` | constructed packaged recursive frontier from raw syntax |
| `PvNP.FormulaRecursiveDepth.recursiveDepthFrontier_depth_add_le` | `propext`, `Quot.sound` | proven packaged recursive frontier raw-depth budget |
| `PvNP.FormulaRecursiveDepth.recursiveDepthFrontier_fullDepth_zero` | `propext`, `Quot.sound` | proven packaged full-depth frontier members have raw formula depth zero |
| `PvNP.FormulaDepthZeroBottom.trueDNF` | none | axiom-free constant-true DNF definition |
| `PvNP.FormulaDepthZeroBottom.falseDNF` | none | axiom-free constant-false DNF definition |
| `PvNP.FormulaDepthZeroBottom.literalDNF` | none | axiom-free singleton-literal DNF definition |
| `PvNP.FormulaDepthZeroBottom.trueDNF_simple` | `propext` | proven simplicity of the constant-true DNF |
| `PvNP.FormulaDepthZeroBottom.falseDNF_simple` | `propext` | proven simplicity of the constant-false DNF |
| `PvNP.FormulaDepthZeroBottom.literalDNF_simple` | `propext` | proven simplicity of singleton-literal DNFs |
| `PvNP.FormulaDepthZeroBottom.widthDNF_trueDNF` | `propext` | proven width of the constant-true DNF |
| `PvNP.FormulaDepthZeroBottom.widthDNF_falseDNF` | `propext` | proven width of the constant-false DNF |
| `PvNP.FormulaDepthZeroBottom.widthDNF_literalDNF` | `propext` | proven width of singleton-literal DNFs |
| `PvNP.FormulaDepthZeroBottom.trueFormulaDNFView` | `propext`, `Quot.sound` | exact DNF view for the true formula |
| `PvNP.FormulaDepthZeroBottom.falseFormulaDNFView` | `propext`, `Quot.sound` | exact DNF view for the false formula |
| `PvNP.FormulaDepthZeroBottom.literalFormulaDNFView` | `propext`, `Quot.sound` | exact DNF view for literal formulas |
| `PvNP.FormulaDepthZeroBottom.depthZeroFormula_cases` | `propext`, `Quot.sound` | proven depth-zero formula classification into constants/literals |
| `PvNP.FormulaDepthZeroBottom.depthZeroFormulaDNFView` | `propext`, `Quot.sound` | constructed exact DNF view from a depth-zero proof |
| `PvNP.FormulaDepthZeroBottom.depthZeroFormulaGate` | `propext`, `Quot.sound` | constructed `GateSpec.dnf` for depth-zero formulas |
| `PvNP.FormulaDepthZeroBottom.depthZeroFormulaGate_formula` | `propext`, `Quot.sound` | proven depth-zero gate formula identity |
| `PvNP.FormulaDepthZeroBottom.depthZeroFormulaGate_width_le_one` | `propext`, `Quot.sound` | proven depth-zero gate switching DNF width at most one |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierFormulaGate` | `propext`, `Quot.sound` | constructed width-one-or-less bottom gate for full-depth frontier members |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierFormulaGate_formula` | `propext`, `Quot.sound` | proven full-depth frontier bottom gate formula identity |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierFormulaGate_width_le_one` | `propext`, `Quot.sound` | proven full-depth frontier bottom gate width at most one |
| `PvNP.FormulaDepthZeroBottom.FullDepthFrontierBottomGate` | `propext`, `Quot.sound` | audited packaged full-depth frontier bottom-gate witness |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierBottomGate` | `propext`, `Quot.sound` | constructed packaged full-depth frontier bottom-gate witness |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierGateList` | `propext`, `Quot.sound` | constructed bottom-gate list for the full-depth frontier |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierGateList_length` | `propext`, `Quot.sound` | proven full-depth frontier bottom-gate list length |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierGateList_formulas` | `propext`, `Quot.sound` | proven full-depth frontier bottom-gate formulas match the frontier |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierGateList_width_le_one` | `propext`, `Quot.sound` | proven every full-depth frontier bottom-layer gate has width at most one |
| `PvNP.FormulaDepthZeroBottom.FullDepthFrontierBottomLayer` | `propext`, `Quot.sound` | audited packaged full-depth frontier bottom-layer witness |
| `PvNP.FormulaDepthZeroBottom.fullDepthFrontierBottomLayer` | `propext`, `Quot.sound` | constructed packaged full-depth frontier bottom-layer witness |
| `PvNP.FormulaRecursiveDecomposition.depthFrontier_succ_eq_bind_topChildren` | none | axiom-free recursive frontier transition for root lists |
| `PvNP.FormulaRecursiveDecomposition.formulaDepthFrontier_succ_eq_bind_topChildren` | none | axiom-free recursive frontier transition for a single root |
| `PvNP.FormulaRecursiveDecomposition.FullDepthRecursiveDecomposition` | `propext`, `Quot.sound` | audited packaged full-depth recursive decomposition skeleton |
| `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition` | `propext`, `Quot.sound` | constructed full-depth recursive decomposition skeleton from raw syntax |
| `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition_transition` | `propext`, `Quot.sound` | proven packaged frontier level transition |
| `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition_depthBudget` | `propext`, `Quot.sound` | proven packaged raw-depth budget at every frontier level |
| `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition_terminal_formulas` | `propext`, `Quot.sound` | proven packaged terminal bottom-layer formulas match the full-depth frontier |
| `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition_terminal_width` | `propext`, `Quot.sound` | proven packaged terminal bottom-layer widths are at most one |
| `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition_terminal_count` | `propext`, `Quot.sound` | proven packaged terminal bottom-layer count matches the full-depth frontier |
| `PvNP.FormulaRecursiveGateLayers.frontierGateList` | `propext`, `Quot.sound` | constructed truth-table `GateSpec.dnf` list for any recursive frontier level |
| `PvNP.FormulaRecursiveGateLayers.frontierGateList_length` | `propext`, `Quot.sound` | proven frontier gate-list length matches the frontier |
| `PvNP.FormulaRecursiveGateLayers.frontierGateList_formulas` | `propext`, `Quot.sound` | proven frontier gate-list formulas match the frontier |
| `PvNP.FormulaRecursiveGateLayers.frontierGateList_width_le_vars` | `propext`, `Quot.sound` | proven frontier gate-list widths are bounded by the variable count |
| `PvNP.FormulaRecursiveGateLayers.RecursiveFrontierGateLayer` | `propext`, `Quot.sound` | audited packaged frontier gate layer with truth-table width bound |
| `PvNP.FormulaRecursiveGateLayers.recursiveFrontierGateLayer` | `propext`, `Quot.sound` | constructed packaged frontier gate layer |
| `PvNP.FormulaRecursiveGateLayers.FullDepthRecursiveGateLayers` | `propext`, `Quot.sound` | audited packaged all-level recursive frontier gate-layer surface |
| `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers` | `propext`, `Quot.sound` | constructed all-level recursive frontier gate-layer package |
| `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers_transition` | `propext`, `Quot.sound` | proven packaged gate-layer formula transition |
| `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers_depthBudget` | `propext`, `Quot.sound` | proven packaged gate-layer raw-depth budget |
| `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers_level_width_le_vars` | `propext`, `Quot.sound` | proven packaged intermediate frontier layer widths are bounded by the variable count |
| `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers_terminal_formulas` | `propext`, `Quot.sound` | proven packaged terminal bottom-layer formulas match the terminal frontier gate layer |
| `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers_terminal_width` | `propext`, `Quot.sound` | proven packaged terminal bottom-layer widths are at most one |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount` | `propext`, `Quot.sound` | defined per-frontier gate count for recursive gate layers |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount_eq_formulaDepthFrontier_length` | `propext`, `Quot.sound` | proven layer gate count agrees with raw frontier length |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount_zero` | `propext`, `Quot.sound` | proven level-zero gate count is one |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount_succ_eq_layer_bind_topChildren_length` | `propext`, `Quot.sound` | proven successor layer count is the prior layer's top-child bind length |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount_succ_eq_frontier_bind_topChildren_length` | `propext`, `Quot.sound` | proven successor count in raw-frontier bind form |
| `PvNP.FormulaRecursiveLayerProfile.length_bind_topChildren_eq_sum_topChildCount` | `propext` | proven top-child bind length equals the sum of top-child counts |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount_succ_eq_layer_topChildCount_sum` | `propext`, `Quot.sound` | proven successor layer count equals summed top-child counts over the prior gate layer |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount_succ_eq_frontier_topChildCount_sum` | `propext`, `Quot.sound` | proven successor layer count equals summed top-child counts over the raw frontier |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerWidthBudget` | none | axiom-free honest intermediate width-budget definition |
| `PvNP.FormulaRecursiveLayerProfile.terminalLayerWidthBudget` | none | axiom-free terminal width-budget definition |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayer_width_le_budget` | `propext`, `Quot.sound` | proven intermediate frontier layers obey the honest variable-count width budget |
| `PvNP.FormulaRecursiveLayerProfile.terminalLayer_width_le_budget` | `propext`, `Quot.sound` | proven terminal bottom layer obeys the width-one budget |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayerTreeBudget` | `propext`, `Quot.sound` | defined per-layer constant tree-budget profile |
| `PvNP.FormulaRecursiveLayerProfile.frontierLayer_treeBudgetFrom` | `propext`, `Quot.sound` | proven per-layer constant tree-budget profile satisfies every numeric schedule |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayerMinimalLayer` | `propext`, `Quot.sound` | constructed schedule-input layer from any recursive frontier |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayerMinimalLayer_originalFormula` | `propext`, `Quot.sound` | proven frontier schedule-input formula is the chosen parent over the recursive frontier |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayerMinimalLayer_gateCount` | `propext`, `Quot.sound` | proven frontier schedule-input gate count matches the recursive profile |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayerMinimalLayer_width_le_budget` | `propext`, `Quot.sound` | proven frontier schedule-input gates obey the honest intermediate width budget |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayerMinimalLayer_formula_depth_add_le` | `propext`, `Quot.sound` | proven frontier schedule-input gate formulas retain the recursive raw-depth budget |
| `PvNP.FormulaRecursiveGlobalSchedule.terminalLayerMinimalLayer` | `propext`, `Quot.sound` | constructed schedule-input layer from the terminal full-depth bottom layer |
| `PvNP.FormulaRecursiveGlobalSchedule.terminalLayerMinimalLayer_originalFormula` | `propext`, `Quot.sound` | proven terminal schedule-input formula is the chosen parent over the full-depth frontier |
| `PvNP.FormulaRecursiveGlobalSchedule.terminalLayerMinimalLayer_gateCount` | `propext`, `Quot.sound` | proven terminal schedule-input gate count matches the full-depth frontier profile |
| `PvNP.FormulaRecursiveGlobalSchedule.terminalLayerMinimalLayer_width_le_budget` | `propext`, `Quot.sound` | proven terminal schedule-input gates obey the width-one budget |
| `PvNP.FormulaRecursiveGlobalSchedule.recursiveFrontierMaxGateCount` | `propext`, `Quot.sound` | defined formula-wide maximum over recursive frontier gate counts |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayerGateCount_le_recursiveFrontierMaxGateCount` | `propext`, `Quot.sound` | proven in-depth frontier gate counts are bounded by the formula-wide maximum |
| `PvNP.FormulaRecursiveGlobalSchedule.recursiveFrontierGlobalTreeBudget` | `propext`, `Quot.sound` | defined formula-local max-frontier tree-budget profile |
| `PvNP.FormulaRecursiveGlobalSchedule.recursiveFrontierGlobalTreeBudgetFrom` | `propext`, `Quot.sound` | proven formula-local max-frontier budget satisfies every numeric schedule for in-depth frontier layers |
| `PvNP.FormulaRecursiveGlobalSchedule.terminalLayer_globalTreeBudgetFrom` | `propext`, `Quot.sound` | proven terminal-layer specialization of the formula-local max-frontier budget |
| `PvNP.FormulaRecursiveGlobalSchedule.frontierLayer_autoIteratedCollapse_of_globalProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven synthesized frontier layer consumes supplied product beats through the frozen-product schedule interface under the formula-local global budget |
| `PvNP.FormulaRecursiveGlobalSchedule.terminalLayer_autoIteratedCollapse_of_globalProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven terminal layer consumes supplied product beats through the frozen-product schedule interface under the formula-local global budget |
| `PvNP.FormulaRecursiveMaxProduct.freezeGateCountBound` | none | axiom-free product-bound family frozen at a chosen max gate count |
| `PvNP.FormulaRecursiveMaxProduct.rawBadCount_le_of_gateCount_le` | `propext` | proven raw bad-count expression is monotone in gate count |
| `PvNP.FormulaRecursiveMaxProduct.productBeat_freezeGateCount_of_le` | `propext` | proven max-count product beat transfers to a smaller gate count under the frozen bound family |
| `PvNP.FormulaRecursiveMaxProduct.productValidFrom_freezeGateCount_of_le` | `propext` | proven full product-valid schedules transfer from max gate count to smaller gate count under the frozen bound family |
| `PvNP.FormulaRecursiveMaxProduct.recursiveFrontierMaxProductBound` | `propext`, `Quot.sound` | defined product-bound family frozen at the formula's recursive max frontier count |
| `PvNP.FormulaRecursiveMaxProduct.frontierLayer_productValidFrom_of_maxProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven max-frontier product schedule supplies any in-depth frontier layer at truth-table fallback width |
| `PvNP.FormulaRecursiveMaxProduct.terminalLayer_productValidFrom_of_maxProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven max-frontier product schedule supplies the terminal layer when supplied at terminal width |
| `PvNP.FormulaRecursiveMaxProduct.frontierLayer_autoIteratedCollapse_of_maxProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven in-depth frontier layers consume a max-count product schedule through the frozen-product interface |
| `PvNP.FormulaRecursiveMaxProduct.terminalLayer_autoIteratedCollapse_of_maxProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven terminal layer consumes a max-count product schedule supplied at terminal width |
| `PvNP.FormulaRecursiveMaxProduct.allFrontierLayers_autoIteratedCollapse_of_maxProductBeats` | `propext`, `Classical.choice`, `Quot.sound` | proven one max-count product schedule covers every in-depth recursive frontier layer |
| `PvNP.FormulaRecursiveRatioSchedule.frontierLayer_ratioRegimeCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven recursive frontier layers consume supplied ratio-regime schedules under the formula-local global budget |
| `PvNP.FormulaRecursiveRatioSchedule.terminalLayer_ratioRegimeCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven terminal recursive layers consume supplied ratio-regime schedules under the formula-local global budget |
| `PvNP.FormulaRecursiveRatioSchedule.allFrontierLayers_ratioRegimeCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven all in-depth nonempty recursive frontier layers consume supplied ratio-regime schedules |
| `PvNP.FormulaRecursiveRatioSchedule.frontierLayer_geometricCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven recursive frontier layers consume the geometric ratio schedule under an explicit entry-size inequality |
| `PvNP.FormulaRecursiveRatioSchedule.terminalLayer_geometricCollapseWithGlobalTreeBudget` | `propext`, `Classical.choice`, `Quot.sound` | proven terminal recursive layers consume the geometric ratio schedule under an explicit entry-size inequality |
| `PvNP.FormulaRecursiveWidthSchedule.truthTableRecursiveWidthProfile` | `propext`, `Quot.sound` | defined fallback recursive width profile using the existing truth-table layer width budget |
| `PvNP.FormulaRecursiveWidthSchedule.frontierLayer_ratioRegimeCollapseWithWidthProfile` | `propext`, `Classical.choice`, `Quot.sound` | proven recursive frontier layers consume supplied ratio-regime schedules at a supplied profile width |
| `PvNP.FormulaRecursiveWidthSchedule.allFrontierLayers_ratioRegimeCollapseWithWidthProfile` | `propext`, `Classical.choice`, `Quot.sound` | proven all in-depth nonempty recursive frontier layers consume supplied ratio-regime schedules at supplied profile widths |
| `PvNP.FormulaRecursiveWidthSchedule.frontierLayer_geometricCollapseWithWidthProfile` | `propext`, `Classical.choice`, `Quot.sound` | proven recursive frontier layers consume the geometric ratio schedule at a supplied profile width under an explicit entry-size inequality |
| `PvNP.FormulaRecursiveWidthSchedule.allFrontierLayers_geometricCollapseWithWidthProfile` | `propext`, `Classical.choice`, `Quot.sound` | proven all in-depth recursive frontier layers consume geometric ratio schedules at supplied profile widths under per-level entry-size bounds |
| `PvNP.FormulaRecursiveNonempty.NoEmptyFanins` | none | structural raw-syntax predicate excluding empty unbounded fan-in gates |
| `PvNP.FormulaRecursiveNonempty.exists_child_depth_ge_of_le_depthMax` | `propext`, `Quot.sound` | proven max-depth list witness used by the nonempty recursive frontier proof |
| `PvNP.FormulaRecursiveNonempty.exists_topChild_depth_ge_of_noEmptyFanins` | `propext`, `Quot.sound` | proven no-empty-fanin formulas with positive remaining depth expose a no-empty-fanin top child with enough depth |
| `PvNP.FormulaRecursiveNonempty.depthFrontier_nonempty_of_noEmptyFanins` | `propext`, `Quot.sound` | proven root-list recursive frontiers are nonempty when a no-empty-fanin root has enough depth |
| `PvNP.FormulaRecursiveNonempty.formulaDepthFrontier_nonempty_of_noEmptyFanins` | `propext`, `Quot.sound` | proven single-formula recursive frontiers are nonempty for every level within depth under no-empty-fanin syntax |
| `PvNP.FormulaRecursiveNonempty.frontierLayerGateCount_nonempty_of_noEmptyFanins` | `propext`, `Quot.sound` | proven recursive frontier gate counts are nonempty for every level within depth under no-empty-fanin syntax |
| `PvNP.FormulaRecursiveNonempty.allFrontierLayers_ratioRegimeCollapseWithWidthProfile_noEmptyFanins` | `propext`, `Classical.choice`, `Quot.sound` | proven supplied-width ratio-regime frontier consumers discharge nonempty counts from no-empty-fanin syntax |
| `PvNP.FormulaRecursiveNonempty.allFrontierLayers_geometricCollapseWithWidthProfile_noEmptyFanins` | `propext`, `Classical.choice`, `Quot.sound` | proven supplied-width geometric frontier consumers discharge nonempty counts from no-empty-fanin syntax |
| `PvNP.FormulaRecursiveSizeBound.formulaSizeSum` | `propext`, `Quot.sound` | defined list-level raw formula-size sum used by recursive frontier size accounting |
| `PvNP.FormulaRecursiveSizeBound.formulaSizeSum_topChildren_le` | `propext`, `Quot.sound` | proven one top-child expansion does not increase raw formula-size sum |
| `PvNP.FormulaRecursiveSizeBound.formulaSizeSum_depthFrontier_le` | `propext`, `Quot.sound` | proven repeated recursive frontier expansion does not increase raw formula-size sum |
| `PvNP.FormulaRecursiveSizeBound.formulaDepthFrontier_length_le_formulaSize` | `propext`, `Quot.sound` | proven each recursive formula frontier length is bounded by raw formula size |
| `PvNP.FormulaRecursiveSizeBound.frontierLayerGateCount_le_formulaSize` | `propext`, `Quot.sound` | proven each recursive frontier gate count is bounded by raw formula size |
| `PvNP.FormulaRecursiveSizeBound.recursiveFrontierMaxGateCount_le_formulaSize` | `propext`, `Quot.sound` | proven the formula-wide max-frontier gate count is bounded by raw formula size |
| `PvNP.FormulaRecursiveSizeBound.recursiveFrontierSizeTreeBudget` | `propext`, `Quot.sound` | defined size-based structural tree-budget profile `formulaSize F * (s - 1)` |
| `PvNP.FormulaRecursiveSizeBound.recursiveFrontierGlobalTreeBudget_le_sizeTreeBudget` | `propext`, `Quot.sound` | proven the previous max-frontier tree budget is bounded by the formula-size tree budget |
| `PvNP.FormulaRecursiveSizeBound.recursiveFrontierSizeTreeBudgetFrom` | `propext`, `Quot.sound` | proven the size-based tree budget satisfies every numeric schedule for any recursive frontier layer |
| `PvNP.FormulaRecursiveSizeBound.recursiveFrontierMaxSizeTreeBudgetFrom` | `propext`, `Quot.sound` | proven the size-based tree budget also satisfies every numeric schedule for the max-frontier count |
| `PvNP.FormulaSyntacticDNF.syntacticDNF` | none | axiom-free syntactic DNF expansion for raw formulas |
| `PvNP.FormulaSyntacticDNF.dnfEval_andDNF` | `propext` | proven semantic conjunction law for distributed DNF products |
| `PvNP.FormulaSyntacticDNF.eval_syntacticDNF` | `propext`, `Quot.sound` | proven exact Boolean semantics of syntactic DNF expansion |
| `PvNP.FormulaSyntacticDNF.widthDNF_orDNF_le` | `propext` | proven DNF disjunction preserves a shared width bound |
| `PvNP.FormulaSyntacticDNF.widthDNF_andDNF_le_add` | `propext`, `Quot.sound` | proven DNF conjunction width is bounded by sum of operand widths |
| `PvNP.FormulaSyntacticDNF.widthDNF_syntacticDNF_le_formulaSize` | `propext`, `Quot.sound` | proven syntactic DNF width is bounded by raw formula size |
| `PvNP.FormulaSyntacticDNF.syntacticDNFView` | `propext`, `Quot.sound` | constructed semantic `DNFView` from syntactic DNF under supplied simplicity |
| `PvNP.FormulaSyntacticDNF.widthDNF_syntacticDNFView_le_formulaSize` | `propext`, `Quot.sound` | proven packaged syntactic DNF view width is bounded by raw formula size |
| `PvNP.FormulaVarWidthSchedule.topConnectiveFormula_child_width_le_vars` | `propext`, `Quot.sound` | proven top-connective truth-table child views have generic width at most `n` |
| `PvNP.FormulaVarWidthSchedule.positiveDepthFormula_child_width_le_vars` | `propext`, `Quot.sound` | proven positive-depth raw-formula truth-table child views have generic width at most `n` |
| `PvNP.FormulaVarWidthSchedule.topConnectiveFormula_ratioRegimeCollapseWithVarWidth` | `propext`, `Classical.choice`, `Quot.sound` | proven top-connective raw formulas route through supplied ratio schedules at width `n` |
| `PvNP.FormulaVarWidthSchedule.positiveDepthFormula_ratioRegimeCollapseWithVarWidth` | `propext`, `Classical.choice`, `Quot.sound` | proven positive-depth raw formulas route through supplied ratio schedules at width `n` |
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
function and its partial-matching restrictions; the matching-distribution and
probability-interface layers are exact finite counting/cross-multiplied event
probability only (no measure-theoretic probability, expectation, or
collapse-probability upper bound; identity-subset and square-permutation
spaces only, not rectangular `p > h` injections). The Gate B route theorems are certificate theorems whose
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
instantiation whose second stage is the width-budget-0 tail. `FrozenDepthView`
adds a supplied-view consumer with an actual final-tree global budget
`t(d,s) = gateCount * (s - 1)`, and `FormulaStructuralSchedule` extends that
consumer to arbitrary nonempty ratio-regime schedules plus positive-depth raw
formulas after top-constructor synthesis.  `FormulaDepthDecomposition` proves
that this top synthesis strictly decreases formula depth for every exposed
gate formula, and `FormulaRecursiveDepth` proves the repeated-frontier
raw-depth budget for recursive top-child expansion.  `FormulaDepthZeroBottom`
adds exact width-one-or-less DNF gates and a packaged bottom-layer list for
members that survive to the full-depth frontier.  `FormulaRecursiveDecomposition`
packages every frontier level, the top-child transition, the raw-depth budget,
and the terminal bottom layer as one structural skeleton.
`FormulaRecursiveGateLayers` reifies every recursive frontier level as a
`GateSpec.dnf` list with formula and count alignment, but the intermediate
width bound is only the truth-table fallback `n`; only the terminal full-depth
bottom layer carries the width-one-or-less bound. `FormulaRecursiveLayerProfile`
adds the per-level profile facts over those layers: gate counts, successor
counts by top-child expansion, honest width budgets, and constant tree-budget
facts. `FormulaRecursiveGlobalSchedule` then packages synthesized frontier and
terminal layers as schedule inputs under one formula-local max-frontier tree
budget and routes them through the frozen-product schedule consumer from
supplied `ProductValidFrom` beats. `FormulaRecursiveMaxProduct` freezes a
supplied product-bound family at the recursive max frontier count so the same
max-count schedule covers every smaller in-depth recursive frontier layer.
`FormulaRecursiveRatioSchedule` routes recursive frontier and terminal layers
through supplied ratio-regime schedules under the same formula-local global
budget, and generates the named geometric ratio schedule only under explicit
entry-size inequalities. `FormulaRecursiveWidthSchedule` adds a supplied
per-level width-profile hook for recursive frontier ratio/geometric consumers,
so later structural width theorems can replace the truth-table fallback in
those consumers without changing the global tree-budget interface.
`FormulaRecursiveNonempty` adds the `NoEmptyFanins` structural predicate and
uses it to synthesize the nonempty recursive frontier gate-count hypotheses
for all levels within `depth F`; its supplied-width ratio/geometric corollaries
therefore remove that one caller obligation under no-empty-fanin raw syntax.
`FormulaRecursiveSizeBound` proves that repeated recursive frontier expansion
does not increase raw formula-size sum, so every frontier gate count and the
max-frontier count are bounded by `formulaSize F`; it exposes the corresponding
size-based `TreeBudgetFrom` profile `formulaSize F * (s - 1)`.
`FormulaSyntacticDNF` gives every raw formula a semantic syntactic DNF expansion
and proves its width is at most `formulaSize F`; packaging it as a `DNFView`
still requires a supplied `SimpleDNF (syntacticDNF F)` proof, with no
normalization or efficient product/counting synthesis.
`FormulaVarWidthSchedule` instantiates the supplied positive-depth raw-formula
ratio-regime route at width `n`, removing the caller-supplied child-width
predicate while preserving the honest truth-table fallback boundary.
Product-beat hypotheses remain supplied on the frozen-product route;
ratio-regime schedules remain supplied except for explicit-bound geometric
corollaries, and the recursive width profile remains supplied.  Intermediate
child views still use the truth-table fallback unless an external profile is
provided, and the artifact still does not synthesize `B` from arbitrary
formulas, derive efficient recursive depth-`d` layered views from arbitrary
formula syntax, synthesize normalized/simple syntactic DNF views or efficient
width profiles, prove a global efficient `t(d,s)` theorem, or close full
frozen-form B4.
The PHP switching lemma (Gate A rung 4 as a whole) remains open: the
collapse-probability analysis covers depth-1 events only —
single-literal/single-term (`PHPFullMatchingCollapseBound`), with the
single-literal event's probability additionally made exact and its
realizability certified in `PHPFullMatchingCollapseExact`, and the
multi-term DNF total-size union bound of `PHPFullMatchingDNFBound`; the
  restricted-DNF canonical-tree skeleton of `PHPFullMatchingCanonicalDT` is
  deterministic infrastructure only, `PHPFullMatchingBadPathEncoding` keeps
  the original matching point in a conservative optional-code count, and
  `PHPFullMatchingCompressedBadPathCount` proves only free-variable
  certification, a row-level free-set multiplicity count, and a conditional
  compressed-target count scaffold. No constructed compressed matching-space
  bad-set encoding/counting theorem, path-code fiber bound, or geometric
  term-count-independent depth-`t` collapse-probability bound is proved.

## Re-Verification

```bash
lake env lean lean/PvNP/Audit.lean
```

Release-candidate audit helper:

```powershell
./scripts/audit-release.ps1
```
