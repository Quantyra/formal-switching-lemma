# Integrity & Claims Ledger

**Scope:** this document states what this repository proves and what it does not.
The audit surface is `lean/PvNP/Audit.lean`, which pins selected kernel axiom
profiles with `#guard_msgs`.

## Non-Claims

This repository does **not** establish or imply:

- `P != NP` or `P = NP`;
- an NP or circuit lower bound;
- a Frege/PHP lower bound;
- a proved PHP decision-tree floor beyond explicitly supplied boundary records
  such as the tiny `1 × 1` restricted view, or the bounded `2 × 1`
  and `3 × 2` falsified-clause search floors;
- a positive Boolean decision-tree depth floor for the full `2 × 1` PHP formula
  (the formula is identically false, so a constant-false Boolean tree has depth
  `0`);
- any positive Boolean decision-tree depth floor for an unsatisfiable PHP formula
  merely from the bounded falsified-clause search floors;
- arbitrary AC0 collapse or arbitrary bounded-depth formula collapse;
- a general CNF switching lemma independent of the explicit dualization bridge;
- a proof-size or proof-depth lower bound for any proof system WITH CUT: the
  variable-coverage and trace-size floors concern only this repository's local
  cut-free bounded-depth Tait trace system and are linear in formula size;
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

No declaration above depends on `sorryAx`.

**S2065 redefinition disclosure.** The S2052-S2064 interface-contract
"obligation" `Prop`s in `PvNP.BDTraceToSearchPremise` were deliberately
constructorless placeholders (uninhabitable, logically equivalent to `False`)
until S2065 gave them explicitly displayed content, which was then proved.
Nothing previously open was proved under its old statement.  The genuine open
proof-complexity route obligation remains an explicitly uninhabited `Prop`.

**Scope of the coverage/trace floors.** All variable-coverage and trace-size
floors (`BDVariableCoverage`, `PHPCNFCoverage`, `PHPFamilyCoverage`,
`TraceSearchConnection`, `PHPFamilyTraceSearchRoute`) concern the LOCAL
cut-free bounded-depth Tait trace system defined in this repository and are
linear in formula size.  The parameterized `2*h` search floor is a
decision-tree bound for the falsified-clause SEARCH problem, vacuous for
`p <= h` (informal, not formalized; non-vacuity is witnessed at `3 x 2`), and
its family tightness is informal only.  Completeness (`bdTait_complete`) alone proves no hardness and
carries no size/depth optimality claim. The CNF-facing bridge dualizes simple
CNF views into simple DNF views and reuses the proved DNF switching bridge. The
two-layer, three-layer, and k-layer theorems are schedule-composition results
under explicit hypotheses; they are not arbitrary bounded-depth collapse
theorems.

## Re-Verification

```bash
lake env lean lean/PvNP/Audit.lean
```

Release-candidate audit helper:

```powershell
./scripts/audit-release.ps1
```
