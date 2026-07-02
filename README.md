# Formal Switching Lemma in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20757627.svg)](https://doi.org/10.5281/zenodo.20757627)

This repository is a curated Lean 4 publication artifact for the `PvNP`
SimpleDNF switching-lemma line, CNF-dual bridge, and bounded-depth explicit
layer-schedule infrastructure.

It is split from the private Quantyra/PvNP research workspace so the theorem
surface is narrow, reproducible, and easy to cite by release/DOI.

## Theorem Surface

- `PvNP.SwitchingClose2.switchingLemmaTermSimple_proved`: a Lean-checked
  SimpleDNF switching lemma in the repository's canonical decision-tree encoding.
- `PvNP.BoundedDepthFregeSwitchingBridge.bdDNF_switching_bridge`: a bridge from
  the proved SimpleDNF statement to real bounded-depth formula/restriction and
  decision-tree infrastructure.
- `PvNP.BoundedDepthLayerView.bdFormula_dnfView_switching_collapse`: one-step
  collapse for a bounded-depth formula carrying an explicit simple DNF view.
- `PvNP.BoundedDepthIteratedCollapse.twoLayerCollapse_exists_from_stagePremises`:
  two-layer explicit DNF/CNF schedule composition under named restriction and
  per-stage decision-tree hypotheses.
- `PvNP.BoundedDepthIteratedCollapse.oneLitTwoLayerCollapse_example`: non-empty
  one-literal DNF/CNF witness for the two-layer schedule machinery.
- `PvNP.BoundedDepthIteratedCollapse.bdFormula_cnfView_dual_switching_collapse`:
  CNF-view collapse obtained by dualizing a simple CNF into a simple DNF,
  applying the proved DNF switching bridge, and complementing the resulting
  decision tree.
- `PvNP.BoundedDepthIteratedCollapse.threeLayerCollapse_exists_from_stagePremises`:
  explicit three-layer DNF/CNF/DNF schedule composition with common-extension
  compatibility and depth accounting by the sum of stage depths.
- `PvNP.BoundedDepthIteratedCollapse.kLayerCollapse_exists_from_schedule`:
  list-indexed alternating DNF/CNF schedule certificates for named explicit
  layers, with common-extension compatibility, non-empty layer lists, and summed
  decision-tree depth bounds.
- `PvNP.BoundedDepthIteratedCollapse.oneLitThreeLayerCollapse_example_nonvacuous`
  and `PvNP.BoundedDepthIteratedCollapse.oneLitKLayerSchedule3_nonempty`:
  non-empty one-literal witnesses for the three-layer and list-indexed schedule
  machinery.
- `PvNP.BoundedDepthIteratedCollapse.GeneratedDNFLayerStage`,
  `generatedDNFStage_exists`, `GeneratedCNFLayerStage`, `generatedCNFStage_exists`,
  `dnfPremiseOfGenerated`, `cnfPremiseOfGenerated`, `generatedTwoLayerCollapse_exists`,
  `generatedThreeLayerCollapse_exists`:
  generated one-step DNF/CNF stage witnesses directly from the switching collapse
  (with exact `depthBound = s` accounting) and their composition into two- and
  three-layer certificates under common-extension compatibility.
- `PvNP.BoundedDepthIteratedCollapse.GeneratedExplicitLayerStage` and
  `generatedKLayerCollapse_exists` / `generatedNonemptyKLayerCollapse_exists`:
  list-indexed generated DNF/CNF stage schedules whose explicit images preserve
  per-stage `depthBound = s`, aggregate generated-depth accounting, and common
  extension compatibility. `emptyGeneratedKLayerSchedule4_nonempty` is a concrete
  generated DNF/CNF/DNF/CNF witness with aggregate depth sum `4`.
- `PvNP.CertifiedAffine.certifiedAffineExtraction_completeOn` and
  `PvNP.CertifiedAffine.incident_collision_endpoints`: arbitrary finite
  Tseitin-graph extraction metadata, low-degree/simple-edge certificate surface,
  and a reusable non-loop incidence collision lemma connected to
  `SemanticExtractorCompleteOn`.
- `PvNP.RestrictedPHPFloor.restrictedPHPFormula` and
  `PvNP.RestrictedPHPFloor.PHPDepthFloorStatement`: a restricted PHP formula
  surface and isolated decision-tree depth-floor interface.  Collision clauses in
  this restricted view are proper-pair only.
- `PvNP.RestrictedPHPFloor.eval_tinyOneOneRestrictedPHPFormula` and
  `PvNP.RestrictedPHPFloor.tinyOneOnePHPDepthFloor`: a concrete `1 × 1`
  restricted PHP semantic witness and bounded decision-tree/query-depth floor
  under the empty restriction.  This is not a Frege/PHP lower bound.
- `PvNP.RestrictedPHPFloor.twoOnePHPFalsifiedClauseSearchDepthFloor`: a concrete
  `2 × 1` bounded query/search floor for outputting a falsified clause of the
  fixed restricted PHP formula.  This is only a certificate-search result; it is
  not a Frege/PHP lower bound and not a positive Boolean depth floor for the
  identically false unsatisfiable formula.
- `PvNP.RestrictedPHPFloor.queryTree_depth_ge_two_of_two_unqueried_ambiguity`:
  a reusable output-valued query-tree ambiguity lemma for proving depth-at-least
  two certificate-search floors from branch-invalidity witnesses.
- `PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor`: a concrete
  `3 × 2` bounded query/search floor (`2 ≤` worst-case query depth) for outputting
  a falsified clause of the fixed restricted PHP formula.  This is only a
  certificate-search result; it is not a Frege/PHP lower bound.
- `PvNP.RestrictedPHPFloor.queryTree_depth_ge_three_of_adversary` and
  `threeTwoPHPFalsifiedClauseSearchDepthFloor_three`: a reusable generic
  adversary lemma forcing search-query depth at least three, and the `3 × 2`
  falsified-clause search floor strengthened to three by a pigeon-partner
  adversary; `FalsifiedClauseSearchDepthFloorStatement` is the general
  statement shape with the proved `2 × 1` and `3 × 2` instances.
- `PvNP.PHPSearchFloor.phpFalsifiedClauseSearchDepthFloor` and
  `phpFalsifiedClauseSearchDepthFloorStatement`: the parameterized `p × h`
  falsified-clause search depth floor (`2·h ≤` worst-case query depth) for
  every `p` and `h`, via a reusable generic STATEFUL adversary lemma
  (`queryTree_depth_floor_of_stateful_adversary`) — a FAMILY instance of the
  statement shape.  Non-vacuity witnessed at `3 × 2`
  (`phpFalsifiedClause32_correctTree_exists`); for `p ≤ h` the statement is
  vacuous (no correct tree exists — informal, not formalized);
  `threeTwoPHPFalsifiedClauseSearchDepthFloor_four` strengthens the bespoke
  `3 × 2` floor to four.
- `PvNP.PHPSearchFloorTightness.threeTwoPHPFalsifiedClauseSearch_optimal_depth_eq_four`:
  formalized tightness at the fixed `3 × 2` instance — an explicit correct
  search tree of depth exactly four together with the floor of four; the
  optimal worst-case query count there is exactly four.  Family tightness of
  the `2·h` floor is not formalized.
- `PvNP.BDVariableCoverage.refutationTrace_queries_var` (with
  `bdProofTrace_sound_nonstandard`): the variable-coverage theorem for the
  repository's LOCAL cut-free bounded-depth Tait trace system — every
  refutation trace must perform `litEM` on every variable whose avoiding
  clauses are satisfiable (non-standard-semantics soundness device).
- `PvNP.PHPCNFCoverage.phpCNF32_traceSize_ge_six` and
  `PvNP.PHPFamilyCoverage.phpCNF_family_traceSize`: concrete `3 × 2` and
  growing-family variable-coverage floors — for every `h > 0`, every
  refutation trace of `phpCNF (h+1) h` queries all `(h+1)·h` variables, so its
  query-order length and trace size are at least `(h+1)·h`.  These are
  variable-coverage floors, LINEAR in the number of PHP variables, on the local cut-free trace system,
  not Frege/PHP proof-size lower bounds.
- `PvNP.BDTaitCompleteness.bdTait_complete` with `phpCNF_family_unsat` and
  `phpCNF_family_refutationTrace_nonempty`: completeness of the local
  cut-free bounded-depth Tait system (every unsatisfiable CNF admits a
  refutation trace; stated with `Nonempty`), pigeonhole unsatisfiability of
  `phpCNF (h+1) h`, and nonemptiness of the refutation-trace types the
  coverage floors quantify over.  Completeness alone proves no hardness.
- `PvNP.TraceSearchConnection.extractQueryTreeUnpadded_evalSelector` and
  `PvNP.PHPFamilyTraceSearchRoute.phpCNF_family_traceSize_ge_two_h_via_search`:
  the trace-dependent UNPADDED extraction (query schedule = the trace's
  `litEM` order; correctness consumes refutation-hood via the coverage
  theorem; non-freeness witnessed by `buildTree_nil_incorrect`) and the
  composed family route — refutation trace → extracted correct search tree
  whose depth equals the trace's query-order length → the `2·h` adversary
  floor → `2·h ≤` query-order length `≤` trace size for every `h > 0` (bounds
  on refutation traces of the LOCAL cut-free trace system, in the
  linear-in-the-number-of-variables regime).  The direct coverage bound `(h+1)·h` is
  numerically stronger for `h > 1`; the composition (the first
  refutation→search→adversary route formalized in this development) is the
  contribution, not the number.
- `PvNP.BDTraceToSearchExtraction` / `PvNP.BDTraceToSearchPremise`: the
  S2065 trace/profile-to-query extraction bridge for the fixed `twoCyclePath3`
  CNF against the fixed `3 × 2` search problem, with all S2052–S2064
  interface-contract obligations proved under their S2065-redefined content.
  REDEFINITION DISCLOSURE: before S2065 those obligation `Prop`s were
  deliberately constructorless placeholders (uninhabitable); they were given
  explicitly displayed content first and that content was then proved —
  nothing previously open was proved under its old statement.  At that fixed
  instance the search problem is total, so extraction correctness is
  order-independent (disclosed in the module headers).

## Non-Claims Boundary

This artifact does **not** prove or imply:

- `P != NP` or `P = NP`;
- an NP or circuit lower bound;
- a Frege/PHP lower bound;
- a proved PHP decision-tree floor beyond explicitly supplied boundary records
  such as the tiny `1 × 1` restricted view, or the bounded `2 × 1`
  and `3 × 2` falsified-clause search floors;
- a positive Boolean decision-tree depth floor for the full `2 × 1` PHP formula
  (that formula is identically false, so a constant-false Boolean tree has depth
  `0`);
- any positive Boolean decision-tree depth floor for an unsatisfiable PHP formula
  merely from the bounded falsified-clause search floors;
- arbitrary AC0 or arbitrary bounded-depth formula collapse;
- a general CNF switching lemma independent of the explicit dualization bridge;
- a proof-size or proof-depth lower bound for any proof system WITH CUT: the
  variable-coverage and trace-size floors concern only the repository's local
  cut-free bounded-depth Tait trace system and are linear in the number of PHP variables (the stated `(h+1)*h` / `2*h` variable-query floors);
- tightness of the parameterized `2·h` search floor beyond the fixed `3 × 2`
  instance (family tightness is informal only);
- any claim that the S2065 extraction bridge carries proof-complexity content
  at its fixed instance (its search problem is total, so correctness there is
  order-independent; the genuine open proof-complexity route obligation
  remains an explicitly uninhabited `Prop`);
- any strength, efficiency, or size/depth-optimality claim for the local
  cut-free system from its completeness theorem (completeness alone proves no
  hardness; the naive constructed refutations are exponential-size).

Note on naming: the Lean namespace `BoundedDepthFrege` names this repository's
bounded-depth formula and trace INFRASTRUCTURE; no lower bound for the
bounded-depth Frege proof system is proved here.

The CNF-facing public theorem is a dual corollary for simple CNF views: it
reduces to the proved DNF switching bridge by complementing literals, formulas,
and decision trees. The two-layer, three-layer, and k-layer results are explicit
schedule/certificate theorems for named layers and named restrictions; they are
not arbitrary formula-collapse theorems. The repository is P-vs-NP-relevant
proof-complexity infrastructure only, with claims limited to the Lean-checked
declarations listed above.

## Reproducibility

Toolchain: `leanprover/lean4:v4.13.0`.

Build the artifact:

```bash
lake build PvNP.BoundedDepthIteratedCollapse
```

Run the audit surface:

```bash
lake env lean lean/PvNP/Audit.lean
```

Release-candidate audit helper:

```powershell
./scripts/audit-release.ps1
```

## DOI

Repository concept DOI: `10.5281/zenodo.20757627`.

Version `v0.1.0` is archived on Zenodo:

- DOI: `10.5281/zenodo.20757628`
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.1.0`

Version `v0.4.0` adds the variable-coverage floors for the local cut-free
bounded-depth Tait trace system (`BDVariableCoverage`, `PHPCNFCoverage`,
`PHPFamilyCoverage`), the parameterized `2·h` falsified-clause search depth
floor via a reusable generic stateful adversary with formalized `3 × 2`
tightness (`PHPSearchFloor`, `PHPSearchFloorTightness`), completeness of the
local system with pigeonhole non-vacuity witnesses (`BDTaitCompleteness`), the
trace-dependent unpadded extraction and the composed family
refutation→search→adversary route (`TraceSearchConnection`,
`PHPFamilyTraceSearchRoute`), the `3 × 2` search floor of three with its
generic adversary lemma (`RestrictedPHPFloor` additions), and the S2065
fixed-instance extraction bridge with its redefinition disclosure
(`BDTraceToSearchExtraction`, `BDTraceToSearchPremise`; the genuine
proof-complexity route obligation remains open):

- DOI: (version DOI pending Zenodo auto-archive; concept DOI is `10.5281/zenodo.20757627`)
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.4.0`

Version `v0.3.1` adds audited generated-stage infrastructure and generated
nonempty k-layer schedule infrastructure
(`GeneratedDNFLayerStage`, `generatedDNFStage_exists`, `GeneratedCNFLayerStage`,
`generatedCNFStage_exists`, `dnfPremiseOfGenerated`, `cnfPremiseOfGenerated`,
`generatedTwoLayerCollapse_exists`, `generatedThreeLayerCollapse_exists`,
`GeneratedExplicitLayerStage`, `generatedKLayerCollapse_exists`,
`generatedNonemptyKLayerCollapse_exists`, `emptyGeneratedKLayerSchedule3_nonempty`,
`emptyGeneratedKLayerSchedule4_nonempty`) for explicit one-step DNF/CNF stages
with exact per-stage `depthBound = s` accounting, aggregate depth accounting,
and common-extension composition into k-layer certificates:

- DOI: (version DOI pending Zenodo auto-archive; concept DOI is `10.5281/zenodo.20757627`)
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.3.1`

Version `v0.3.0` (prior) adds the audited generated-stage infrastructure
(`GeneratedDNFLayerStage`, `generatedDNFStage_exists`, `GeneratedCNFLayerStage`,
`generatedCNFStage_exists`, `dnfPremiseOfGenerated`, `cnfPremiseOfGenerated`,
`generatedTwoLayerCollapse_exists`) for explicit one-step DNF/CNF stages
with exact depth accounting and common-extension two-layer composition:

- DOI: (version DOI pending Zenodo auto-archive; concept DOI is `10.5281/zenodo.20757627`)
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.3.0`

Version `v0.2.0` (prior) adds the audited CNF-dual bridge and explicit three-layer and
list-indexed k-layer schedule certificates:

- DOI: `10.5281/zenodo.20764338`
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.2.0`
