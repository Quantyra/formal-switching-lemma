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
- `PvNP.PHPBooleanDepthFloor.fullPHPBoundary_depthFloor`: the first genuine
  FAMILY instance of `PvNP.RestrictedPHPFloor.PHPDepthFloorStatement` — for
  every `h`, any decision tree computing the SATISFIABLE `h × h` pigeonhole
  Boolean function under the empty restriction has depth at least `h · h`
  (evasiveness, via full sensitivity at the identity permutation point).
  Non-vacuity by `fullPHPBoundary_correctTree_exists` (a correct tree of depth
  `h·h + 1`).  Empty-restriction family only, elementary sensitivity
  mathematics; for `p > h` the PHP formula is identically false and no positive
  Boolean floor is claimed there (that regime is served by the falsified-clause
  SEARCH floors and the separate trace-system variable-coverage floors
  above).  This is a decision-tree depth floor, not a Frege/PHP
  proof-size lower bound.
- `PvNP.PHPRestrictedDepthFloor.matchingRestriction_depthFloor` and
  `matchingBoundary_depthFloor`: the master per-restriction theorem — for every
  partial-matching restriction (a set `S` of pigeons fixed along a permutation
  with two-sided inverse, other rows free), every decision tree computing the
  restricted `h × h` PHP function has depth at least the number of free
  variables — and the two-parameter boundary family instantiating
  `PHPDepthFloorStatement` with floor `(h − s) · h` (first `s` pigeons fixed
  along the identity), built on the permutation-point sensitivity lemmas
  `eval_permAssignment_true` / `eval_flip_permAssignment_false`.  Non-vacuity
  by `matchingBoundary_correctTree_exists`.  These are worst-case floors for
  each FIXED restriction in the class, not probabilistic statements over
  random-restriction distributions, and not a Frege/PHP proof-size lower
  bound.
- `PvNP.PHPMatchingDistribution.star_ratio` with `card_subsetSpace`,
  `freeCount_eq` / `phpVar_freeCount` / `fixCount_eq`, and
  `subsetSpace_depthFloor`: the uniform space of `s`-subsets of pigeons (each
  inducing the identity partial-matching restriction via `restrictionOf`) has
  exactly `choose h s` elements; every PHP variable is left free (a "star") by
  exactly `choose (h−1) s` subsets and fixed by the complement; and the exact
  star-probability identity `h * choose (h−1) s = (h − s) * choose h s` holds —
  the counting form of "every variable is a star with probability `(h−s)/h`",
  in the same counting style as the proved SimpleDNF switching lemma.
  `subsetSpace_depthFloor` transfers the `(h − s) · h` floor to EVERY point of
  the space (probability one), with per-subset non-vacuity by
  `subsetSpace_correctTree_exists`.  No probability measure is defined — all
  statements are exact finite counting identities; this first distribution
  pins the matching to the identity; and this is NOT a PHP switching lemma —
  no collapse-probability upper bound for restricted formulas is stated or
  proved (that summit, Gate A rung 4, remains open).
- `PvNP.PHPFullMatchingDistribution.card_fullMatchingSpace` with
  `phpVar_freeCount_full`, `phpVar_star_ratio_full`, and
  `fullMatchingSpace_depthFloor`: the Gate A rung-3 counting layer now also
  covers the full square matching-restriction space
  `subsetSpace h s × Equiv.Perm (Fin h)`.  The space has cardinality
  `choose h s * Fintype.card (Equiv.Perm (Fin h))`; every PHP variable is
  left free by exactly `choose (h−1) s * Fintype.card (Equiv.Perm (Fin h))`
  points; the same star-ratio identity holds after carrying the permutation
  factor; and the `(h − s) · h` floor transfers to EVERY point of the full
  space, with per-point non-vacuity by `fullMatchingSpace_correctTree_exists`.
  This formalizes square `h × h` permutation matchings, not rectangular
  `p > h` injection spaces, and still states no collapse-probability upper
  bound.
- `PvNP.PHPFullMatchingProbability.fullStarEvent_probability_eq` and
  `fullPHPCollapseBad_depthFloor_probability_one`: the full square matching
  surface now has an exact finite event/probability interface.  `EventProbEq`
  and `EventProbLe` are cross-multiplied counting statements, not measure
  theory: the star event has probability `(h-s)/h` in this finite sense, and
  the PHP depth-floor obstruction is packaged as a probability-one
  collapse-bad event.  This is still not the PHP switching lemma and states no
  collapse-probability upper bound.
- `PvNP.GeneratedGoodRestriction.jointBadSet_card_le`, `goodRestriction_exists`,
  and `simultaneousCollapse_exists`: Gate B stages B1/B2 — the first theorems in
  this repository where the switching lemma's counting GENERATES restrictions
  instead of consuming them: an explicit per-gate bad-set union bound, and,
  whenever a supplied counting hypothesis beats the `ℓ`-star restriction-space
  size, a single restriction that simultaneously collapses every listed
  DNF/CNF-view bottom gate to a decision tree of depth `< s`.  These are exact
  `Finset.card` counting corollaries of the proved SimpleDNF switching lemma
  (no probability measure, no new switching lemma).
- `PvNP.GeneratedIteratedCollapse.generatedSharedLayerCertificate_exists` with
  `OpenObligation` / `openObligations_nonempty`: a shared generated
  bottom-layer certificate plus a machine-readable obstruction map of the
  frozen-form B4 obligations.  The `openObligations` list is INTENTIONALLY
  nonempty and remains so: frozen-form B4 is open.
- `PvNP.GeneratedOneStepDepthReduction.generatedOneStepDepthReduction_exists`:
  the B3 one-step depth reduction for a minimal SUPPLIED layered view (one
  `and`/`or` parent gate over a listed bottom layer): B1/B2 counting generates
  the restriction, collapsed bottom gates are replaced by their generated
  trees, parent-merge semantics are preserved on assignments agreeing with the
  generated restriction, and one-step depth and child-count accounting is
  proved (`singletonEmptyDNFOr_nonvacuous` is the
  witness).  This is not arbitrary AC0/`BDFormula` decomposition into layered
  views.
- `PvNP.RestrictionComposition.restrict_compose`,
  `simultaneousCollapse_exists_consistent`, and `restrictionsWithStars_card`:
  first-wins restriction composition commuting with iterated restriction, the
  B1/B2 counting beat strengthened to subspaces of restrictions consistent
  with an accumulated base, and the closed form
  `|restrictionsWithStars n ℓ| = C(n, ℓ) · 2^(n − ℓ)` for the FULL star space.
  No closed-form cardinality is claimed for consistent subspaces over nonfree
  bases.
- `PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse`: the B4
  ROUTE theorem — for every plan-supplied `GeneratedCollapsePlan` of positive
  depth, counting generates one restriction per stage (never supplied),
  sequentially consistent and composed first-wins with a proved total
  extension, with final semantic preservation on assignments agreeing with
  the composed restriction, per-stage depth AND size
  accounting, and a last-stage combined decision tree of depth
  `≤ m_last · (s_last − 1)`.  In this route theorem, the per-stage layered
  views and counting beats are SUPPLIED side conditions, not a single
  product-of-stages hypothesis.  Full frozen-form B4 (single upfront depth-`d`
  layered view, internally derived product hypothesis `B(m, w, s, d)`, final
  global `t(d, s)` tree bound) remains OPEN.
  DISCLOSED SATISFIABILITY-GAP HISTORY: as shipped, each consistent-route beat
  compared a full-space bad-set count against a consistent-subspace
  cardinality, and no nonempty-gate multi-stage instance of those beats is
  exhibited (the witnesses `generatedIteratedCollapse_singleton_nonvacuous`
  and `generatedIteratedCollapse_twoStage_nonvacuous` use empty or width-0
  gate lists); the gap is closed for the refinement route by the renormalized
  bound below.
- `PvNP.RefinedSubspace.refinesSubspace_card` with
  `PvNP.SwitchingRelabel.dnfRestrict_refinesWith` and
  `dtDepth_termCanonicalDT_mapDNF`: the refinement subspace (extend a base's
  fixings exactly; strictly stronger than consistency) with the closed form
  `C(stars base, ℓ) · 2^(stars base − ℓ)` via an explicit free-subcube
  bijection, plus support-injective relabeling of literals/terms/DNFs/trees commuting
  with restriction and with canonical decision trees, canonical-tree depth
  invariance, and the factoring lemma that a refinement's restriction
  factors through its base (`dnfRestrict_refinesWith`) — the transport
  machinery for renormalized counting.
- `PvNP.GeneratedRefinedCollapse.badSetTerm_refines_card_le`,
  `simultaneousCollapse_exists_refined`, and
  `generatedRefinedIteratedCollapse`: the free-subcube RENORMALIZED bad-set
  bound `|badSetTerm D s ℓ ∩ refinesSubspace base ℓ| ≤ |R(stars base, ℓ−s)| · (8w)^s`,
  proved by transporting along the free-subcube relabeling and instantiating
  the proved SimpleDNF switching lemma at dimension `stars base`, together
  with the refined plan/certificate machinery whose stage restrictions REFINE
  the accumulated base.  This closes the disclosed B4-route satisfiability gap
  FOR THE REFINEMENT ROUTE only; merely-consistent-subspace-relative counting
  is still not provided, and frozen-form B4 remains open.
- `PvNP.RefinedTwoStageInstance.refinedTwoStage_nonemptyGates_nonvacuous` with
  `depthOneDNFView`: one concrete depth-2 renormalized plan over `n = 306`
  with a nonempty gate LIST, width BUDGET `1`, and the non-degenerate
  `(8·1)^s` beat factor at BOTH stages (stage-1 beat
  `256 · C(306,15) < C(306,17)`, proved symbolically; stage-2 beat
  `2^20 < 17 · 2^16`).  The stage-2 gate re-views the stage-1 GENERATED
  depth-`≤ 1` tree, which may be constant, so realized stage-2 width `≥ 1` is
  NOT certified; the instance's re-viewing is the depth-`≤ 1` special case
  only.  One concrete finite instance; no asymptotic family is claimed.
- `PvNP.TreePathViews.treeDNFView` / `treeCNFView` (with
  `widthDNF_treeDNFView_le` and `widthDNF_cnfDualDNF_treePathCNF₀_le`) and
  `PvNP.AutoReviewedIteration.nextLayer_originalFormula` /
  `nextLayer_gateCount` / `nextLayer_width`: every decision tree re-views as a
  simple DNF (its accepted paths, with repeated queries pruned so simplicity
  is structural) and dually as a simple CNF, with width bounded by the tree
  depth; `nextLayer` builds the next stage's layered view automatically from
  one generated one-step certificate, preserving gate count with per-gate
  width budget `s - 1`.  Representation infrastructure only — no counting and
  no lower bound; realized widths of auto re-viewed gates are BUDGET claims
  (generated trees may be constants); not frozen-form B4 closure.
- `PvNP.ScheduledAutoCollapse.autoIteratedCollapse` (with `ScheduleStage`,
  `BeatArith`, `ValidFrom`, `stepInput`, and the `castFormula` bookkeeping
  transport): schedule-driven automatic many-round iterated collapse — from
  one SUPPLIED width-bounded start layer and a purely numeric schedule of
  stage budgets and star counts whose beat conditions hold as closed-form
  `Nat` arithmetic (`ValidFrom`), a `GeneratedRefinedIteratedCertificate` of
  the schedule's length exists with constant stage gate counts and exactly
  the schedule's budgets and star counts.  The pinned STATEMENT records only
  these bookkeeping lists; the `nextLayer` re-viewing of every layer after
  the first is a property of the CONSTRUCTED WITNESS, and the theorem must
  not be cited for the re-viewing property of an arbitrary witness.  The
  beats remain per-stage supplied arithmetic side conditions, not a single
  product hypothesis — frozen-form B4 remains open; after any `s = 1` stage
  the schedule's tail degenerates to width-budget-0 stages with near-free
  beats, so schedule length alone is not a strength measure.
- `PvNP.FrozenProductSchedule.productValidFrom_validFrom` and
  `autoIteratedCollapse_of_frozenProduct`: a narrow product-to-schedule bridge.
  A single supplied bad-count bound family `B m w s d`, used for both the
  current refinement-space size `p` and the ambient space `n`, upper-bounds each
  raw closed-form bad count and beats the corresponding star-space size; this
  derives the exact `ValidFrom` obligations consumed by `autoIteratedCollapse`.
  A companion supplied tree-budget family `t d s` records the per-stage bound
  `m * (s - 1) <= t d s` and is preserved by the certificate theorem.  The
  start layer and numeric schedule remain supplied, and this is not arbitrary
  layered decomposition, not a final global
  `t(d,s)` depth theorem for arbitrary AC0 formulas, and not full frozen-form
  B4 closure.  `frozenProductSchedule_oneStage_nonvacuous` is a tiny
  one-stage width-0 sanity witness for the interface only.
- `PvNP.FrozenProductScheduleDemo.frozenProductSchedule_seventeenTwoStage_nonvacuous`:
  a named finite instantiation of that bridge over `n = 17`, one width-1
  single-literal start gate, schedule `[(1, 1), (1, 1)]`, explicit
  `B(1,1,1,2) = 2^20`, `B(1,0,1,1) = 0`, and `t(d,s) = 0`, yielding a
  certificate with stage gate counts `[1, 1]`, budgets `[1, 1]`, star counts
  `[1, 1]`, and the supplied `TreeBudgetFrom` witness.  It is beyond the
  earlier width-0 one-stage witness, but after the first `s = 1` stage the
  tail is width-budget-0 with a near-free beat; it is a small finite demo, not
  an asymptotic product-bound family or full frozen-form B4 closure.
- `PvNP.FormulaFamilyCollapse.formulaFamilyCollapse`: formula-level family
  collapse for parent-merged embedded simple-DNF children, synthesizing the
  semantic `GateSpec.dnf` start layer from raw DNF syntax and then applying the
  geometric family collapse.  This removes a supplied semantic-view premise for
  that syntactic class only; it is not arbitrary bounded-depth decomposition.
- `PvNP.MixedFormulaFamilyCollapse.mixedFormulaFamilyCollapse` and
  `cnfFormulaFamilyCollapse`: bottom-layer synthesis for both `GateSpec`
  constructors from raw syntax.  Raw DNF children use the constructed
  `dnfToBD_dnfView`; raw CNF children are embedded as real `and`-of-`or`s
  formulas with a constructed `CNFView`, then switched through the existing
  dual-DNF bridge.  The mixed theorem covers parent merges of arbitrary mixtures
  of those embedded simple DNF/CNF children, with a finite witness
  `mixedFamily_dnfCnf_twoStage` exercising both constructors.  This is still
  bottom-layer synthesis only: no depth-`d` decomposition, no global `t(d,s)`
  theorem, and no PHP switching lemma.
- `PvNP.FrozenDepthView.frozenDepthView_geometricCollapseWithGlobalTreeBudget`:
  an explicit structural B4 interface consumer.  A supplied
  `FrozenDepthView n F d` packages a real formula, a start layer that is exactly
  that formula, and a depth bound `depth F <= d`; from that view plus the
  geometric entry hypotheses, the theorem returns the generated refined
  certificate and an actual last-stage decision tree bounded by the global
  budget `t(d,s) = gateCount * (s - 1)`.  The mixed-bottom corollary
  `mixedBottomFrozenDepthView_geometricCollapseWithGlobalTreeBudget` routes the
  raw DNF/CNF bottom-layer class through this interface at its computed depth.
  This is not automatic decomposition of arbitrary bounded-depth formulas, and
  full frozen-form B4 remains open.
- `PvNP.FormulaTruthTableView.topConnectiveFormula_geometricCollapseWithGlobalTreeBudget`:
  a broad semantic fallback for exact top-level `and`/`or` formulas.  Every
  immediate child formula is viewed as a DNF by querying all variables in a
  full decision tree and converting tree paths to a simple DNF, so
  `topConnectiveFrozenDepthView` automatically constructs a `FrozenDepthView`
  for the raw syntax `p.merge children`.  The consumer theorem inherits the
  global last-tree budget under an explicit supplied width bound; the module
  proves only the generic truth-table width bound `<= n`.  This covers more
  raw syntax but is intentionally not an efficient arbitrary AC0 depth-`d`
  decomposition.  The raw positive-depth wrapper
  `positiveDepthFormula_geometricCollapseWithGlobalTreeBudget` removes the
  need for callers to manually expose the top constructor: any positive-depth
  `BDFormula` is pattern-matched to its top `and`/`or` gate and routed through
  the same truth-table fallback.  Leaves/constants still have no exact identity
  parent in `MinimalLayeredFormula`, and full frozen-form B4 remains open.
- `PvNP.FormulaStructuralSchedule.frozenDepthView_ratioRegimeCollapseWithGlobalTreeBudget`
  and `positiveDepthFormula_ratioRegimeCollapseWithGlobalTreeBudget`:
  the same supplied-view global last-tree budget consumer now works for
  arbitrary nonempty ratio-regime schedules, not just the fixed geometric
  schedule.  The supplied-view theorem carries
  `TreeBudgetFrom (frozenGlobalTreeBudget V)` for every schedule and returns
  the actual last-stage tree bounded by `gateCount * (s - 1)`; the
  positive-depth raw-formula corollary synthesizes the top-layer view from
  non-leaf raw syntax and routes it through the same schedule interface.  The
  child views still use the truth-table/path-DNF fallback and the ratio-regime
  hypotheses are supplied, so this is not efficient arbitrary AC0
  decomposition or full frozen-form B4.
- `PvNP.FormulaDepthDecomposition.positiveDepthPeel`: the synthesized
  positive-depth raw-formula `FrozenDepthView` now carries an audited one-step
  depth-decomposition fact.  Every exposed top child, and every gate formula in
  `positiveDepthFrozenDepthView`, has strictly smaller `depth` than the
  original raw formula, with the predecessor-budget form also pinned.  This is
  a real structural prerequisite for recursive depth-`d` decomposition, but it
  still uses truth-table/path-DNF child views and does not synthesize efficient
  bottom width or product/counting hypotheses.
- `PvNP.FormulaRecursiveDepth.recursiveDepthFrontier`: repeated top-child
  expansion now has a checked raw-depth budget.  If a formula survives in the
  `k`-step frontier, then `depth child + k <= depth F`; in particular, every
  surviving member of the full-depth frontier has depth zero.  This is
  recursive structural bookkeeping only: it does not build recursive
  `FrozenDepthView` layers, efficient bottom views, or product/counting
  hypotheses.
- `PvNP.FormulaDepthZeroBottom.fullDepthFrontierBottomLayer`: every surviving
  full-depth recursive frontier member is now packaged as an exact
  `GateSpec.dnf` with switching DNF width at most `1`, and the whole full-depth
  recursive frontier is collected as an audited bottom-layer list whose formulas
  match the frontier.  The module proves the depth-zero classification
  (constants or literals) and constructs exact DNF views for true, false, and
  literal formulas.  This supplies the terminal bottom layer for
  already-depth-zero frontier leaves, but it still does not assemble the
  recursive layers into a global B4 certificate or synthesize product/counting
  hypotheses.
- `PvNP.FormulaRecursiveDecomposition.fullDepthRecursiveDecomposition`: the
  recursive frontier is now packaged as an explicit decomposition skeleton.
  The package records every frontier level, the transition from level `k` to
  level `k+1` by expanding top children, the raw-depth budget at every level,
  and the terminal bottom layer from `FormulaDepthZeroBottom`.  This is the
  structural skeleton for B4, not full B4: intermediate efficient `GateSpec`
  layers, product/counting hypotheses, and a collapse schedule theorem remain
  open.
- `PvNP.FormulaRecursiveGateLayers.fullDepthRecursiveGateLayers`: every
  recursive frontier level is now reified as a `GateSpec.dnf` gate list with
  exact formula alignment, count alignment, and the honest truth-table
  fallback width bound `<= n`.  The terminal full-depth layer is still tied to
  the exact S2086 bottom layer whose gates have width at most one.  This
  exposes the next B4 gap precisely: efficient intermediate-width bounds,
  product/counting hypotheses, and a global collapse theorem are still open.
- `PvNP.FormulaRecursiveLayerProfile.frontierLayerGateCount`: the recursive
  gate-layer surface now has explicit per-level profile facts: gate-count
  alignment with the raw frontier, successor counts by top-child expansion and
  summed `topChildCount`, honest width budgets (`n` for intermediate
  truth-table layers, `1` for the terminal bottom layer), and per-layer
  constant tree budgets `m_k * (s - 1)`.  This is bookkeeping over the existing
  layers only; it still does not synthesize efficient widths, product/counting
  hypotheses, a schedule, or full B4.
- `PvNP.ScheduledCollapseDemo.scheduledThreeStage_budget3_nonvacuous`: one
  concrete scheduled instance — the schedule `[(3, 561), (2, 17), (1, 1)]`
  over `n = 10000` variables from one width-1 single-literal gate, with all
  six beat conditions proved by pure `Nat` arithmetic (stage-1/2 beats by
  symbolic `Nat.choose` ratio chains, stage-3 beats by direct small-number
  evaluation and positivity; no kernel evaluation of large binomials), yielding a
  certificate with stage gate counts `[1, 1, 1]`, budgets `[3, 2, 1]`, star
  counts `[561, 17, 1]`, `RefinesSeq`, a proved common total extension, and
  restricted-eval agreement.  The pinned STATEMENT records only these
  bookkeeping lists plus `RefinesSeq`, the extension, and the eval
  agreement; the counting-generation of the restrictions and the `nextLayer`
  re-viewing of stages 2/3 are properties of the constructed witness.  This
  is the artifact's first
  counting-beat-backed stage budget `s > 2` (the earlier
  `GeneratedCNFLayerStage` record in `GraphIndexedBridge` carries `s = 49`,
  but with a directly supplied good restriction for a constant leaf tree, not
  a counting beat).  One concrete finite demo instance, no asymptotic family;
  realized widths of the auto re-viewed stage-2/3 gates are BUDGET claims —
  only the start gate is syntactically pinned at realized width 1.

## Non-Claims Boundary

This artifact does **not** prove or imply:

- `P != NP` or `P = NP`;
- an NP or circuit lower bound;
- a Frege/PHP lower bound;
- a proved PHP decision-tree floor beyond the Lean-checked records listed
  above, such as the tiny `1 × 1` restricted view, the bounded `2 × 1` and
  `3 × 2` and parameterized `p × h` falsified-clause search floors, and the
  satisfiable `p = h` evasiveness/partial-matching family floors
  (`fullPHPBoundary_depthFloor`, `matchingBoundary_depthFloor`,
  `subsetSpace_depthFloor`);
- a positive Boolean decision-tree depth floor for the full `2 × 1` PHP formula
  (that formula is identically false, so a constant-false Boolean tree has depth
  `0`);
- any positive Boolean decision-tree depth floor for an unsatisfiable PHP formula
  merely from the bounded falsified-clause search floors;
- arbitrary AC0 or arbitrary bounded-depth formula collapse;
- arbitrary raw-formula synthesis from all `BDFormula` syntax: the
  formula-family synthesis covers only parent merges of embedded simple DNF/CNF
  children whose bottom-layer raw syntax is supplied, not a decomposition of
  general depth-`d` formulas into such layers;
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
- a PHP switching lemma: no collapse-probability upper bound for restricted
  formulas over the matching-restriction space is stated or proved (that
  rung of the general PHP depth-floor ladder remains open);
- a measure-theoretic probability measure, expectation, or
  with-high-probability theorem over restriction distributions: the
  `PHPMatchingDistribution`, `PHPFullMatchingDistribution`, and
  `PHPFullMatchingProbability` layers prove exact finite counting,
  cross-multiplied event-probability equalities/inequalities, and every-point
  floor transfer over identity-subset and square-permutation matching spaces
  only; rectangular `p > h` injection spaces are not formalized;
- a positive Boolean decision-tree depth floor for any unsatisfiable PHP
  formula (`p > h`): the proved evasiveness and partial-matching floors
  concern the satisfiable `p = h` function only;
- a discharge of the full frozen-form B4 goal: the artifact now has an
  explicit `FrozenDepthView` consumer theorem with a global final-tree budget
  `t(d,s) = gateCount * (s - 1)` for supplied views, now for both the fixed
  geometric schedule and arbitrary nonempty ratio-regime schedules, but it
  still does not automatically derive the upfront depth-`d` layered view from
  arbitrary `BDFormula`/AC0 syntax with efficient bottom width and does not
  internally derive a product-of-stages counting hypothesis `B(m, w, s, d)` for
  arbitrary formulas.  The `FormulaTruthTableView` fallback does synthesize
  exact top-connective views from raw `and`/`or` syntax, and the positive-depth
  wrappers expose that top constructor automatically for every non-leaf raw
  formula.  `FormulaDepthDecomposition` now proves that this top peel is a real
  one-step depth decrease for every exposed child, and
  `FormulaRecursiveDepth` proves the corresponding repeated-frontier raw-depth
  budget.  `FormulaDepthZeroBottom` adds exact width-one bottom `GateSpec.dnf`
  witnesses and an audited bottom-layer list for members that survive to the
  full-depth frontier.  `FormulaRecursiveDecomposition` packages every
  frontier level, the top-child transition, the depth budget, and the terminal
  bottom layer as one decomposition skeleton, but the recursive layers are not
  yet assembled into one global depth-`d`
  decomposition theorem and intermediate child DNF views outside that terminal
  frontier still come from full truth-table decision trees with only the generic
  width bound `<= n`.  The start view and geometric or ratio-regime entry
  hypotheses therefore remain supplied, syntactically exposed by the
  bottom-layer class, or satisfied only through this expensive fallback, and
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
  re-viewing property of an arbitrary witness (and the empty schedule yields
  the trivial `.done` certificate — content lives in nonempty schedules);
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
lake build PvNP
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

Version `v0.5.0` adds the opening rungs of the general-PHP-depth-floor ladder
and the Gate B generated-collapse routes.  This release opens the general-PHP-depth-floor ladder ("Gate A") with two proved rungs of satisfiable-PHP decision-tree floors plus the first increment of the rung-3 counting layer (at that release, only the identity-subset matching distribution was formalized). Rung 1 (`PvNP.PHPBooleanDepthFloor`): the satisfiable `h × h` pigeonhole Boolean function is evasive — every correct decision tree under the empty restriction has depth at least `h·h` (`fullPHPBoundary_depthFloor`), the first genuine family instance of `PHPDepthFloorStatement` beyond the trivial `1 × 1` boundary, with non-vacuity at depth `h·h + 1`. Rung 2 (`PvNP.PHPRestrictedDepthFloor`): the floor survives every fixed partial-matching restriction — the master theorem `matchingRestriction_depthFloor` gives depth at least the number of free variables, and the two-parameter family `matchingBoundary_depthFloor` instantiates the statement surface with floor `(h − s)·h` under genuinely nontrivial restriction families. Rung 3, first increment (`PvNP.PHPMatchingDistribution`): the uniform space of `s`-subset identity-matching restrictions with exact star counting — `star_ratio` (`h * choose (h−1) s = (h − s) * choose h s`, axioms `propext` only) is the exact counting form of "every variable is a star with probability `(h−s)/h`", the quantity switching-lemma arguments consume — plus probability-one transfer of the rung-2 floor to every point of the space (`subsetSpace_depthFloor`). The current post-v0.5.0 surface adds `PvNP.PHPFullMatchingDistribution`, the full square `h × h` permutation-matching space `subsetSpace h s × Equiv.Perm (Fin h)` with exact star counting and every-point floor transfer, plus `PvNP.PHPFullMatchingProbability`, an exact finite event-probability interface over that square space. Rectangular `p > h` injection spaces remain unformalized. These Gate A rungs are elementary sensitivity and finite-counting mathematics; no measure-theoretic probability, expectation theorem, or high-probability theorem is defined. The PHP switching lemma itself — collapse-probability upper bounds over the restriction space (Gate A rung 4) — remains OPEN, and none of this is a Frege/PHP proof-size bound, an NP/circuit bound, or a statement about P vs NP.

It also adds the Gate B generated-restriction ladder: B1/B2 counting-generated good restrictions with the explicit joint union bound and simultaneous collapse (`GeneratedGoodRestriction`), the shared-layer obstruction map with its intentionally nonempty machine-readable `openObligations` list (`GeneratedIteratedCollapse`), the B3 one-step generated depth reduction for supplied minimal layered views (`GeneratedOneStepDepthReduction`), first-wins restriction composition with consistent-subspace counting and the full-star-space closed form (`RestrictionComposition`), and the plan-supplied B4 route theorem `generatedIteratedCollapse` (`GeneratedIteratedCollapseFinal`), shipped with its satisfiability gap disclosed — the consistent-route stage beats compared full-space bad-set counts against consistent-subspace cardinalities, with no exhibited nonempty-gate multi-stage instance.  That gap is closed for the REFINEMENT ROUTE by the renormalized free-subcube counting: refinement subspaces with a closed-form cardinality (`RefinedSubspace`), support-injective relabel transport (`SwitchingRelabel`), the renormalized bad-set bound `badSetTerm_refines_card_le` and refined route theorem `generatedRefinedIteratedCollapse` (`GeneratedRefinedCollapse`), and the concrete depth-2, `n = 306`, width-budget-1 two-stage instance `refinedTwoStage_nonemptyGates_nonvacuous` (`RefinedTwoStageInstance`; realized stage-2 width is not certified).  Frozen-form B4 (single upfront depth-`d` layered view, product hypothesis `B(m, w, s, d)`, `t(d, s)` tree bound) remains open, and `GeneratedIteratedCollapse.openObligations` intentionally remains nonempty.

Finally it adds general decision-tree DNF/CNF re-viewing with depth-bounded width and built-in repeated-query pruning (`TreePathViews`), the automatic one-step next-layer scaffold from a generated one-step certificate (`AutoReviewedIteration.nextLayer` with its `originalFormula`/`gateCount`/`width` lemmas), and the schedule-driven automatic many-round collapse (`ScheduledAutoCollapse`, `ScheduledCollapseDemo`): from one supplied width-bounded start layer and a purely numeric budget/star-count schedule whose beat conditions hold as closed-form `Nat` arithmetic (`ValidFrom`), `autoIteratedCollapse` produces a `GeneratedRefinedIteratedCertificate` of the schedule's length — in the constructed witness every layer after the first is `nextLayer`-re-viewed automatically, while the pinned statement records only the bookkeeping lists (gate counts, budgets, star counts). The concrete schedule `[(3, 561), (2, 17), (1, 1)]` over `n = 10000` is proved non-vacuously (`scheduledThreeStage_budget3_nonvacuous`), the artifact's first counting-beat-backed stage budget `s > 2` (the earlier `GraphIndexedBridge` `s = 49` record used a directly supplied good restriction for a constant leaf tree, not a counting beat). The per-stage beats remain supplied arithmetic side conditions rather than a single product hypothesis; realized widths of auto re-viewed gates are budget claims; the budget-3 schedule is one concrete finite demo instance, not an asymptotic family; after any `s = 1` stage the schedule's tail degenerates to width-budget-0 stages with near-free beats, so schedule length alone is not a strength measure; frozen-form B4 and Gate A rung 4 remain open.

The formula-structural ratio-regime wrapper (`FormulaStructuralSchedule`) also
carries the supplied `FrozenDepthView` global tree budget through arbitrary
nonempty ratio-regime schedules and through positive-depth raw syntax after
top-constructor synthesis; the hypotheses remain supplied and this is not a
full B4 theorem.

The raw-formula depth-peel wrapper (`FormulaDepthDecomposition`) also proves
that the synthesized positive-depth top layer strictly decreases formula depth
on every exposed gate formula; this is still one-step structural peeling, not
full recursive B4 decomposition.

The recursive frontier wrapper (`FormulaRecursiveDepth`) extends that structural
bookkeeping across repeated top-child expansion: any surviving `k`-step
frontier member has spent `k` units of raw formula depth.  It still does not
construct recursive layered views, efficient bottom views, or product/counting
hypotheses.

The depth-zero bottom wrapper (`FormulaDepthZeroBottom`) gives exact simple DNF
views of width at most one for constants and literals, and packages each
full-depth recursive frontier member as a width-one-or-less `GateSpec.dnf`.
It also collects the full-depth frontier as an audited bottom-layer list whose
gate formulas match the frontier and whose gate widths are all at most one.
This is terminal-frontier bottom-layer synthesis only, not a global recursive
B4 decomposition theorem.

The recursive decomposition skeleton (`FormulaRecursiveDecomposition`) packages
all frontier levels, the level-to-level top-child transition, the raw-depth
budget, and the terminal bottom layer in one audited surface.  It is still a
structural skeleton only: efficient intermediate `GateSpec` layers,
product/counting hypotheses, and the global collapse theorem remain open.

The recursive frontier gate-layer wrapper (`FormulaRecursiveGateLayers`) reifies
every frontier level as a `GateSpec.dnf` list with formula and count alignment.
Intermediate widths are bounded only by the truth-table fallback `n`; the
terminal full-depth bottom layer remains the width-one-or-less layer.  This is
not efficient recursive B4 decomposition.

The recursive layer-profile wrapper (`FormulaRecursiveLayerProfile`) records
per-frontier gate counts, successor count transitions, the honest intermediate
and terminal width budgets, and per-layer constant tree-budget facts.  This is
still profile bookkeeping over truth-table fallback layers, not product/counting
synthesis or a generated collapse theorem.

The variable-width schedule wrapper (`FormulaVarWidthSchedule`) instantiates the
positive-depth raw-formula ratio-regime route at width `n`, using the proved
truth-table/path-DNF width bound instead of a caller-supplied child-width
predicate.  The ratio-regime schedule is still supplied, and `w = n` is not
efficient syntactic width control; this is not full B4.

The current audit surface has 789 `#guard_msgs`-pinned `#print axioms` profiles in `lean/PvNP/Audit.lean`; none of the pinned declarations depends on `sorryAx`, and every profile is within `propext`/`Classical.choice`/`Quot.sound`. One of the pins deliberately certifies OPENNESS rather than a theorem: `PvNP.GeneratedIteratedCollapse.openObligations_nonempty` pins the intentionally nonempty frozen-form Gate B obstruction map inside the audit surface. Frozen-form B4 and Gate A rung 4 (a PHP switching lemma) remain open.

- DOI: `10.5281/zenodo.21184992`
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.5.0`

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

- DOI: `10.5281/zenodo.21184612`
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
