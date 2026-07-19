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
- `PvNP.PHPFullMatchingCollapseBound.matchingCollapseBad_lit_probability_le`
  and `matchingCollapseBad_term_probability_le`: the first collapse-probability
  UPPER bounds over the full square matching space in this artifact.
  Containment of the
  depth-1 collapse-bad event in the star event(s) gives probability at most
  `(h−s)/h` for a single PHP literal and, via a finite list union bound, at
  most `w·(h−s)/h` for a single width-`w` conjunctive term (the empty term's
  bad event is exactly empty), all in exact cross-multiplied counting form,
  with strictly-below-one nonvacuous instances at `h = 3`, `s = 2`
  (`matchingCollapseBad_lit_three_two_strict` and
  `matchingCollapseBad_term_three_two_strict`).  These are depth-1
  single-literal/single-term events only: NOT a PHP switching lemma — these
  bounds supply no multi-term DNF bad-set bound, no compressed matching-space
  bad-set count, and no geometric depth-`t` `(8w)^s`-style bound
  over matchings.
- `PvNP.PHPFullMatchingCollapseExact.matchingCollapseBad_lit_probability_eq`:
  the single-literal bound is EXACT in this artifact.  The converse
  containment (`matchingCollapseBad_lit_of_fullStarEvent`, via two explicit
  agreeing assignments flipping the free variable under a depth-0 leaf)
  makes the depth-1 single-literal collapse-bad event pointwise EQUAL to the
  star event of its variable
  (`matchingCollapseBad_lit_iff_fullStarEvent`), so its probability is
  exactly `(h−s)/h` in cross-multiplied counting form, and at `h = 3`,
  `s = 2` the event count is positive
  (`matchingCollapseBad_lit_three_two_count_pos`), certifying the event is
  realized by actual points of the space.  Exactness covers ONLY the
  single-literal event: the single-term union bound remains an inequality
  (a term with a literal fixed to false collapses to a leaf even when its
  other variables are free), and this is still NOT a PHP switching lemma —
  exactness supplies no multi-term DNF bad-set bound, no compressed
  matching-space bad-set count, and no geometric depth-`t` `(8w)^s`-style
  bound over matchings.
- `PvNP.PHPFullMatchingDNFBound.matchingCollapseBad_dnf_probability_le`: the
  first multi-term DNF depth-1 bad-set bound over the matching space in this
  artifact.  A simple DNF `phpDNFFormula h tvs` (an `or` of conjunctive
  terms over PHP variables) fails to collapse to depth `0` with probability
  at most `|tvs.join|·(h−s)/h` — a union bound over ALL literal occurrences
  (`exists_fullStarEvent_of_matchingCollapseBad_dnf`), linear in TOTAL DNF
  size with duplicates counted, NOT the switching-lemma regime.  The
  degenerate shapes are theorems (the empty DNF and any DNF containing an
  empty term have exactly empty bad events), and a two-term instance at
  `h = 3`, `s = 2` gives `2/3 < 1` over a nonempty space
  (`matchingCollapseBad_dnf_three_two_strict`).  Depth-1 collapse-bad means
  only "the restricted DNF fails to be constant": this union bound supplies
  no compressed matching-space bad-set count (the coarse compressed count
  arrives only in `PHPFullMatchingPathCodeFiberBound`) and no geometric
  term-count-independent depth-`t` `(8w)^s`-style collapse-probability
  bound; Gate A rung 4 as a whole remains open.
- `PvNP.PHPFullMatchingCanonicalDT.canonicalRestrictedDNFTree_correct`:
  deterministic restricted-DNF canonical decision-tree skeleton over the full
  square matching space.  `phpDNFAsDNF` translates the PHP DNF list format to
  the generic DNF representation; `canonicalRestrictedDNFTree h tvs P` is the
  term-canonical tree of that DNF after `fullRestrictionOf P`;
  `treeVarsIn_canonicalRestrictedDNFTree` keeps every decision-node variable
  inside the original PHP DNF variable set; and
  `canonicalRestrictedDNFTree_depth_le_total` /
  `canonicalRestrictedDNFTree_path_length_le_total` bound deterministic
  worst-case depth and assignment-path query count by `tvs.join.length`.
  This is representation and structural infrastructure only: it supplies no
  compressed bad-set count of its own, no geometric collapse-probability
  bound, and no rectangular `p > h` injection-space result.
- `PvNP.PHPFullMatchingBadPathEncoding.canonicalDepthBad_count_le_space_mul_optional_pathCode`:
  the first conservative bad-path encoding/counting theorem for
  `canonicalRestrictedDNFTree` over `fullMatchingSpace`.  A depth-`t` bad
  matching point carries a certified `BadPathCode` consisting of `t`
  deepest-path query/direction pairs, with queries in `phpDNFVarSet h tvs`
  (`deepestPath_treeVarsIn`, `canonicalDepthBad_pathCode_exists`), and the
  filtered bad event has cardinality at most the matching-space cardinality
  times the optional path-code count.  This encoder deliberately keeps the
  original matching point as its first coordinate, so it is not a geometric
  compression, not a switching lemma, and not a collapse-probability
  improvement.
- `PvNP.PHPFullMatchingCompressedBadPathCount.canonicalDepthBad_freePathCode_exists`,
  `fullRowsFree_count`, and
  `canonicalDepthBad_count_le_target_mul_pathCode_of_injOn`: the first
  compressed-count scaffold after the conservative bad-path count.  The module
  proves that variables surviving DNF restriction, variables queried by
  `canonicalRestrictedDNFTree`, and variables on its deepest path are free under
  the concrete `fullRestrictionOf P`, then packages every depth-`t` bad point
  with a `P`-dependent free-certified path code.  It also gives the exact count
  of full matching points leaving any specified row set free,
  `choose (h - rows.card) s * |Equiv.Perm (Fin h)|`, as row-level
  multiplicity infrastructure.  The compressed bad-event count theorem is only
  conditional: if later work supplies a genuine compressed target and an
  injective encoder into that target paired with `BadPathCode`, the bad-event
  count follows.  It does not construct that encoder, prove a path-code fiber
  bound, prove a geometric probability bound, or prove a PHP switching lemma.
- `PvNP.PHPFullMatchingPathCodeFiberBound.canonicalDepthBad_fiber_count_le`,
  `canonicalDepthBad_count_le_pathCode_mul_rowFree`, and
  `canonicalDepthBad_ratio_le`: the shared path-code fiber bound — the first
  compressed bad-set count in this artifact over `fullMatchingSpace` whose
  encoder does NOT retain the original matching point.  Bad matching points
  are grouped by their deepest-path code, drawn from a `P`-independent code
  space; every point in a code's fiber
  leaves that code's touched pigeon rows (`codeRows`, nonempty for positive
  code length by `codeRows_nonempty`) free, so each fiber has at most
  `choose (h - |codeRows c|) s * h!` points by `fullRowsFree_count`.  Summing
  over codes gives, for `1 <= t`,
  `eventCount <= card (BadPathCode) * (choose (h-1) s * h!)` and its
  cross-multiplied ratio form via `star_ratio_full`.  At `h = 3`, `s = 2`,
  `t = 1` with the single-literal (support-1) demo DNF, the bound `12` is
  strictly below the space size `18` over a
  nonempty bad event (`card_badPathCode_demo`, `demo_bound_lt_space`,
  `demo_bad_count_pos`).  The path-code space is still the coarse
  support-based code space and only ONE guaranteed free row is exploited:
  this is not a geometric `(8w)^s`-style bound, not a depth-`t`
  canonical decision-tree encoding argument with per-stage information
  recovery, and not a PHP switching lemma.
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
  bound `|badSetTerm D s ℓ ∩ refinesSubspace base ℓ| ≤ |R(stars base, ℓ−s)| · (4w)^s`,
  proved by transporting along the free-subcube relabeling and instantiating
  the proved SimpleDNF switching lemma at dimension `stars base`, together
  with the refined plan/certificate machinery whose stage restrictions REFINE
  the accumulated base.  This closes the disclosed B4-route satisfiability gap
  FOR THE REFINEMENT ROUTE only; merely-consistent-subspace-relative counting
  is still not provided, and frozen-form B4 remains open.
- `PvNP.RefinedTwoStageInstance.refinedTwoStage_nonemptyGates_nonvacuous` with
  `depthOneDNFView`: one concrete depth-2 renormalized plan over `n = 306`
  with a nonempty gate LIST, width BUDGET `1`, and the non-degenerate
  `(4·1)^s` beat factor at BOTH stages (stage-1 beat
  `64 · C(306,15) < C(306,17)`, proved symbolically; stage-2 beat
  `2^18 < 17 · 2^16`).  The stage-2 gate re-views the stage-1 GENERATED
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
- `PvNP.FormulaRecursiveGlobalSchedule.frontierLayer_autoIteratedCollapse_of_globalProductBeats`
  and
  `PvNP.FormulaRecursiveGlobalSchedule.terminalLayer_autoIteratedCollapse_of_globalProductBeats`:
  synthesized recursive frontier layers and the terminal full-depth bottom
  layer can now feed the existing frozen-product schedule theorem under one
  formula-wide max-frontier budget
  `recursiveFrontierGlobalTreeBudget F d s =
  recursiveFrontierMaxGateCount F * (s - 1)`.  Product/counting beats remain
  supplied as `ProductValidFrom`, and the intermediate width budget remains the
  truth-table fallback `n`; this advances the structural B4 interface but is
  not an efficient asymptotic `t(d,s)` theorem or full B4.
- `PvNP.FormulaRecursiveMaxProduct.frontierLayer_autoIteratedCollapse_of_maxProductBeats`
  and
  `PvNP.FormulaRecursiveMaxProduct.allFrontierLayers_autoIteratedCollapse_of_maxProductBeats`:
  one product schedule supplied at the formula's max recursive frontier count
  can be frozen and reused for any in-depth recursive frontier layer.  This
  removes a layer-local product-beat obligation for the truth-table fallback
  frontier layers, while leaving the product/counting beat theorem itself
  supplied and leaving the formula-local max-frontier budget short of an
  efficient asymptotic `t(d,s)` theorem.
- `PvNP.FormulaRecursiveRatioSchedule.frontierLayer_ratioRegimeCollapseWithGlobalTreeBudget`
  and
  `PvNP.FormulaRecursiveRatioSchedule.terminalLayer_geometricCollapseWithGlobalTreeBudget`:
  synthesized recursive frontier and terminal layers can now consume
  ratio-regime schedules under the same formula-local global tree budget.  The
  ratio-regime route proves the per-stage arithmetic beats from the supplied
  regime, and the geometric terminal/frontier corollaries generate the named
  geometric schedule under explicit entry-size inequalities.  Intermediate
  layers still use truth-table fallback width `n`, nonempty gate counts remain
  explicit hypotheses, and this is not full B4 or an efficient asymptotic
  `t(d,s)` theorem.
- `PvNP.FormulaRecursiveWidthSchedule.frontierLayer_ratioRegimeCollapseWithWidthProfile`
  and
  `PvNP.FormulaRecursiveWidthSchedule.allFrontierLayers_geometricCollapseWithWidthProfile`:
  recursive frontier layers can now consume supplied per-level width profiles
  instead of hard-coding the intermediate truth-table fallback width `n`.  The
  profile is supplied, nonempty layer counts and ratio/geometric schedule
  hypotheses remain explicit, and the formula-local max-frontier tree budget is
  unchanged.  This is a B4 interface hook for later efficient width synthesis,
  not efficient B4, not a global asymptotic `t(d,s)` theorem, and not a PHP
  switching lemma.
- `PvNP.FormulaRecursiveNonempty.frontierLayerGateCount_nonempty_of_noEmptyFanins`
  and
  `PvNP.FormulaRecursiveNonempty.allFrontierLayers_geometricCollapseWithWidthProfile_noEmptyFanins`:
  raw formulas whose `and`/`or` gates all have nonempty fan-in now synthesize
  nonempty recursive frontier gate counts for every level `k <= depth F`, and
  the supplied-width ratio/geometric consumers use that fact instead of a
  caller-supplied `hm` count hypothesis.  Width profiles, schedule regimes,
  entry-size inequalities, and the formula-local max-frontier tree budget
  remain supplied or local; this is not efficient B4, not a global asymptotic
  `t(d,s)` theorem, and not a PHP switching lemma.
- `PvNP.FormulaRecursiveSizeBound.frontierLayerGateCount_le_formulaSize` and
  `PvNP.FormulaRecursiveSizeBound.recursiveFrontierMaxGateCount_le_formulaSize`:
  every recursive frontier layer count, and the max-frontier count used by the
  recursive global schedule interface, is bounded by the raw formula size
  `formulaSize F`.  The companion `recursiveFrontierSizeTreeBudgetFrom` theorem
  exposes the structural size-based budget `formulaSize F * (s - 1)` through
  the existing `TreeBudgetFrom` interface.  This advances the B4
  structural-budget route but still does not synthesize efficient widths,
  product/counting hypotheses, ratio regimes, a formula-class asymptotic
  `t(d,s)`, or a PHP switching lemma.
- `PvNP.FormulaSyntacticDNF.eval_syntacticDNF` and
  `PvNP.FormulaSyntacticDNF.widthDNF_syntacticDNF_le_formulaSize`: every raw
  `BDFormula` now has a syntactic DNF expansion with exact Boolean semantics and
  term width bounded by `formulaSize F`.  The packaged
  `syntacticDNFView` still requires a supplied `SimpleDNF (syntacticDNF F)`
  proof because this module does not normalize repeated variables or
  contradictory terms.  The DNF can be exponentially large, and this is
  structural width control only: no product/counting synthesis, efficient
  global `t(d,s)`, full B4 theorem, or PHP switching lemma is proved.
- `PvNP.FormulaSyntacticSimpleBridge.simpleDNF_syntacticDNF_of_simple` and
  `PvNP.FormulaSyntacticSimpleBridge.syntacticFormula_switching_bridge`:
  a sufficient structural predicate now synthesizes the `SimpleDNF` evidence
  needed to package a raw formula's syntactic DNF view, and routes those
  structurally certified formulas through the proved simple-DNF switching
  bridge with formula-size width control.  The predicate is sufficient but not
  complete; it does not normalize arbitrary formulas, and the resulting bad-set
  statement remains over `badSetTerm (syntacticDNF F)`, not a full depth-`d`
  B4 decomposition or a PHP switching lemma.
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
- arbitrary raw-formula synthesis from all `BDFormula` syntax into full
  generated-collapse inputs: the formula-family synthesis covers only parent
  merges of embedded simple DNF/CNF children whose bottom-layer raw syntax is
  supplied, and `FormulaSyntacticDNF` gives a semantic DNF expansion for every
  raw formula, while `FormulaSyntacticSimpleBridge` supplies the packaged
  `DNFView` simplicity proof only for a structurally certified sufficient
  subclass; neither is a decomposition of general depth-`d` formulas into
  efficient generated-collapse layers;
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
- a PHP switching lemma: beyond the depth-1 single-literal and
  single-conjunctive-term collapse bounds of `PHPFullMatchingCollapseBound`
  (made exact for the single-literal event in
  `PHPFullMatchingCollapseExact`) and the depth-1 multi-term DNF total-size
  union bound of `PHPFullMatchingDNFBound`, plus the deterministic restricted
  DNF canonical-tree skeleton of `PHPFullMatchingCanonicalDT`, plus the
  conservative optional-code bad-path count of
  `PHPFullMatchingBadPathEncoding`, plus the free-variable, row-level
  multiplicity, and conditional compressed-target scaffold of
  `PHPFullMatchingCompressedBadPathCount`, plus the shared path-code fiber
  bound and coarse compressed count of `PHPFullMatchingPathCodeFiberBound`
  (the first count in this artifact whose encoder forgets the matching point,
  but which uses the coarse support-based code space, exploits only one
  guaranteed free row, and in relative form is
  `(2 * |support|)^t * (h - s) / h` of the space size — weakening as `t`
  grows rather than strengthening geometrically),
  no collapse-probability upper bound for restricted formulas over the
  matching-restriction space is stated or proved — in particular no
  multi-term DNF bad-set bound beyond the depth-1 total-size union bound of
  `PHPFullMatchingDNFBound` and the coarse path-code count above, no
  geometric `(8w)^s`-style depth-`t` collapse-probability bound
  (term-count-independent) over matchings, and no depth-`t` canonical
  decision-tree encoding argument with per-stage information recovery (that
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
  width bound `<= n`, unless one separately supplies the simplicity condition
  needed to use the new syntactic DNF expansion whose width is bounded by
  `formulaSize F`.  The start view and geometric or ratio-regime entry
  hypotheses therefore remain supplied, syntactically exposed by the
  bottom-layer class, conditionally available through syntactic DNF simplicity,
  or satisfied only through this expensive fallback, and
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

Version `v0.9.0` publishes the post-`v0.8.0` Gate B coefficient-lane and
frozen-form stack S2175-S2183 under unchanged `t(d,s)=S(d)*(s-1)`.  S2175 adds
the affine headroom beat (`ratio_beat_affine`, `(16*m*w+1)*l <= p`,
coefficient-17 packaging, ambient `9826`).  S2176 threads the exact factor-4
`(4*w)^s` `RCode` cardinality through the real consumer path (`ratio_beat4`,
`geometricSchedule16`, ambient `8192`).  S2177 adds Route A-sharp coefficient
9 (`ratio_beat9` packaging the exact affine fold `(8*m*w+1)*l <= p`;
`geometricSchedule9`; ambient `1458 = 2*9^2*9`, the exact minimum for the
three-stage schedule; 9 is the floor of the multiplicative packaging family).
S2179 adds multi-round uniform-9 packages at ambients `13122` (rounds 3) and
`118098` (rounds 4) and closes the free multiplicative coefficient lane
(Route B factor-2 parked behind new encode mathematics).  S2180 adds the
hypothesis-free frontier count recurrence (`formulaRecurrenceCount`; raw <=
recurrence <= size for every raw formula).  S2181 adds the frozen-form B4 v1
class wrapper `frozenFormB4_v1_allLevels_uniform9` (class-level only; full
frozen-payload B4 remains open): for every nonempty-fanin
raw formula, under a single syntax-only coarse Entry product, every depth
level carries the synthesized-dedup uniform-9 final-tree payload (width and
count schedules, `S`, and `d` synthesized; only merge parent, round count,
and ambient remain free).  S2182 adds the strong structural non-vacuity
witness `twinCubeWitness9 : BDFormula 23328` (synthesized dedup count 2 and
normalized width 2 at the unique binding level, welded to
`levelEntryProduct9 = 23328`; `dupCubeWitness11` kernel-checked to admit no
such level) and the first through-the-hypothesis wrapper instantiation at
ambient `73811250`.  S2183 threads the count recurrence into the Entry
(`frozenFormEntryProduct9Rec`, never exceeding the size-coarse Entry, with a
same-witness strict separation at ambient `11197440`; the recurrence charges
leaf mass only and is not sharing-aware).  The audit surface has `1810`
`#guard_msgs`-pinned `#print axioms` profiles.  Boundary: class-level
iterated collapse for the restricted nonempty-fanin normalized-view/dedup
route and bounded schedule-entry arithmetic only; packaging witnesses are
structural schedule non-degeneracy, **not** switching non-vacuity; not full
frozen-payload B4 beyond the named class, not a PHP switching lemma, not
Frege/PHP, NP/circuit, arbitrary AC0 collapse, Gate A revival, or P-vs-NP.

- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.9.0`
- Zenodo version DOI: `10.5281/zenodo.21408241`
  (concept DOI remains `10.5281/zenodo.20757627`)

Version `v0.8.0` publishes the post-`v0.7.0` Gate B 32-route stack S2162-S2172
under unchanged `t(d,s)=S(d)*(s-1)`.  S2162-S2163 add DNF normalization and
normalized-view tight-entry consumers.  S2164-S2166 add hypothesis-free
recurrence width, frontier-local width schedules, and actual
normalized-frontier DNF width schedules.  S2167-S2169 add representative
frontier layers and automatic `dedupRepresentativeFrontier` synthesis (module-
local decidable syntactic equality; consumers synthesize layer lists,
membership proofs, and count obligations).  S2170 rebalances geometric entry
stars to `n/(32*m*w)` with product `2*(64*m)^k*(32*m*w)`.  S2171 adds the
parallel uniform-32 schedule `geometricSchedule32` (stage divisor `32*m`) with
product `2*(32*m)^k*(32*m*w)`.  S2172 packages zero-hypothesis all-level
final-tree instances on the uniform-32 synthesized-dedup route at ambients
`2^16` (rounds 2), `2^21` (rounds 3), and `2^26` (rounds 4).  The audit
surface has `1704` `#guard_msgs`-pinned `#print axioms` profiles.  Boundary:
restricted nonempty-fanin normalized-view route and schedule-entry arithmetic
within the existing ratio coefficient 32 only; single finite concrete
instances; not switching redesign below 32, full B4, PHP switching, Frege/PHP,
NP/circuit, arbitrary-class width synthesis, Gate A revival, or P-vs-NP.

- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.8.0`
- Zenodo version DOI: pending GitHub/Zenodo archive after tag publication
  (concept DOI remains `10.5281/zenodo.20757627`)

Version `v0.7.0` publishes the post-`v0.6.0` Gate B increments S2158-S2161.
S2158 adds the disjoint-support AND-compatibility synthesis class
(`FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget`):
pairwise-disjoint child variable supports plus child simplicity provably
synthesize `syntacticAndListSimpleDNF`, so AND nodes carry only a purely
syntactic disjointness condition instead of a constructor-carried
compatibility Prop, with an embedding into the S2157 recurrence-width class
and inherited supplied-width final-tree routing.  S2160 adds the first
numerically-discharged unconditional final-tree instances
(`...DisjointSupportUnconditionalInstance`): the coarse ambient threshold is
discharged by `decide` on `Nat` literals at fixed ambients `2^22`
(`rounds = 1`) and `2^31` (`rounds = 2`) for an AND-bearing
recurrence-width-2 witness, yielding `SuppliedWidthClassDepthFinalTreeAt`
payloads with zero open side conditions (the S2155/S2156 nested-OR packed
families already gave zero-hypothesis instances via threshold-defined
ambient arity; the numeric discharge at independently chosen ambients and
the recurrence-width route are the new content).  S2161 adds frontier-local
tight-entry consumers (`...DisjointSupportTightEntry`): the ambient
obligation becomes the layer-local
`2*(64*count)^rounds*(64*count*W) <= n` instead of the coarse
`S(d)`-inflated threshold, with subsumption lemmas re-deriving the coarse
route, and zero-hypothesis instances at `2^20` (`rounds = 2`), `2^26`
(`rounds = 3`, plus all levels at `rounds = 2`), and `2^32` (`rounds = 4`),
each strictly dominating an S2160 instance; coarse-entry-failure pins
document that the class-size-7 coarse threshold fails at every instantiated
pair.  The audit surface has `1452` `#guard_msgs`-pinned `#print axioms`
profiles.  Boundary: restricted classes and single finite concrete
instances only; a tighter entry condition, not a change to switching-lemma
constants, budgets, schedules, or payloads; shared-variable ANDs still
require a supplied compatibility proof; no PHP switching lemma, full B4,
Frege/PHP, NP/circuit, arbitrary-class width synthesis, Gate A revival, or
P-vs-NP.

- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.7.0`
- Zenodo version DOI: pending GitHub/Zenodo archive after tag publication
  (concept DOI remains `10.5281/zenodo.20757627`)

Version `v0.6.0` publishes the post-`v0.5.0` Gate A and Gate B formal stack
through S2157.  Gate A adds realized-code counting, row-variable uniqueness
diagnostics, row-collision splits, parametric and rectangular obstructions, and
the current SimpleDNF row-collision denominator-route no-go package
(`PHPFullMatchingGateANoGoAfterS2139`).  Gate B adds terminal-aware and
syntactic-terminal class envelopes, packed-family sources, ambient adequacy and
small-arity obstruction packages, efficient and tight width budgets, recursive
nested-OR families, the restricted nonempty OR-only class
(`FormulaRecursiveSyntacticTerminalBoundedShallowOrOnlyTightBudget`) with
width-one frontier closure and supplied-width final-tree routing under
unchanged `t(d,s)=S(d)*(s-1)`, and the restricted nonempty OR/AND
recurrence-width class
(`FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget`)
with max-OR/sum-AND recurrence width, frontier closure, and supplied-width
final-tree routing at `W = max 1 (formulaRecurrenceWidth F)` under the same
unchanged budget.  The current audit surface has `1354`
`#guard_msgs`-pinned `#print axioms` profiles.  Boundary: finite named Gate A
witnesses and restricted Gate B classes/families only; no PHP switching lemma,
full B4, Frege/PHP, NP/circuit, arbitrary-class width synthesis, or P-vs-NP.

- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.6.0`
- Zenodo version DOI: pending GitHub/Zenodo archive after tag publication
  (concept DOI remains `10.5281/zenodo.20757627`)

Version `v0.5.0` adds the opening rungs of the general-PHP-depth-floor ladder
and the Gate B generated-collapse routes.  This release opens the general-PHP-depth-floor ladder ("Gate A") with two proved rungs of satisfiable-PHP decision-tree floors plus the first increment of the rung-3 counting layer (at that release, only the identity-subset matching distribution was formalized). Rung 1 (`PvNP.PHPBooleanDepthFloor`): the satisfiable `h × h` pigeonhole Boolean function is evasive — every correct decision tree under the empty restriction has depth at least `h·h` (`fullPHPBoundary_depthFloor`), the first genuine family instance of `PHPDepthFloorStatement` beyond the trivial `1 × 1` boundary, with non-vacuity at depth `h·h + 1`. Rung 2 (`PvNP.PHPRestrictedDepthFloor`): the floor survives every fixed partial-matching restriction — the master theorem `matchingRestriction_depthFloor` gives depth at least the number of free variables, and the two-parameter family `matchingBoundary_depthFloor` instantiates the statement surface with floor `(h − s)·h` under genuinely nontrivial restriction families. Rung 3, first increment (`PvNP.PHPMatchingDistribution`): the uniform space of `s`-subset identity-matching restrictions with exact star counting — `star_ratio` (`h * choose (h−1) s = (h − s) * choose h s`, axioms `propext` only) is the exact counting form of "every variable is a star with probability `(h−s)/h`", the quantity switching-lemma arguments consume — plus probability-one transfer of the rung-2 floor to every point of the space (`subsetSpace_depthFloor`). The current post-v0.5.0 surface adds `PvNP.PHPFullMatchingDistribution`, the full square `h × h` permutation-matching space `subsetSpace h s × Equiv.Perm (Fin h)` with exact star counting and every-point floor transfer, plus `PvNP.PHPFullMatchingProbability`, an exact finite event-probability interface over that square space, plus `PvNP.PHPFullMatchingCollapseBound`, the first depth-1 single-literal and single-conjunctive-term collapse-probability upper bounds over that space, plus `PvNP.PHPFullMatchingDNFBound`, the depth-1 multi-term DNF total-size union bound over that space, plus `PvNP.PHPFullMatchingCanonicalDT`, the deterministic restricted-DNF canonical-tree skeleton over that space, plus `PvNP.PHPFullMatchingBadPathEncoding`, the conservative optional-code bad-path count over that space. Rectangular `p > h` injection spaces remain unformalized. These Gate A rungs are elementary sensitivity, deterministic tree, and finite-counting mathematics; no measure-theoretic probability, expectation theorem, or high-probability theorem is defined. The PHP switching lemma itself (Gate A rung 4 as a whole) remains OPEN: beyond those depth-1 literal/term/DNF events, the deterministic canonical-tree skeleton, and the conservative optional-code count, there is no multi-term DNF bad-set bound beyond the depth-1 total-size union bound, no compressed matching-space bad-set encoding/counting theorem beyond the later coarse S2121 path-code fiber count described below, and no geometric term-count-independent depth-`t` collapse-probability bound over matchings, and none of this is a Frege/PHP proof-size bound, an NP/circuit bound, or a statement about P vs NP.

Post-v0.5.0 S2120 also adds `PvNP.PHPFullMatchingCompressedBadPathCount`,
which proves free-variable certification for restricted DNF survivors and
canonical restricted-DNF tree paths, an exact row-level free-set count
`fullRowsFree_count`, and a conditional compressed-target count theorem.  This
is still only scaffold infrastructure: no compressed encoder, path-code
fiber/multiplicity theorem, geometric collapse-probability bound, PHP switching
lemma, Frege/PHP lower bound, NP/circuit lower bound, or P-vs-NP claim is
proved in that module — the path-code fiber bound and coarse compressed count
arrive in S2121 below; the geometric matching-space bound, PHP switching
lemma, Frege/PHP, NP/circuit, and P-vs-NP items remain unproved everywhere in
this artifact.

Post-v0.5.0 S2121 adds `PvNP.PHPFullMatchingPathCodeFiberBound`, the shared
path-code fiber bound: the first compressed bad-path count in this artifact
over the full square matching space whose encoder does not retain the
original matching point.  Bad points are grouped by their deepest-path code,
drawn from a `P`-independent code space, each code fiber is bounded by the
row-free multiplicity of the code's touched rows, and the headline count
(for `1 <= t`) is
`card (BadPathCode) * (choose (h-1) s * h!)`, strictly below the space size
at the nonempty `h = 3`, `s = 2`, `t = 1` demo instance with the
single-literal (support-1) demo DNF.  The count is still
coarse — support-based code space, one guaranteed free row — so no geometric
`(8w)^s`-style bound, no per-stage information-recovery encoding argument, no
PHP switching lemma, no rectangular `p > h` space, and no Frege/PHP,
NP/circuit, or P-vs-NP claim is proved.  In relative form the headline bound
is `(2 * |support|)^t * (h - s) / h` times the space size, so it improves on
the trivial full-space bound only when the star fraction is below
`(2 * |support|)^(-t)`; it weakens as `t` grows, whereas a switching lemma
must strengthen geometrically in `t`.

Post-v0.5.0 S2122 adds `PvNP.PHPFullMatchingStageRows`, a bounded
stage-indexed recovery increment for the same finite full square matching
space.  Each bad-path-code stage is decoded to the PHP row/column occurrence
whose variable is stored in the code; every recovered stage row is proved free
for any bad point in the corresponding code fiber; and the bad event is bounded
by the sum of row-free multiplicities using the full set of recovered stage
rows.  A conditional coarsening theorem turns any separately proved lower bound
`q <= (codeStageRows c).card` into the uniform `choose (h-q) s * h!` factor,
and S2124 adds a realized-code-only refinement where that `q`-row lower bound is
required only for codes whose canonical bad-path fiber is nonempty.  These
theorems do not prove realized row growth, distinct recovered rows, `q = t`, a
geometric-in-`t` switching lemma, rectangular `p > h` injection-space theorem,
Frege/PHP lower bound, NP/circuit lower bound, or P-vs-NP claim.

Post-v0.5.0 S2123 adds `PvNP.PHPFullMatchingStageRowObstruction`, a bounded
follow-up for the same finite code-space/matching-space surface.  It proves the
safe one-row lower bound for positive-length codes (`codeStageRows_nonempty`,
`one_le_codeStageRows_card`) and an injective-stage-row conditional
(`codeStageRows_card_eq_of_injective`).  It also isolates the current-definition
obstruction: at `h = 1`, `t = 2`, over the one-literal support
`[[((0 : Fin 1), (0 : Fin 1), true)]]`, a duplicate-stage code maps both stages
to `phpVar 1 1 0 0`, has `(codeStageRows c).card = 1`, and refutes a global
two-row lower bound for all `BadPathCode`s over that support.  This does not
prove distinct rows for all codes, `q = t`, geometric decay, a PHP switching
lemma, rectangular `p > h`, Frege/PHP, NP/circuit, or P-vs-NP.

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

The recursive global-schedule wrapper (`FormulaRecursiveGlobalSchedule`) adds a
single formula-wide max-frontier tree budget over the recursive layer profile,
proves every in-depth frontier gate count is below that maximum, and routes the
synthesized frontier and terminal layers through the frozen-product schedule
consumer from supplied `ProductValidFrom` beats.  The resulting `t_F` is a
formula-local structural budget, not an efficient asymptotic B4 `t(d,s)` bound.

The recursive max-product wrapper (`FormulaRecursiveMaxProduct`) freezes a
supplied product-bound family at `recursiveFrontierMaxGateCount F` and proves
that the frozen product schedule applies to every smaller recursive frontier
layer count.  This reduces the product-beat interface from per-frontier counts
to one max-count schedule for truth-table fallback frontier layers, but it
still does not synthesize the product/counting beats or an efficient global
`t(d,s)`.

The recursive ratio-schedule wrapper (`FormulaRecursiveRatioSchedule`) lets
synthesized recursive frontier and terminal layers consume supplied
ratio-regime schedules under the same formula-local global tree budget; its
geometric corollaries generate the named ratio schedule under explicit
entry-size inequalities.  Nonempty layer counts remain hypotheses, intermediate
width remains truth-table fallback `n`, and this is not efficient recursive B4.

The recursive width-schedule wrapper (`FormulaRecursiveWidthSchedule`) adds a
supplied per-level width profile for recursive frontier layers and reroutes the
ratio/geometric consumers through that profile.  This creates the theorem hook
needed for later efficient structural width synthesis, while still leaving the
profile, nonempty counts, schedule regime, and formula-local tree budget
explicit.

The recursive nonempty wrapper (`FormulaRecursiveNonempty`) adds the structural
predicate `NoEmptyFanins` and proves that it supplies nonempty recursive
frontier gate counts for all levels `k <= depth F`.  Its ratio/geometric
corollaries remove the caller-supplied nonempty-count hypothesis from the
supplied-width route under that raw-syntax condition, but width profiles,
entry-size bounds, and efficient global B4 structure remain open.

The recursive size-bound wrapper (`FormulaRecursiveSizeBound`) proves that
every recursive frontier layer count and the formula-wide max-frontier count
are bounded by `formulaSize F`, then exposes the structural size budget
`formulaSize F * (s - 1)` through `TreeBudgetFrom`.  This replaces the
max-frontier budget by a formula-size bound for the recursive count surface,
but it is still not the final formula-class asymptotic `t(d,s)` theorem and
does not synthesize efficient widths or product/counting hypotheses.

The syntactic DNF wrapper (`FormulaSyntacticDNF`) gives every raw formula a
semantic syntactic DNF expansion and proves its width is at most
`formulaSize F`.  The packaged `DNFView` still requires a supplied
`SimpleDNF (syntacticDNF F)` proof; no normalization, product/counting
synthesis, efficient global `t(d,s)`, full B4 theorem, or PHP switching lemma
is proved.

The structural syntactic-DNF bridge (`FormulaSyntacticSimpleBridge`) defines a
sufficient raw-syntax predicate for syntactic DNF simplicity, packages certified
formulas as `DNFView`s, and inherits the proved simple-DNF switching bridge with
formula-size width control.  This removes the supplied simplicity premise only
for that certified subclass; arbitrary normalization, efficient depth-`d`
recursive decomposition, product/counting synthesis, and Gate A rung 4 remain
open.

The recursive syntactic frontier layer (`FormulaRecursiveSyntacticLayer`)
packages structurally certified frontier formulas as `GateSpec.dnf` children
through their syntactic DNF views, proves every child width is bounded by
`formulaSize F`, and routes the existing ratio/geometric recursive consumers
through the size-based tree budget at that formula-size width.  The per-frontier
syntactic simplicity predicate, ratio regime, nonempty counts, and entry-size
bounds are still supplied; this is not arbitrary normalization, full B4, or the
global depth-`d` `t(d,s)` theorem.

The syntactic frontier nonempty wrapper
(`FormulaRecursiveSyntacticNonempty`) composes that formula-size frontier route
with the existing `NoEmptyFanins` syntax predicate, discharging the nonempty
gate-count hypothesis for single-level and all-level ratio/geometric consumers.
The frontier simplicity predicate, ratio/geometric hypotheses, product/counting
synthesis, and global depth-`d` `t(d,s)` theorem remain open.

The recursive syntactic-simple wrapper (`FormulaRecursiveSyntacticSimple`)
proves that the root structural predicate `syntacticFormulaSimpleDNF F`
propagates along every recursive `topChildren` frontier, synthesizing
`FrontierSyntacticSimple F level` for all levels.  It exposes formula-size
ratio/geometric consumers that no longer need per-frontier simplicity
hypotheses, plus no-empty variants that also discharge nonempty-count
hypotheses under `NoEmptyFanins F`.  The root structural predicate,
ratio/geometric hypotheses, product/counting synthesis, arbitrary
normalization, full B4, and global depth-`d` `t(d,s)` theorem remain open.

The syntactic geometric wrapper (`FormulaRecursiveSyntacticGeometric`) removes
the per-level geometric entry-size inequality for the root-simple/no-empty
syntactic frontier route.  It proves that
`frontierLayerGateCount F level <= formulaSize F` turns one formula-size
ambient bound
`2 * (64 * formulaSize F)^rounds * (64 * formulaSize F * formulaSize F) <= n`
into the geometric entry bound for every recursive frontier level, and exposes
a single all-level consumer under `syntacticFormulaSimpleDNF F` plus
`NoEmptyFanins F`.  This remains formula-size dependent and does not synthesize
product/counting hypotheses, arbitrary normalization, full B4, or a global
depth-`d` `t(d,s)` theorem.

The syntactic global-envelope wrapper (`FormulaRecursiveSyntacticGlobal`) turns
that formula-local route into a supplied class-envelope route: if a caller
provides `formulaSize F <= M` and the ambient bound
`2 * (64 * M)^rounds * (64 * M * M) <= n`, then all root-simple/no-empty
syntactic recursive frontier levels consume the same geometric route while
returning a `TreeBudgetFrom` proof for the global budget
`t_M(d,s)=M*(s-1)`.  This supplies a B4-facing global-budget hook, but it does
not synthesize the envelope `M`, product/counting hypotheses, arbitrary
normalization, full B4, or a discharged formula-class `t(d,s)` theorem.

The global syntactic final-tree wrapper
(`FormulaRecursiveSyntacticGlobalTree`) exposes the generated certificate's
last-stage decision tree for the same supplied-envelope route and proves the
extracted tree has `dtDepth T <= M*(s-1)`.  The wrapper carries both the
single-level and all-level root-simple/no-empty consumers forward with the
final tree, semantic agreement with the restricted frontier formula, and the
same global `TreeBudgetFrom` witness.  Its formula-local corollaries discharge
the external envelope parameter by specializing `M = formulaSize F`, returning
the same final tree under `recursiveFrontierSizeTreeBudget F`.  The root
predicates and formula-size ambient bound are still supplied; this is not
synthesized normalization, product/counting/ratio synthesis, full frozen-form
B4, a discharged formula-class `t(d,s)` theorem, or Gate A rung 4.

The depth-indexed syntactic class-budget wrapper
(`FormulaSyntacticClassGlobalTree`) packages a supplied class-size envelope
`S(d)` as the explicit tree budget `t(d,s)=S(d)*(s-1)` and routes the same
syntactic final-tree theorem through that budget for all recursive frontier
levels of formulas satisfying `depth F <= d`.  This is a B4-facing
formula-class theorem surface under supplied assumptions: `formulaSize F <=
S(d)`, root syntactic simplicity, `NoEmptyFanins F`, and the ambient bound in
`S(d)` are still hypotheses.  It does not synthesize the envelope `S`,
product/counting hypotheses, ratio regimes, arbitrary normalization, full B4,
or Gate A rung 4.

The recursive class-profile wrapper (`FormulaRecursiveClassProfile`) moves the
same depth-indexed budget to the arbitrary raw recursive frontier interface:
under supplied class-size and class-width envelopes `S(d)` and `W(d)`, a
supplied recursive width profile, nonempty frontier counts, positive width
facts, and the ambient bound in those class envelopes, every in-depth
recursive frontier layer exposes a generated final tree with
`dtDepth T <= S(d)*(s-1)`.  This is a stronger structural B4-facing consumer
than the syntactic-only route, but the width profile, width envelope,
product/counting or ratio conditions, and formula-class decomposition
guarantees remain supplied; full frozen-form B4 and Gate A rung 4 remain open.

The default recursive class-width wrapper
(`FormulaRecursiveClassDefault`) instantiates that class-profile theorem with
the existing truth-table recursive width profile and uses `NoEmptyFanins F` to
synthesize nonempty frontier counts.  This removes the caller-supplied width
profile object and the separate nonempty-count hypothesis for raw recursive
frontiers, while retaining the honest fallback width `n`: the class-width
envelope form must still satisfy `n <= W(d)`, and the ambient bound is still
stated against `S(d)` and `W(d)`.  Its fixed-width corollaries specialize
`W(d)=n`, removing the separate class-width-envelope argument at the cost of
using the ambient bound `2 * (64*S(d))^rounds * (64*S(d)*n) <= n`.  Its
formula-size corollaries also specialize `S(d)=formulaSize F`, removing the
separate class-size-envelope argument at the cost of using the formula-local
ambient bound `2 * (64*formulaSize F)^rounds * (64*formulaSize F*n) <= n` and
budget `formulaSize F*(s-1)`.  This is not efficient width synthesis, product
or ratio synthesis, arbitrary normalization, full frozen-form B4, or Gate A
rung 4.

The full-depth recursive decomposition tree package
(`FormulaRecursiveDecompositionTree`) combines the existing raw full-depth
recursive skeleton and terminal width-one bottom layer with the formula-size
truth-table final-tree route for every in-depth recursive frontier level.  This
is the current structural package from raw syntax: it gives one synthesized
decomposition skeleton plus all-level final-tree evidence under the fallback
ambient bound.  Width remains truth-table fallback `n`; product/counting
hypotheses, efficient width synthesis, formula-class envelopes, arbitrary
normalization, full frozen-form B4, and Gate A rung 4 remain open.

The terminal full-depth frontier sharpening (`FormulaRecursiveTerminalTree`)
adds a width-one final-tree route for the terminal bottom layer under the same
formula-size ambient bound.  It packages that sharper terminal evidence on top
of the all-level formula-size truth-table package, but it does not change the
intermediate recursive layers: those still use fallback width `n`, and the
global product/counting and asymptotic `t(d,s)` obligations remain open.

The terminal-aware recursive profile (`FormulaRecursiveTerminalProfile`)
selects the terminal width-one bottom layer inside one all-level final-tree
consumer at `level = depth F`, while retaining the truth-table fallback layer
at intermediate levels.  This gives one uniform terminal-aware package from
raw syntax under the same formula-size ambient bound; it still does not
synthesize efficient intermediate widths, product/counting hypotheses, or a
formula-class global `t(d,s)` theorem.

The terminal-aware recursive schedule interface
(`FormulaRecursiveTerminalSchedule`) reuses the same terminal-aware layer
selector for supplied ratio/geometric schedules under the formula-local
recursive max-frontier budget `t_F`.  This closes another wiring gap between
terminal-aware bottom layers and the earlier supplied-schedule machinery, but
still leaves efficient width synthesis, product/counting synthesis, and a
discharged global `t(d,s)` theorem open.

The variable-width schedule wrapper (`FormulaVarWidthSchedule`) instantiates the
positive-depth raw-formula ratio-regime route at width `n`, using the proved
truth-table/path-DNF width bound instead of a caller-supplied child-width
predicate.  The ratio-regime schedule is still supplied, and `w = n` is not
efficient syntactic width control; this is not full B4.

The full-matching collapse-bound opener (`PHPFullMatchingCollapseBound`)
proves the first collapse-probability upper bounds over the full square
matching space in this artifact: containment of the depth-1 collapse-bad
event in the star
event(s) gives `(h−s)/h` for a single PHP literal and, via a finite list
union bound, `w·(h−s)/h` for a single width-`w` conjunctive term, in exact
cross-multiplied counting form, with strictly-below-one nonvacuous
instances at `h = 3`, `s = 2` for both the literal and a width-`2` term.
This opens the upper-bound direction of Gate
A rung 4 but is NOT a PHP switching lemma: it supplies no multi-term DNF
bad-set bound, no compressed matching-space bad-set count, and no
geometric depth-`t` collapse-probability bound over matchings.

The exact single-literal follow-up (`PHPFullMatchingCollapseExact`) upgrades
the literal bound to an equality: the converse containment is proved via two
explicit agreeing assignments flipping the free variable, so the depth-1
single-literal collapse-bad event coincides pointwise with the star event of
its variable and its probability is exactly `(h−s)/h`, with a positive event
count at `h = 3`, `s = 2` certifying realizability.  Exactness covers the
single-literal event only — the single-term union bound remains an
inequality (a term with a literal fixed to false collapses to a leaf even
when its other variables are free) — and this is still NOT a PHP switching
lemma.

The multi-term DNF opener (`PHPFullMatchingDNFBound`) proves the first
multi-term DNF depth-1 bad-set bound over the matching space in this
artifact: a simple DNF fails to collapse to depth `0` with probability at
most `|tvs.join|·(h−s)/h`, a union bound over all literal occurrences that
is linear in total DNF size, NOT the switching-lemma regime, with degenerate
empty-DNF/empty-term shapes proved exactly empty and a strictly-below-one
two-term instance `2/3` at `h = 3`, `s = 2`.

The restricted-DNF canonical-tree skeleton (`PHPFullMatchingCanonicalDT`)
connects those PHP DNFs to the existing generic term-canonical DNF tree: the
tree computes the restricted PHP DNF under agreeing assignments, queries only
variables from the original PHP DNF, and has deterministic worst-case
depth/path length at most `tvs.join.length`.  This remains infrastructure
only: the compressed matching-space count arrives only later, in
`PHPFullMatchingPathCodeFiberBound`, and no geometric collapse-probability
bound over the matching space is proved anywhere in this artifact (the
proved `(8w)^s` bounds live on the Boolean star-restriction space).

The conservative bad-path encoding/count (`PHPFullMatchingBadPathEncoding`)
extracts a certified depth-`t` deepest-path code for any bad
`canonicalRestrictedDNFTree` point and proves the filtered full-matching bad
event is bounded by the full matching-space size times the optional path-code
count.  Because the encoder keeps the original matching point, this is not a
geometric compression or collapse-probability improvement.

The compressed bad-path scaffold (`PHPFullMatchingCompressedBadPathCount`)
proves that restricted DNF survivors, canonical restricted-tree queries, and
deepest-path queries are free under `fullRestrictionOf P`; it also extracts a
free-certified `P`-dependent path code and exposes a conditional target-count
theorem for a future compressed encoder.  That module itself constructs no
encoder and no fiber bound; a fiber-bounded count over the shared code
projection arrives in the successor module below (the conditional
injective-encoder scaffold itself remains uninstantiated).

The shared path-code fiber bound (`PHPFullMatchingPathCodeFiberBound`) is the
first compressed bad-path count in this artifact over the full matching
space whose encoder forgets the original matching point: bad points are
grouped by their deepest-path code, drawn from a `P`-independent code
space, each fiber is bounded by the row-free
multiplicity of the code's touched rows, and the headline count
`card (BadPathCode) * (choose (h-1) s * h!)` beats the space size strictly at
the nonempty `h = 3`, `s = 2`, `t = 1` demo.  It is still coarse — the
support-based code space and a single guaranteed free row — so it is not a
geometric `(8w)^s`-style bound, not a per-stage information-recovery encoding
argument, and not a PHP switching lemma.

As of `v0.9.0`, the audit surface has `1810` `#guard_msgs`-pinned `#print axioms` profiles in `lean/PvNP/Audit.lean`; none of the pinned declarations depends on `sorryAx`, and every profile is within `propext`/`Classical.choice`/`Quot.sound`. One of the pins deliberately certifies OPENNESS rather than a theorem: `PvNP.GeneratedIteratedCollapse.openObligations_nonempty` pins the intentionally nonempty frozen-form Gate B obstruction map inside the audit surface. The v0.9.0 class wrapper is class-level only: full frozen-payload B4 beyond the nonempty-fanin normalized-view/dedup class and Gate A rung 4 (a PHP switching lemma) remain open.

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
