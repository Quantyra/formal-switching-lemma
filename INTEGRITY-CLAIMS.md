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
  `PHPFullMatchingCompressedBadPathCount`, plus the shared path-code fiber
  bound and coarse compressed count of `PHPFullMatchingPathCodeFiberBound`
  (the first count in this artifact whose encoder forgets the matching point,
  but which uses the coarse support-based code space, exploits only one
  guaranteed free row, and in relative form is
  `(2 * |support|)^t * (h - s) / h` of the space size — weakening as `t`
  grows rather than strengthening geometrically), plus the stage-indexed row
  recovery and conditional `q`-row coarsening infrastructure of
  `PHPFullMatchingStageRows` (which preserves recovered stage rows in the
  fiber bound and now includes a realized-code-only coarsening requiring the
  `q`-row lower bound only for nonempty canonical bad-path code fibers, a
  `q = t` specialization under the corresponding realized row-growth
  hypothesis, a proved pure row-free binomial/geometric ratio for the full square
  matching space, geometric full-square counting and finite-probability forms
  conditional only on supplied realized row-growth, and a simple-DNF structural
  replacement proving realized fibers satisfy `t <= h * |rows|`, which instantiates
  the same row-free consumer at `q = t / h`; it does not prove exact
  `t <= |rows|`, distinct recovered rows, or a term-count-independent PHP
  switching lemma), plus the code-factor quantification of
  `PHPFullMatchingCodeFactor` (which proves
  `card (BadPathCode h tvs t) = (2 * |phpDNFVarSet h tvs|)^t`, the coarser
  literal-occurrence bound `(2 * tvs.join.length)^t`, the resulting simple-DNF
  `EventProbLe` numerator `(2*m)^t * (h-s)^(t/h)`, and the obstruction that when
  `(h-s)^(t/h) >= 1`, nontriviality forces `(2*m)^t < h^(t/h)`), plus the
  S2127 realized-code count replacement of `PHPFullMatchingRealizedCodeCount`
  (which defines the finite subset of `BadPathCode` values with nonempty
  canonical full-matching bad-event fibers, replaces the simple-DNF `q = t / h`
  all-code numerator by this realized cardinality in the count, geometric count,
   and `EventProbLe` wrappers, and exposes that nontriviality still requires this
   realized-code cardinality below `h^(t/h)` whenever the row-free factor is at
   least one; it does not prove a genuinely smaller realized-code cardinality
   bound), plus the S2128 concrete realized-code obstruction of
   `PHPFullMatchingRealizedCodeObstruction` (which proves that a simple `2 x 2`
   full-square witness at `s = 1`, `t = 2` has at least two realized canonical
   bad-path codes, so the S2127 denominator `2^(2/2)` is already no larger than
   the realized-code cardinality and SimpleDNF alone cannot force the strict
   cardinality inequality needed by that route), plus the S2129/S2130 strict
   row-variable-unique gate of `PHPFullMatchingRowUniqueStrict` (which introduces
   the whole-DNF `PHPDNFGlobalRowVarUnique` hypothesis requiring same-row entries
   to use the same PHP column, proves the S2128 witness does not satisfy it, and
   under SimpleDNF plus that extra hypothesis first proves the finite `h = 2`,
   `s = 1`, `t = 2` realized-code set is empty and hence strictly below
   `2^(2/2)`, then generalizes the diagnostic to a square full-matching
    parametric realized-code emptiness theorem under the fit condition
    `h < s + t`, with strict-cardinality and zero-numerator `EventProbLe`
    corollaries; the earlier whole-DNF `PHPDNFGlobalRowUnique` condition, which
    also requires sign equality, is retained only as a stronger corollary; this is
    not general PHP switching, not arbitrary SimpleDNF compression, not
    rectangular, not Frege/PHP, not NP/circuit, not AC0, and not a P-vs-NP
    theorem), plus the S2131 code-local realized-code split of
    `PHPFullMatchingRealizedCodeSplit` (which splits realized canonical bad-path
    codes into code-local row-variable-unique codes and row-collision codes,
    proves the row-variable-unique realized-code class is empty under SimpleDNF
    and `h < s + t`, rewrites the full realized-code set and cardinality as the
    row-collision class in that finite row-capacity regime, and proves the S2128
    two-by-two witness has at least two row-collision realized codes so the
    displayed denominator `2^(2/2)` is no larger than the collision-class count;
    it also proves row collisions are impossible when `h = 1`, so the obstruction
    is minimal in the PHP-column-count direction only; this is not a strict
    row-collision compression theorem, not general PHP switching, not arbitrary
    SimpleDNF compression, not rectangular, not Frege/PHP, not NP/circuit, not
    AC0, and not a P-vs-NP theorem), plus the S2132 parametric row-collision
    obstruction of `PHPFullMatchingRealizedCodeParametricObstruction` (which for
    every `h >= 2` constructs the full-row SimpleDNF family at `s = h - 1`,
    `t = h`, proves at least `h` row-collision realized canonical bad-path
    codes, proves the denominator `h^(h/h)` is no larger than that
    collision-class cardinality, and proves the corresponding strict
    denominator route impossible for this family; this closes only the
    SimpleDNF-only row-collision denominator route for the displayed finite
    square full-matching family and is not a general compression theorem, not
    PHP switching, not rectangular, not Frege/PHP, not NP/circuit, not AC0, and
    not a P-vs-NP theorem), plus the S2133 Gate-A invariant surface of
     `PHPFullMatchingGateAInvariant` (which defines the code-local invariant that
     every realized code is row-variable-unique, proves the row-collision
     realized-code set has cardinality zero under that invariant, and proves the
     S2132 full-row family violates the invariant for every `h >= 2`; this is not
     a compression theorem, not PHP switching, not rectangular, not Frege/PHP, not
     NP/circuit, not AC0, and not a P-vs-NP theorem), plus the S2134 natural
     Gate-A invariant variants of `PHPFullMatchingGateANaturalInvariant` (which
     define finite whole-DNF row-variable capacity one, per-term row-variable
     uniqueness, code-local row-to-variable functionality, and a canonical-code
     discipline; prove that row-to-variable functionality, whole-DNF capacity one,
     or the canonical discipline imply the S2133 realized-code row-variable
     invariant and its row-collision denominator-control corollary; prove the
     S2132 full-row family violates capacity-one, per-term uniqueness,
     realized-code functionality, and canonical functionality for every `h >= 2`;
     and give a concrete `h = 2`, `s = 1`, `t = 2` cross-term witness showing
      per-term uniqueness alone does not imply realized-code row-variable
      uniqueness; this is bounded finite bookkeeping only, not a compression
      theorem, not PHP switching, not rectangular, not Frege/PHP, not NP/circuit,
      not AC0, and not a P-vs-NP theorem), plus the S2135 canonical row
      discipline increment of `PHPFullMatchingGateACanonicalRowDiscipline` (which
      defines cross-term same-row conflict exclusion, named canonical-path row
      compatibility, named syntax-facing realized row-to-variable functionality,
      and realized/canonical row-collision-free disciplines; proves term-pair
      compatibility implies whole-DNF row capacity one, realized/canonical
      row-to-variable functionality, the S2133 realized row-variable invariant,
      and the same finite row-collision denominator-control corollary; proves the
      named canonical-path and syntax-facing realized-functionality surfaces also
      recover the S2133 invariant or denominator-control route; and records
      bounded full-row and `h = 2`, `s = 1`, `t = 2` cross-term obstructions
      showing that weaker per-term uniqueness and the tested weaker candidate
      wrappers do not imply the needed realized or canonical row-to-variable
      functionality; this is bounded finite square full-matching bookkeeping only,
      not a natural-syntax satisfaction theorem, not a general compression
      theorem, not PHP switching, not rectangular, not Frege/PHP, not NP/circuit,
      not AC0, and not a P-vs-NP theorem), plus the S2136 route-decision
      obstruction of `PHPFullMatchingGateARouteDecision` (which proves S2135
      term-pair row compatibility is equivalent to S2134 whole-DNF row-capacity
      one, defines the natural local discipline `SimpleDNF` plus per-term
      row-variable uniqueness, and proves via the concrete `h = 2`, `s = 1`,
      `t = 2` cross-term witness that this natural local discipline does not
      imply realized row-to-variable functionality, canonical-path compatibility,
      term-pair compatibility, or whole-DNF row-capacity one; this is a bounded
      finite list-support obstruction only and does not prove a general
      natural-syntax theorem, PHP switching, rectangular PHP, Frege/PHP,
      NP/circuit, AC0, or P-vs-NP theorem), plus the S2137 realized-code
      bad-path/good-path split of
      `PHPFullMatchingGateARealizedCodePathSplit` (which splits the existing
      realized canonical bad-path codes by code-local row-to-variable
      functionality, proves the S2136 `h = 2`, `s = 1`, `t = 2` cross-term code
      is bad and not good, proves the bad side is empty exactly when realized
      row-to-variable functionality holds, and pins that bad-empty recovers the
      existing row-collision denominator-control theorem; this is bounded finite
      square full-matching/list-support bookkeeping only, not a natural-syntax
      satisfaction theorem, not a compression theorem, not PHP switching, not
      rectangular PHP, not Frege/PHP, not NP/circuit, not AC0, and not a P-vs-NP
      theorem), plus the S2138 bad-conflict-signature extraction of
   `PHPFullMatchingGateABadConflictSignature` (which extracts a canonical
      same-row/different-column conflict signature from every S2137 bad realized
      code, proves the S2137 bad class equals the S2131 row-collision class for
      finite square full-matching/list-support instances, and transfers the
      concrete two-by-two denominator obstruction to the bad class; this is not a
      natural-syntax theorem, not a general compression or charging theorem, not
       PHP switching, not rectangular `p > h`, not Frege/PHP, not NP/circuit, not arbitrary AC0, and not a P-vs-NP theorem), plus the S2139 rectangular/injection-space obstruction of `PHPRectMatchingInjectionObstruction` (which defines a rectangular selected-row injection space, ports the realized bad-path code/fiber interface, proves row-var-unique vs row-collision splitting/capacity results, and proves a bounded 3-by-2 full-row obstruction showing the naive rectangular row-collision denominator route still fails; this is finite rectangular matching/injection bookkeeping only; not a PHP switching lemma, not rectangular `p > h` theorem, not Frege/PHP, not NP/circuit, not AC0, and not a P-vs-NP theorem), plus the S2140 Gate-A no-go packaging of `PHPFullMatchingGateANoGoAfterS2139` (which defines only the named square full-row and rectangular 3-by-2 full-row SimpleDNF row-collision denominator/nontrivial targets and proves those current realized-code/row-collision targets fail on the S2132/S2139 witness families; this says a future route needs stronger structure, a different invariant, or a different counting/denominator target, and it is not a global Gate A impossibility theorem, not a broad SimpleDNF no-go beyond the named full-row/3-by-2 targets, not a natural-syntax theorem, not arbitrary DNF compression, not Frege/PHP, not NP/circuit, not arbitrary AC0, and not P-vs-NP), plus the S2123 one-row
   nonemptiness and duplicate-stage obstruction
in `PHPFullMatchingStageRowObstruction` (which proves every positive-length
code has at least one recovered row, and that a concrete `h = 1`, `t = 2`
duplicate-stage code has only one recovered row, so the current all-
`BadPathCode` coarsening cannot yield `q = 2` globally for that witness),
  no collapse-probability upper bound for restricted formulas over the
  matching-restriction space is stated or proved — in particular no
  multi-term DNF bad-set bound beyond the depth-1 total-size union bound of
  `PHPFullMatchingDNFBound` and the coarse path-code count above, no
  geometric `(8w)^s`-style depth-`t` collapse-probability bound
  (term-count-independent) over matchings, and no depth-`t` canonical
  decision-tree encoding argument with exact distinct per-stage row recovery;
- a measure-theoretic probability measure, expectation, or
  with-high-probability theorem over restriction distributions.  The
  matching-distribution/probability layers prove exact finite counting,
  cross-multiplied event-probability equalities/inequalities, and
  every-point floor transfer only, over the identity-subset and
  square-permutation matching spaces; rectangular `p > h` injection spaces remain
  unformalized and were not routed by the current theorem surface;
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
- any broad consequence from the S2147 exact-threshold packed-family surface:
  `FormulaRecursiveSyntacticTerminalExact` only defines the restricted
  exact-threshold subclass, routes it through the existing packed-family
  adequacy/parameter/final-tree consumers, and gives the bounded gated
  literal/true witness (`lit0` at depth index `0`, `lit0 OR true` at positive
  depth indices).  It proves no product/counting synthesis, threshold
  improvement, arbitrary normalization, arbitrary AC0/bounded-depth collapse,
  PHP switching lemma, Frege/PHP, NP/circuit, P-vs-NP, full B4, or Gate A work;
- any schematic negative claim from the S2148 small-arity obstruction:
  `FormulaRecursiveSyntacticTerminalObstruction` records only one concrete
  arity-source obstruction for the current packed-family packaging, with the same
  size/depth/class profile as the S2147 gated exact-threshold witness but fixed
  packed arity `1`, hence not ambient adequate.  It proves no product/counting
  synthesis, threshold improvement, arbitrary normalization, arbitrary
  AC0/bounded-depth collapse, PHP switching lemma, Frege/PHP, NP/circuit,
  P-vs-NP, full B4, or Gate A work;
- any broad consequence from the S2149 product/counting ambient arity source:
  `FormulaRecursiveSyntacticTerminalProduct` only names the S2144 coarse threshold
  as an explicit product of counting factors, obtains ambient adequacy from a
  positive counting multiplicity without exact-threshold equality, and gives a
  multiplicity-2 gated literal/true witness with class/depth/parameter/final-tree
  wrappers.  It proves no threshold improvement, efficient width-profile
  synthesis, arbitrary normalization, arbitrary AC0/bounded-depth collapse, PHP
  switching lemma, Frege/PHP, NP/circuit, P-vs-NP, full B4, or Gate A work;
- any broad consequence from the S2150 structural restricted-family package:
  `FormulaRecursiveSyntacticTerminalStructural` only packages class-size and width
  envelope data for the packed-family interface, derives width from class-size for
  the syntactic-terminal class, states structural ambient adequacy against the
  class-size envelope, recovers S2145 ambient adequacy by threshold monotonicity,
  and routes S2142 final-tree consumers under `t(d,s)=S(d)*(s-1)`.  It proves no
  efficient width-profile synthesis, threshold improvement, arbitrary
  normalization, arbitrary AC0/bounded-depth collapse, PHP switching lemma,
  Frege/PHP, NP/circuit, P-vs-NP, full B4, or Gate A work;
- any broad consequence from the S2151 efficient width-profile package:
  `FormulaRecursiveSyntacticTerminalWidth` only synthesizes a terminal-sharp
  non-fallback width envelope for restricted syntactic-terminal packed families,
  proves depth-zero envelope `1` is stricter than ambient arity under ambient
  adequacy, and routes S2142 consumers for a one-literal witness under
  `t(d,s)=S(d)*(s-1)`.  It proves no global efficient width-profile synthesis for
  arbitrary formula classes, threshold improvement, arbitrary normalization,
  arbitrary AC0/bounded-depth collapse, PHP switching lemma, Frege/PHP,
  NP/circuit, P-vs-NP, full B4, or Gate A work;
- any broad consequence from the S2152 intermediate-depth efficient width package:
  the same module only adds a positive-depth budget efficient envelope for the
  restricted product/counting family (non-fallback vs ambient, budget still
  equals size cap at positive depth) plus a *parallel* intermediate actual-width
  envelope with `W=1 < sizeCap` on depth-1 formulas, routing S2142 final-tree
  consumers via the budget structural data under `t(d,s)=S(d)*(s-1)`.  The
  intermediate envelope does not discharge budget `WidthEnvelope` (which still
  requires `W ≥ formulaSize` at non-terminal levels).  It proves no global
  efficient width-profile synthesis for arbitrary formula classes, threshold
  improvement, arbitrary normalization, arbitrary AC0/bounded-depth collapse,
  PHP switching lemma, Frege/PHP, NP/circuit, P-vs-NP, full B4, or Gate A work;
- any broad consequence from the S2153 restricted depth-1 tight frontier width
  budget package: `FormulaRecursiveSyntacticTerminalTightBudget` only adds a
  *parallel* depth-1 tight budget (constantly `1` when `depth F ≤ 1`, otherwise
  the standard S2142 budget) without changing the global
  `syntacticTerminalFrontierWidthBudget`, discharges a tight WidthEnvelope-style
  predicate with `W=1` and actual gate-width ≤ 1 for the restricted
  product/counting (gated lit-OR-true) family, and routes a specialized
  final-tree consumer under unchanged `t(d,s)=S(d)*(s-1)` whose geometric
  schedule uses width budget `1`.  It proves no global budget change, no global
  arbitrary-class width synthesis, no threshold improvement, no arbitrary
  normalization, no arbitrary AC0/bounded-depth collapse, no PHP switching
  lemma, no Frege/PHP, no NP/circuit, no P-vs-NP, no full B4, and no Gate A
  work;
- any broad consequence from the S2154 restricted depth-2 tight frontier width
  budget package: `FormulaRecursiveSyntacticTerminalDepthTwoTightBudget` only
  adds a *parallel* depth-2 tight budget (constantly `1` when `depth F ≤ 2`)
  without changing the global `syntacticTerminalFrontierWidthBudget`, a concrete
  nested-OR witness family with actual gate DNF width at most `1`, and
  specialized final-tree consumers under unchanged `t(d,s)=S(d)*(s-1)`.  It
  proves no global budget change, no arbitrary-class width synthesis, no
  threshold improvement, no arbitrary AC0/bounded-depth collapse, no PHP
  switching lemma, no Frege/PHP, no NP/circuit, no P-vs-NP, no full B4, and no
  Gate A work;
- any broad consequence from the S2155 restricted k-indexed bounded-shallow tight
  frontier width budget package:
  `FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget` only adds a
  *parallel* k-indexed tight budget (constantly `1` when `depth F ≤ k`) without
  changing the global S2142 `syntacticTerminalFrontierWidthBudget` or the coarse
  ambient threshold; for each fixed `k`, one recursively defined pure nested-OR
  family with depth `min(d,k)`, size `2*min(d,k)+1`, and width `1` at every
  selected frontier; reusable supplied-width syntactic-terminal consumer
  schedules on a supplied `W` level; and a concrete route that instantiates
  `W=1` and retains `t=S*(s-1)`.  Budget equality is only for the `k=1`/`k=2`
  specializations (not whole-family definitional equality).  It proves no
  arbitrary-class width synthesis, no threshold improvement, no arbitrary
  collapse, no full B4, no PHP switching lemma, no Frege/PHP, no NP/circuit, no
  P-vs-NP, and no Gate A work;
- any broad consequence from the S2156 restricted nonempty OR-only formula class
  under the S2155 bounded-shallow tight budget:
  `FormulaRecursiveSyntacticTerminalBoundedShallowOrOnlyTightBudget` only adds an
  inductive OR-only class over constants/literals closed under nonempty OR lists
  (no AND), proves syntactic simplicity / no empty fanins / syntactic DNF width
  ≤ 1 with top-child and recursive-frontier closure, discharges the S2155 tight
  envelope at `W=1` under `depth F ≤ k`, and routes formula-level plus
  packed-family final-tree consumers by reusing the S2155 supplied/bounded-shallow
  path under unchanged `t(d,s)=S(d)*(s-1)` and the coarse ambient threshold,
  with the S2155 nested-OR family as an instance and a concrete fan-in-three
  branching witness.  It proves no arbitrary-class width synthesis, no threshold
  improvement, no full B4, no PHP switching lemma, no Frege/PHP, no NP/circuit,
  no P-vs-NP, and no Gate A work;
- any broad consequence from the S2157 restricted nonempty OR/AND recurrence-width
  class under the S2155 supplied-width consumers:
  `FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget` only
  adds an inductive recurrence-fanin class over constants/literals closed under
  nonempty OR and AND lists (AND nodes carry `syntacticAndListSimpleDNF`), a
  recurrence-width measure (max under OR, sum under AND), proves syntactic
  simplicity / no empty fanins / syntactic DNF width ≤ recurrence width with
  top-child and recursive-frontier closure (frontier recurrence width ≤ root),
  lifts selected GateSpec widths against `W ≡ max 1 (formulaRecurrenceWidth F)`,
  and routes formula-level plus packed-family final-tree consumers by reusing the
  S2155 supplied-width path under unchanged `t(d,s)=S(d)*(s-1)` and the coarse
  ambient threshold, with S2156 OR-only formulas embedding at recurrence width
  ≤ 1 and a concrete two-literal AND witness of recurrence width 2.  It proves
  no arbitrary-class width synthesis, no threshold improvement, no full B4, no
  PHP switching lemma, no Frege/PHP, no NP/circuit, no P-vs-NP, and no Gate A
  work;
- any broad consequence from the S2158 restricted disjoint-support OR/AND class
  under the S2157 embedding:
  `FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget`
  only adds a syntactic support function `formulaVars` with term-support
  inclusion lemmas for the syntactic DNF expansion, a compatibility-synthesis
  lemma (pairwise-disjoint child supports synthesize
  `syntacticAndListSimpleDNF`), an inductive disjoint-support class over
  constants/literals closed under nonempty OR and AND lists (AND nodes carry
  pairwise support disjointness instead of a supplied compatibility Prop), an
  embedding into the S2157 recurrence-fanin class, inherited wrappers for
  syntactic simplicity / no empty fanins / syntactic DNF width ≤ recurrence
  width / frontier closure and the formula-level plus packed-family final-tree
  routes under unchanged `t(d,s)=S(d)*(s-1)` and the coarse ambient threshold,
  an S2156 OR-only embedding, and concrete witnesses (the S2157 two-literal AND
  and an AND-of-two-variable-disjoint-ORs of recurrence width 2) certified with
  no manual `CompatibleDNF` proof.  This is disjoint-support AND synthesis
  only; shared-variable ANDs still require a supplied compatibility proof.  It
  proves no arbitrary-class width synthesis, no threshold improvement, no full
  B4, no PHP switching lemma, no Frege/PHP, no NP/circuit, no P-vs-NP, and no
  Gate A work;
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
| `PvNP.PHPFullMatchingPathCodeFiberBound.codeRows_nonempty` | `propext`, `Classical.choice`, `Quot.sound` | proven every positive-length path code touches at least one pigeon row |
| `PvNP.PHPFullMatchingPathCodeFiberBound.canonicalDepthBad_fiber_count_le` | `propext`, `Classical.choice`, `Quot.sound` | proven per-code fiber bound: bad matching points sharing a path code number at most the row-free multiplicity `choose (h - |codeRows c|) s * h!` |
| `PvNP.PHPFullMatchingPathCodeFiberBound.canonicalDepthBad_count_le_pathCode_mul_rowFree` | `propext`, `Classical.choice`, `Quot.sound` | for `1 <= t`, proven compressed bad-path count `card (BadPathCode) * (choose (h-1) s * h!)`; first in this artifact whose encoder forgets the matching point, but coarse: support-based code space, one guaranteed free row |
| `PvNP.PHPFullMatchingPathCodeFiberBound.canonicalDepthBad_ratio_le` | `propext`, `Classical.choice`, `Quot.sound` | for `1 <= t`, proven cross-multiplied ratio form of the compressed count via `star_ratio_full`; not a geometric `(8w)^s`-style bound |
| `PvNP.PHPFullMatchingPathCodeFiberBound.card_badPathCode_demo` | `propext`, `Classical.choice`, `Quot.sound` | proven demo path-code space at `h = 3`, `t = 1` has exactly 2 elements |
| `PvNP.PHPFullMatchingPathCodeFiberBound.demo_bound_lt_space` | `propext`, `Classical.choice`, `Quot.sound` | proven demo compressed bound `12` is strictly below the space size `18` at `h = 3`, `s = 2`, `t = 1` |
| `PvNP.PHPFullMatchingPathCodeFiberBound.demo_bad_count_pos` | `propext`, `Classical.choice`, `Quot.sound` | proven demo depth-1 bad event is nonempty, so the strict demo bound is non-vacuous |
| `PvNP.PHPFullMatchingStageRows.codeStageEntry_var_eq` | `propext`, `Classical.choice`, `Quot.sound` | decoded stage entry variable equals the stored bad-path-code variable |
| `PvNP.PHPFullMatchingStageRows.mem_codeStageRows` | `propext`, `Classical.choice`, `Quot.sound` | membership in recovered stage rows iff some stage decodes to the row |
| `PvNP.PHPFullMatchingStageRows.codeStageRow_free_of_encoding_eq_some` | `propext`, `Classical.choice`, `Quot.sound` | each recovered stage row is free for a bad point whose encoding is the code |
| `PvNP.PHPFullMatchingStageRows.fullRowsFree_codeStageRows_of_encoding_eq_some` | `propext`, `Classical.choice`, `Quot.sound` | all recovered stage rows are free in the matching point/code fiber |
| `PvNP.PHPFullMatchingStageRows.choose_rowFree_one_step_le` | `propext`, `Quot.sound` | pure one-step row-free binomial comparison |
| `PvNP.PHPFullMatchingStageRows.choose_rowFree_geometric_le` | `propext`, `Quot.sound` | pure row-free binomial geometric comparison, with no realized row-growth content |
| `PvNP.PHPFullMatchingStageRows.rowFree_geometric_ratio_full` | `propext`, `Classical.choice`, `Quot.sound` | full-square row-free geometric-ratio inequality from finite cardinality arithmetic |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_fiber_count_le_stageRows` | `propext`, `Classical.choice`, `Quot.sound` | per-code fiber bound preserving recovered stage-row set |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_count_le_sum_codeStageRows` | `propext`, `Classical.choice`, `Quot.sound` | bad-event count bounded by sum over code-specific recovered-row multiplicities |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_count_le_pathCode_mul_rowFree_of_codeStageRows_card_ge` | `propext`, `Classical.choice`, `Quot.sound` | conditional uniform coarsening from supplied `q <= (codeStageRows c).card`; does not prove distinct rows or instantiate `q = t` |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBadCodeFiber_count_le_rowFree_of_realized_codeStageRows_card_ge` | `propext`, `Classical.choice`, `Quot.sound` | per-code realized-fiber coarsening; the `q`-row lower bound is required only when the code fiber is nonempty |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge` | `propext`, `Classical.choice`, `Quot.sound` | realized-code-only conditional uniform coarsening; no realized row-growth, `q = t`, geometric decay, PHP switching lemma, or lower-bound claim |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_count_le_pathCode_mul_rowFree_of_realized_codeStageRows_card_ge_t` | `propext`, `Classical.choice`, `Quot.sound` | S2124 `q = t` specialization under supplied realized row-growth; does not prove realized row-growth or distinct stages |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_probability_geometric_le_of_realized_codeStageRows_card_ge_t` | `propext`, `Classical.choice`, `Quot.sound` | geometric full-square counting bound from supplied realized row-growth plus the proved row-free geometric-ratio inequality; does not prove realized row-growth or a rectangular injection result |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_eventProbLe_geometric_of_realized_codeStageRows_card_ge_t` | `propext`, `Classical.choice`, `Quot.sound` | thin `EventProbLe` wrapper for the conditional geometric full-square bound; exposes finite probability interface only and does not prove realized row-growth, rectangular `p > h`, or a PHP switching lemma |
| `PvNP.PHPFullMatchingStageRows.codeStageVar_injective_of_realized_simple` | `propext`, `Classical.choice`, `Quot.sound` | under `SimpleDNF (phpDNFAsDNF h tvs)`, realized nonempty fibers have injective recovered PHP variables along the code stages; no distinct-row theorem |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBadCodeFiberNonempty.le_h_mul_codeStageRows_card_of_simple` | `propext`, `Classical.choice`, `Quot.sound` | simple-DNF structural replacement: realized fibers satisfy `t <= h * (codeStageRows c).card`; this is not exact `t <= |rows|` |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_count_le_pathCode_mul_rowFree_of_simple_realized_div_h` | `propext`, `Classical.choice`, `Quot.sound` | instantiates the realized-code-only row-free consumer with `q = t / h` using the simple-DNF structural replacement |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_probability_geometric_le_of_simple_realized_div_h` | `propext`, `Classical.choice`, `Quot.sound` | geometric full-square count form at `q = t / h` under `SimpleDNF`; retains the `BadPathCode` factor and square matching space |
| `PvNP.PHPFullMatchingStageRows.canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h` | `propext`, `Classical.choice`, `Quot.sound` | finite `EventProbLe` wrapper for the simple-DNF structural replacement at `q = t / h`; not rectangular `p > h` and not a PHP switching lemma |
| `PvNP.PHPFullMatchingCodeFactor.eventProbLe_mono_num` | `propext`, `Quot.sound` | generic finite-probability numerator monotonicity used only to enlarge proved bounds |
| `PvNP.PHPFullMatchingCodeFactor.phpDNFVarSet_card_le_join_length` | `propext`, `Classical.choice`, `Quot.sound` | PHP DNF variable support cardinality is at most total literal-occurrence count `tvs.join.length` |
| `PvNP.PHPFullMatchingCodeFactor.badPathCode_card_support` | `propext`, `Classical.choice`, `Quot.sound` | exact current all-code cardinality `card (BadPathCode h tvs t) = (2 * |phpDNFVarSet h tvs|)^t` |
| `PvNP.PHPFullMatchingCodeFactor.badPathCode_card_le_of_support_card_le` | `propext`, `Classical.choice`, `Quot.sound` | if the PHP DNF variable support has size at most `m`, then `card (BadPathCode h tvs t) <= (2*m)^t` |
| `PvNP.PHPFullMatchingCodeFactor.badPathCode_card_le_join_length` | `propext`, `Classical.choice`, `Quot.sound` | coarser input-data bound `card (BadPathCode h tvs t) <= (2 * tvs.join.length)^t` |
| `PvNP.PHPFullMatchingCodeFactor.canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_support_bound` | `propext`, `Classical.choice`, `Quot.sound` | S2125 simple-DNF `q = t/h` EventProbLe bound with explicit numerator `(2*m)^t * (h-s)^(t/h)` under support cap `m` |
| `PvNP.PHPFullMatchingCodeFactor.canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_join_length` | `propext`, `Classical.choice`, `Quot.sound` | input-data-expanded S2125 simple-DNF bound with numerator `(2 * tvs.join.length)^t * (h-s)^(t/h)` |
| `PvNP.PHPFullMatchingCodeFactor.canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_support_bound_nontrivial` | `propext`, `Classical.choice`, `Quot.sound` | packages the support-bound EventProbLe result with the explicit below-one parameter inequality; does not prove that inequality automatically |
| `PvNP.PHPFullMatchingCodeFactor.codeFactor_nontrivial_requires_code_factor_lt_denominator` | `propext` | formal obstruction: if `(h-s)^(t/h) >= 1`, nontriviality of the current all-code bound forces `(2*m)^t < h^(t/h)` |
| `PvNP.PHPFullMatchingCodeFactor.codeFactor_nontrivial_impossible_of_denominator_le_code_factor` | `propext` | formal obstruction: if `h^(t/h) <= (2*m)^t` and the row-free factor is at least one, the current all-code bound cannot be below one |
| `PvNP.PHPFullMatchingRealizedCodeCount.realizedBadPathCodes_card_le_badPathCode` | `propext`, `Classical.choice`, `Quot.sound` | realized canonical bad-path codes form a finite subset of the ambient `BadPathCode` type; no strict or asymptotic saving is proved |
| `PvNP.PHPFullMatchingRealizedCodeCount.canonicalDepthBad_count_le_realizedCode_mul_rowFree_of_realized_codeStageRows_card_ge` | `propext`, `Classical.choice`, `Quot.sound` | realized-code-count replacement: the row-free multiplicity is paid only for nonempty canonical bad-path code fibers under supplied realized row-growth |
| `PvNP.PHPFullMatchingRealizedCodeCount.canonicalDepthBad_count_le_realizedCode_mul_rowFree_of_simple_realized_div_h` | `propext`, `Classical.choice`, `Quot.sound` | simple-DNF realized-code count bound at `q = t/h`; replaces the all-code factor by realized-code cardinality but does not bound that cardinality sharply |
| `PvNP.PHPFullMatchingRealizedCodeCount.canonicalDepthBad_probability_geometric_le_of_simple_realizedCode_div_h` | `propext`, `Classical.choice`, `Quot.sound` | geometric full-square count form at `q = t/h` with realized-code cardinality numerator; finite square matching-space bookkeeping only |
| `PvNP.PHPFullMatchingRealizedCodeCount.canonicalDepthBad_eventProbLe_geometric_of_simple_realizedCode_div_h` | `propext`, `Classical.choice`, `Quot.sound` | finite EventProbLe wrapper for the simple-DNF realized-code replacement; not a term-count-independent PHP switching lemma |
| `PvNP.PHPFullMatchingRealizedCodeCount.realizedCode_nontrivial_requires_realized_card_lt_denominator` | `propext`, `Classical.choice`, `Quot.sound` | realized-code obstruction: if `(h-s)^(t/h) >= 1`, nontriviality forces the realized-code cardinality below `h^(t/h)` |
| `PvNP.PHPFullMatchingRealizedCodeCount.realizedCode_nontrivial_impossible_of_denominator_le_realized_card` | `propext`, `Classical.choice`, `Quot.sound` | realized-code obstruction: if `h^(t/h)` is no larger than the realized-code cardinality, this realized-code route cannot be below one when the row-free factor is at least one |
| `PvNP.PHPFullMatchingRealizedCodeObstruction.twoRowsTwoCols_realizedBadPathCodes_card_ge_two` | `propext`, `Classical.choice`, `Quot.sound` | concrete simple-DNF `h = 2`, `s = 1`, `t = 2` witness has at least two realized canonical bad-path codes |
| `PvNP.PHPFullMatchingRealizedCodeObstruction.twoRowsTwoCols_denominator_le_realizedBadPathCodes_card` | `propext`, `Classical.choice`, `Quot.sound` | in the concrete witness, the S2127 denominator `2^(2/2)` is no larger than the realized-code cardinality |
| `PvNP.PHPFullMatchingRealizedCodeObstruction.twoRowsTwoCols_not_realizedBadPathCodes_card_lt_denominator` | `propext`, `Classical.choice`, `Quot.sound` | finite obstruction showing SimpleDNF alone cannot force the strict realized-cardinality inequality in the concrete witness |
| `PvNP.PHPFullMatchingRealizedCodeObstruction.twoRowsTwoCols_realizedCode_route_nontrivial_impossible` | `propext`, `Classical.choice`, `Quot.sound` | applies the S2127 obstruction to the concrete witness: the realized-code numerator is not strictly below the displayed denominator |
| `PvNP.PHPFullMatchingRowUniqueStrict.twoRowsTwoColsTvs_h2_not_globalRowUnique` | `propext` | the S2128 two-by-two witness is not sign-sensitive globally row-unique |
| `PvNP.PHPFullMatchingRowUniqueStrict.twoRowsTwoColsTvs_h2_not_globalRowVarUnique` | `propext` | the S2128 two-by-two witness is not globally row-variable-unique: one row uses two PHP columns |
| `PvNP.PHPFullMatchingRowUniqueStrict.codeStageVar_eq_of_globalRowVarUnique_row_eq` | `propext`, `Classical.choice`, `Quot.sound` | under whole-DNF row-variable uniqueness, equal recovered rows force equal stored code variables |
| `PvNP.PHPFullMatchingRowUniqueStrict.codeStageRow_injective_of_realized_simple_globalRowVarUnique` | `propext`, `Classical.choice`, `Quot.sound` | realized SimpleDNF plus whole-DNF row-variable uniqueness gives injective recovered stage rows |
| `PvNP.PHPFullMatchingRowUniqueStrict.codeStageRow_injective_of_realized_simple_globalRowUnique` | `propext`, `Classical.choice`, `Quot.sound` | stronger row-unique corollary of realized SimpleDNF recovered-stage-row injectivity |
| `PvNP.PHPFullMatchingRowUniqueStrict.twoByTwo_realizedBadPathCodes_eq_empty_of_globalRowVarUnique` | `propext`, `Classical.choice`, `Quot.sound` | finite `h = 2`, `s = 1`, `t = 2` realized-code set is empty under SimpleDNF plus whole-DNF row-variable uniqueness |
| `PvNP.PHPFullMatchingRowUniqueStrict.twoByTwo_realizedBadPathCodes_eq_empty_of_globalRowUnique` | `propext`, `Classical.choice`, `Quot.sound` | stronger row-unique corollary of the finite two-by-two realized-code emptiness theorem |
| `PvNP.PHPFullMatchingRowUniqueStrict.twoByTwo_realizedBadPathCodes_card_lt_denominator_of_globalRowVarUnique` | `propext`, `Classical.choice`, `Quot.sound` | finite two-by-two strict cardinality consequence under row-variable uniqueness; not a general compression theorem |
| `PvNP.PHPFullMatchingRowUniqueStrict.twoByTwo_realizedBadPathCodes_card_lt_denominator_of_globalRowUnique` | `propext`, `Classical.choice`, `Quot.sound` | stronger row-unique corollary of the finite two-by-two strict cardinality theorem |
| `PvNP.PHPFullMatchingRowUniqueStrict.realizedBadPathCodes_eq_empty_of_simple_globalRowVarUnique_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | S2130 finite square row-capacity theorem: under SimpleDNF plus row-variable uniqueness, realized-code emptiness follows from `h < s + t` |
| `PvNP.PHPFullMatchingRowUniqueStrict.realizedBadPathCodes_eq_empty_of_simple_globalRowUnique_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | stronger row-unique corollary of the S2130 parametric realized-code emptiness theorem |
| `PvNP.PHPFullMatchingRowUniqueStrict.realizedBadPathCodes_card_lt_denominator_of_simple_globalRowVarUnique_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | S2130 strict realized-code cardinality consequence under the same finite square row-capacity hypotheses |
| `PvNP.PHPFullMatchingRowUniqueStrict.realizedBadPathCodes_card_lt_denominator_of_simple_globalRowUnique_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | stronger row-unique corollary of the S2130 strict realized-code cardinality theorem |
| `PvNP.PHPFullMatchingRowUniqueStrict.canonicalDepthBad_eventProbLe_zero_of_simple_globalRowVarUnique_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | S2130 zero-numerator finite `EventProbLe` wrapper; finite square bookkeeping only, not measure-theoretic probability |
| `PvNP.PHPFullMatchingRowUniqueStrict.canonicalDepthBad_eventProbLe_zero_of_simple_globalRowUnique_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | stronger row-unique corollary of the S2130 zero-numerator finite `EventProbLe` wrapper |
| `PvNP.PHPFullMatchingRealizedCodeSplit.codeRowCollision_iff_not_codeRowVarUnique` | `propext`, `Classical.choice`, `Quot.sound` | code-local split predicate: row-collision codes are exactly non-row-variable-unique codes |
| `PvNP.PHPFullMatchingRealizedCodeSplit.realizedBadPathCodes_eq_rowVarUnique_union_rowCollision` | `propext`, `Classical.choice`, `Quot.sound` | realized bad-path codes split into code-local row-variable-unique and row-collision classes |
| `PvNP.PHPFullMatchingRealizedCodeSplit.disjoint_rowVarUniqueRealizedBadPathCodes_rowCollision` | `propext`, `Classical.choice`, `Quot.sound` | the two S2131 realized-code classes are disjoint |
| `PvNP.PHPFullMatchingRealizedCodeSplit.codeStageVar_eq_of_codeRowVarUnique_row_eq` | `propext`, `Classical.choice`, `Quot.sound` | code-local row-variable uniqueness turns equal recovered rows into equal stored code variables |
| `PvNP.PHPFullMatchingRealizedCodeSplit.codeStageRow_injective_of_realized_simple_codeRowVarUnique` | `propext`, `Classical.choice`, `Quot.sound` | realized SimpleDNF plus code-local row-variable uniqueness gives injective recovered stage rows |
| `PvNP.PHPFullMatchingRealizedCodeSplit.rowVarUniqueRealizedBadPathCodes_eq_empty_of_simple_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | S2131 finite square row-capacity theorem: code-local row-variable-unique realized codes are empty under SimpleDNF and `h < s + t` |
| `PvNP.PHPFullMatchingRealizedCodeSplit.realizedBadPathCodes_eq_rowCollisionRealizedBadPathCodes_of_simple_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | in the S2131 row-capacity regime, every realized code is a row-collision code |
| `PvNP.PHPFullMatchingRealizedCodeSplit.rowCollisionRealizedBadPathCodes_card_eq_realizedBadPathCodes_card_of_simple_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | in the S2131 row-capacity regime, row-collision cardinality equals full realized-code cardinality; no strict collision compression is proved |
| `PvNP.PHPFullMatchingRealizedCodeSplit.canonicalDepthBad_eventProbLe_geometric_of_simple_rowCollision_of_h_lt_s_add_t` | `propext`, `Classical.choice`, `Quot.sound` | finite `EventProbLe` wrapper using row-collision cardinality in the row-capacity regime; square bookkeeping only |
| `PvNP.PHPFullMatchingRealizedCodeSplit.twoRowsTwoColsCode_row0_h2_t2_codeRowCollision` | `propext`, `Classical.choice`, `Quot.sound` | the S2128 row-0 realized code is a same-row/different-column collision code |
| `PvNP.PHPFullMatchingRealizedCodeSplit.twoRowsTwoColsCode_row1_h2_t2_codeRowCollision` | `propext`, `Classical.choice`, `Quot.sound` | the S2128 row-1 realized code is a same-row/different-column collision code |
| `PvNP.PHPFullMatchingRealizedCodeSplit.twoRowsTwoCols_rowCollisionRealizedBadPathCodes_card_ge_two` | `propext`, `Classical.choice`, `Quot.sound` | the concrete S2128 witness has at least two row-collision realized codes |
| `PvNP.PHPFullMatchingRealizedCodeSplit.twoRowsTwoCols_denominator_le_rowCollisionRealizedBadPathCodes_card` | `propext`, `Classical.choice`, `Quot.sound` | in the concrete witness, the S2127 denominator `2^(2/2)` is no larger than the row-collision realized-code cardinality |
| `PvNP.PHPFullMatchingRealizedCodeSplit.twoRowsTwoCols_not_rowCollisionRealizedBadPathCodes_card_lt_denominator` | `propext`, `Classical.choice`, `Quot.sound` | finite obstruction showing SimpleDNF alone cannot force the collision-class cardinality below the displayed denominator in the concrete witness |
| `PvNP.PHPFullMatchingRealizedCodeSplit.twoRowsTwoCols_rowCollision_route_nontrivial_impossible` | `propext`, `Classical.choice`, `Quot.sound` | applies the collision-class obstruction to the concrete witness: the collision numerator is not strictly below the displayed denominator |
| `PvNP.PHPFullMatchingRealizedCodeSplit.not_codeRowCollision_h_one` | `propext`, `Classical.choice`, `Quot.sound` | row collisions are impossible over one PHP column |
| `PvNP.PHPFullMatchingRealizedCodeSplit.rowCollisionRealizedBadPathCodes_eq_empty_h_one` | `propext`, `Classical.choice`, `Quot.sound` | over `h = 1`, the row-collision realized-code class is empty for every square full-matching parameter choice |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowP_canonicalDepthBad` | `propext`, `Classical.choice`, `Quot.sound` | in the S2132 full-row family, the one-free-row matching point has canonical depth at least `h` |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowCode_mem_realized` | `propext`, `Classical.choice`, `Quot.sound` | each free row in the S2132 family yields a realized canonical bad-path code |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowCode_injective` | `propext`, `Classical.choice`, `Quot.sound` | distinct free rows yield distinct realized codes in the S2132 family |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowTvs_simple` | `propext`, `Classical.choice`, `Quot.sound` | the S2132 full-row DNF family is syntactically simple |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowTvs_rowCollisionRealizedBadPathCodes_card_ge_h` | `propext`, `Classical.choice`, `Quot.sound` | parametric row-collision obstruction: for every `h >= 2`, the S2132 family has at least `h` row-collision realized codes at `s = h - 1`, `t = h` |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowTvs_denominator_le_rowCollisionRealizedBadPathCodes_card` | `propext`, `Classical.choice`, `Quot.sound` | in the S2132 family, the denominator `h^(h/h)` is no larger than the row-collision realized-code count |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowTvs_not_rowCollisionRealizedBadPathCodes_card_lt_denominator` | `propext`, `Classical.choice`, `Quot.sound` | finite parametric obstruction: SimpleDNF alone cannot force the row-collision count below the displayed denominator on the S2132 family |
| `PvNP.PHPFullMatchingRealizedCodeParametricObstruction.fullRowTvs_rowCollision_route_nontrivial_impossible` | `propext`, `Classical.choice`, `Quot.sound` | applies the S2132 denominator obstruction to the row-collision numerator route for `s = h - 1`, `t = h` |
| `PvNP.PHPFullMatchingGateAInvariant.RealizedCodeRowVarUnique` | (definition) | S2133 code-local invariant: every realized code is row-variable-unique |
| `PvNP.PHPFullMatchingGateAInvariant.rowCollisionRealizedBadPathCodes_eq_empty_of_realizedCodeRowVarUnique` | (check-pinned) | under the S2133 invariant, the row-collision realized-code set is empty |
| `PvNP.PHPFullMatchingGateAInvariant.rowCollisionRealizedBadPathCodes_card_eq_zero_of_realizedCodeRowVarUnique` | (check-pinned) | cardinal-zero corollary for the row-collision realized-code set under the S2133 invariant |
| `PvNP.PHPFullMatchingGateAInvariant.rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowVarUnique` | (check-pinned) | finite denominator-control corollary: under the S2133 invariant, the row-collision count is below any supplied positive `h^(t/h)` denominator |
| `PvNP.PHPFullMatchingGateAInvariant.fullRowTvs_not_realizedCodeRowVarUnique` | (check-pinned) | the S2132 full-row family violates the S2133 invariant for every `h >= 2` |
| `PvNP.PHPFullMatchingStageRowObstruction.codeStageRows_nonempty` | `propext`, `Classical.choice`, `Quot.sound` | every positive-length code recovers at least one stage row |
| `PvNP.PHPFullMatchingStageRowObstruction.one_le_codeStageRows_card` | `propext`, `Classical.choice`, `Quot.sound` | cardinal form of positive-length one-row nonemptiness |
| `PvNP.PHPFullMatchingStageRowObstruction.codeStageRows_card_eq_of_injective` | `propext`, `Classical.choice`, `Quot.sound` | conditional exact `t` recovered rows under injectivity of the stage-row map |
| `PvNP.PHPFullMatchingStageRowObstruction.duplicateStageCode_h1_t2_codeStageRows_card` | `propext`, `Classical.choice`, `Quot.sound` | duplicate-stage witness over `h = 1`, `t = 2` has exactly one recovered row |
| `PvNP.PHPFullMatchingStageRowObstruction.not_two_le_duplicateStageCode_h1_t2_codeStageRows_card` | `propext`, `Classical.choice`, `Quot.sound` | duplicate-stage witness refutes a two-row lower bound for that code |
| `PvNP.PHPFullMatchingStageRowObstruction.not_forall_two_le_codeStageRows_card_duplicateStageTvs_h1_t2` | `propext`, `Classical.choice`, `Quot.sound` | not all codes over the tiny support recover at least two rows |
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
provided.  `FormulaRecursiveTerminalClassProfile` adds only the bounded S2141
class-envelope terminal-aware Gate B surface: final-tree wrappers are proved
under supplied class-size envelope `S`, terminal-aware width envelope `W`,
`NoEmptyFanins`, and the ambient geometric entry inequality, with a fixed-width
truth-table fallback.  It does not synthesize class envelopes or product/counting
beats, does not give automatic B4, arbitrary formula-class synthesis, arbitrary
AC0 collapse, Frege/PHP, NP/circuit, or P-vs-NP.
`FormulaRecursiveSyntacticTerminalClassProfile` adds only a named restricted
syntactic-terminal class (`syntacticFormulaSimpleDNF F ∧ NoEmptyFanins F`) with a
separate S2142 selector: syntactic/formula-size width at intermediate recursive
frontiers, terminal width one at full depth, class budget
`t(d,s)=S(d)*(s-1)`, and ambient inequality with `W := S`.  Its main all-level
theorem no longer has a caller-supplied width-envelope premise, but it still
relies on the supplied class-size envelope `formulaSize F <= S d` and does not
synthesize `S`, product/counting beats, or arbitrary normalization.
`FormulaRecursiveSyntacticTerminalEntry` adds only a named entry-size
feasibility/no-go packet for that S2142 ambient inequality:
`syntacticTerminalClassEntryThreshold S d rounds =
2 * (64 * S d) ^ rounds * (64 * S d * S d)` and
`SyntacticTerminalClassEntryFeasible S d rounds n` names threshold feasibility.
It proves exact-threshold feasibility, monotonicity in `n`, no-go below the
threshold, and wrappers routing the S2142 all-level final-tree theorem through
the named predicate or discharging it at the exact threshold.  This packet does
not add product/counting synthesis beyond naming/discharging the ambient bound,
does not add arbitrary normalization, arbitrary AC0/bounded-depth collapse, PHP
switching, Frege/PHP, NP/circuit, or P-vs-NP content, and Gate A remains closed.
`FormulaRecursiveSyntacticTerminalRegime` adds only the bounded S2144 coarse
parameter-regime sufficient condition for the same named S2143 entry predicate:
if `S d <= M d` and `N d` is at least
`2 * (64 * M d) ^ (roundsOf d) * (64 * M d * M d)`, then the S2143 exact entry
threshold is feasible at depth `d`, and the existing S2142 all-level final-tree
theorem can be routed under the unchanged class budget `t(d,s)=S(d)*(s-1)` for
restricted `SyntacticTerminalFormulaClass` formulas.  This is not a broad
product/counting synthesis, not a threshold improvement, not arbitrary formula
normalization, not arbitrary AC0/bounded-depth collapse, not full B4, not PHP
switching, not Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A work.
`FormulaRecursiveSyntacticTerminalFamily` adds only the bounded S2145 packed
family source for that S2144 regime: for a depth-indexed packed family
`Nat -> Sigma (fun n => BDFormula n)`, the cap `M` and class envelope `S` are
the actual formula size of the packed formula at each depth, and `N` is the
actual packed arity, with a separate explicit ambient-adequacy hypothesis
against the same coarse threshold.  It provides pointwise entry feasibility and
final-tree wrappers under the unchanged class budget `t(d,s)=S(d)*(s-1)` for the
restricted syntactic-terminal class.  It is not broad product/counting
synthesis, not a threshold improvement, not arbitrary normalization, not
arbitrary AC0/bounded-depth collapse, not full B4, not PHP switching, not
Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A work.
`FormulaRecursiveSyntacticTerminalConcrete` adds only the bounded S2146 concrete
one-literal exact-threshold packed-family adequacy witness: for each depth index,
the packed formula is a positive literal over variable `0`, the formula-size cap
is exactly `1`, the depth is `0`, and the ambient arity is exactly the S2144
coarse threshold for size cap `1` and the supplied `roundsOf d`.  It provides the
corresponding parameter-regime, pointwise entry-feasibility, and final-tree
wrappers for this concrete family only.  It is not product/counting synthesis,
not a threshold improvement, not arbitrary normalization, not arbitrary AC0,
not PHP switching, not Frege/PHP, not NP-circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalExact` adds only the bounded S2147 restricted
exact-threshold packed-family subclass and gated literal/true witness.  At depth
index `0` the packed formula is a positive literal, at positive depth indices it
is `lit0 OR true`, and the corresponding size caps are `1` and `3` respectively;
exact-threshold status discharges ambient adequacy through the existing S2145
consumers.  This is not product/counting synthesis, not a threshold improvement,
not arbitrary normalization, not arbitrary AC0/bounded-depth collapse, not full
B4, not PHP switching, not Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalObstruction` adds only the bounded S2148
concrete arity-source obstruction: the same gated literal/true formula-side
size/depth/class profile is packaged at fixed ambient arity `1`, so the family is
not ambient adequate for any `roundsOf`.  This is not a schematic negative claim,
not product/counting synthesis, not a threshold improvement, not arbitrary
normalization, not arbitrary AC0/bounded-depth collapse, not full B4, not PHP
switching, not Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalProduct` adds only the bounded S2149 product/
counting ambient arity source: the S2144 coarse threshold is named as an explicit
product of counting factors, ambient adequacy is obtained from a positive
counting multiplicity without exact-threshold arity equality, and a multiplicity-2
gated literal/true family witnesses strict super-threshold adequacy with class,
depth, parameter-regime, entry-feasibility, and final-tree wrappers.  This is not
threshold improvement, not efficient width-profile synthesis, not arbitrary
normalization, not arbitrary AC0/bounded-depth collapse, not full B4, not PHP
switching, not Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalStructural` adds only the bounded S2150
structural restricted-family ambient-adequacy package: class-size and width
envelope data for the S2145 packed-family interface, width envelope derived from
class-size for the syntactic-terminal class, structural ambient adequacy against
the class-size envelope, recovery of S2145 ambient adequacy by threshold
monotonicity, and S2142 final-tree routing under unchanged `t(d,s)=S(d)*(s-1)`,
with the S2149 multiplicity-2 family as a concrete structural witness.  This is
not efficient width-profile synthesis, not threshold improvement, not arbitrary
normalization, not arbitrary AC0/bounded-depth collapse, not full B4, not PHP
switching, not Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalWidth` adds only the bounded S2151 efficient
width-profile synthesis package for restricted syntactic-terminal packed
families: a terminal-sharp non-fallback width envelope synthesized from formula
structure, depth-zero envelope `1` stricter than ambient arity under ambient
adequacy, a one-literal concrete witness, and S2142 final-tree routing under
unchanged `t(d,s)=S(d)*(s-1)`.  S2152 extends the same module with an
intermediate-depth package for the restricted product/counting family: positive-
depth budget efficient envelope (equals size cap, non-fallback vs ambient) and a
parallel intermediate actual-width envelope `W=1` that is stricter than size cap
and ambient arity at depth one, with S2142 final-tree routing still discharged
via the budget structural data under unchanged `t(d,s)=S(d)*(s-1)`.  The
intermediate envelope is not a budget `WidthEnvelope` discharge.  This is not
global efficient width-profile synthesis for arbitrary formula classes, not
threshold improvement, not arbitrary normalization, not arbitrary
AC0/bounded-depth collapse, not full B4, not PHP switching, not Frege/PHP, not
NP/circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalTightBudget` adds only the bounded S2153
restricted depth-1 tight frontier width budget package: a parallel budget that
is constantly `1` when `depth F ≤ 1` (falling back to the standard S2142 budget
otherwise) without changing the global `syntacticTerminalFrontierWidthBudget`,
a tight WidthEnvelope-style predicate discharged at `W=1` for the
product/counting family, actual gate-width discharge against that tight budget
for the gated lit-OR-true witness, and a specialized final-tree consumer under
unchanged `t(d,s)=S(d)*(s-1)` whose geometric schedule uses width budget `1`.
This is not a global budget change, not global arbitrary-class width synthesis,
not threshold improvement, not arbitrary normalization, not arbitrary
AC0/bounded-depth collapse, not full B4, not PHP switching, not Frege/PHP, not
NP/circuit, not P-vs-NP, and not Gate A.
`FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget` adds only the
bounded S2155 restricted k-indexed bounded-shallow tight frontier width budget
package: a parallel budget that is constantly `1` when `depth F ≤ k` without
changing the global S2142 `syntacticTerminalFrontierWidthBudget` or the coarse
ambient threshold; for each fixed `k`, one recursively defined pure nested-OR
family with depth `min(d,k)`, size `2*min(d,k)+1`, and width `1` at every
selected frontier; reusable supplied-width syntactic-terminal consumer
schedules on a supplied `W` level; and a concrete route that instantiates
`W=1` and retains `t=S*(s-1)`.  Only `k=1`/`k=2` budget equality is claimed
(not whole-family definitional equality).  This is not arbitrary-class width
synthesis, not threshold improvement, not arbitrary collapse, not full B4, not
PHP switching, not Frege/PHP, not NP/circuit, not P-vs-NP, and not Gate A.
The artifact still does not synthesize `B` from arbitrary
formulas, derive efficient recursive depth-`d` layered views from arbitrary
formula syntax, synthesize normalized/simple syntactic DNF views or global
efficient width profiles for arbitrary classes, prove a global efficient
`t(d,s)` theorem, or close full frozen-form B4.
The PHP switching lemma (Gate A rung 4 as a whole) remains open: the
collapse-probability analysis covers depth-1 events only —
single-literal/single-term (`PHPFullMatchingCollapseBound`), with the
single-literal event's probability additionally made exact and its
realizability certified in `PHPFullMatchingCollapseExact`, and the
multi-term DNF total-size union bound of `PHPFullMatchingDNFBound`; the
  restricted-DNF canonical-tree skeleton of `PHPFullMatchingCanonicalDT` is
  deterministic infrastructure only, `PHPFullMatchingBadPathEncoding` keeps
  the original matching point in a conservative optional-code count,
  `PHPFullMatchingCompressedBadPathCount` proves free-variable
  certification, a row-level free-set multiplicity count, and a conditional
  compressed-target count scaffold, and `PHPFullMatchingPathCodeFiberBound`
  proves the artifact's first compressed bad-path count whose encoder forgets
  the matching point, with each shared path-code fiber bounded by row-free
  multiplicity.  That compressed count is coarse: the path-code space is the
  support-based code space and only one guaranteed free row is exploited.
  No geometric term-count-independent depth-`t` collapse-probability bound
  over matchings,
  no depth-`t` canonical decision-tree encoding argument with per-stage
  information recovery, and no rectangular `p > h` matching-space result is
  proved.

## Re-Verification

```bash
lake env lean lean/PvNP/Audit.lean
```

Release-candidate audit helper:

```powershell
./scripts/audit-release.ps1
```
