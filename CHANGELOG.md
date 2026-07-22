# Changelog

## Unreleased

### Added

- S2216 Gate 2 FREEZE: stop residual grind; package oracle 6 STRICT / 3072
  TRIVIAL; handoff redesign.
- **S2215** Fin4/`searchD4mp`/`t = 3` ell-free package grade sum: the S2214
  `G1`+`G2` bound gives `3072`, still **TRIVIAL** versus honest denominator
  `16`; the independent S2209 exact card `6` remains **STRICT**. Package-only,
  not general GA-4 or a release claim.
- **S2214** Fin4/`searchD4mp`/`t = 3` discharge of the `G1`+`G2`
  length-two path-exit residual and its at-most-two-block grade bound.  This is
  package-only; the asymptotic stop-loss and general residual remain open.
- **S2213** conditional at-most-two entered-block answer-alphabet extension
  (`PHPMatchingEncodeAnswerAlphabetLengthTwo`): under the new `G1`+`G2`
  length-two path-exit residual, `G3` is redundant and the honest-times-mcode
  grade bound extends to this slice.  The package stop-loss remains in force.
- **S2212** at-most-one entered-block answer-alphabet slice
  (`PHPMatchingEncodeAnswerAlphabet`): `G1` and `G2` determine `G3` and give
  the honest-times-mcode grade bound on this slice only.  No general `G3`
  elimination or scaling of the Fin4 oracle result is claimed.
- **S2211** REDESIGN decision and first formal probe
  (`PHPMatchingEncodeAnswerRedesign`): replace ell-dependent `G3` with an
  ell-independent alphabet; the path-code pivot is rejected because its ratio
  worsens in `t`.  Proves the uniform `j ≤ t ≤ 2j` encode-image range and the
  pure honest-times-mcode grade bound without `(2ell)^t`.  This does not yet
  eliminate `G3`; the package remains stop-lossed.
- **S2210** uniform conditional-fiber infrastructure
  (`PHPMatchingEncodeConditionalFiber`): entered-payload fiber injects into
  honest `G1` space of free-count `ell-j`; payload-only fiber under the existing
  entered-term residual. Weak structural bounds only — not asymptotic GA-4.
- **S2209** exact Fin4/`searchD4mp`/t=3 bad-set classification: card = 6
  (strict vs honest denom 16). Oracle only; does not scale.
- **S2208** package mcode counting consumer: product bound TRIVIAL (663552 ≫ 16).
- **S2207** package subtype injectivity on the same Fin4 package.

### Stop-loss (package encode GA-4 asymptotic)

The current `G3 : Fin t → Fin (2·ell)` + mcode product route is **stop-lossed**
for asymptotic PHP switching: even with injectivity, the `(2ell)^t` factor
prevents a switching-quality ratio. Next work must redesign answer recovery
or pivot codes; do not claim GA-4 closure or tag v0.11.0 from this stack alone.

## [0.10.0] - 2026-07-20

### Added

- **S2187** GA-3 feed-parametric matching extension-encode infrastructure:
  vertex-query canonical matching DTs, walk traces/blocks/σ surfaces,
  star-code graded bounds, counterexample-disposal pins, and path-answer
  transport. Components are feed-parametric (externally supplied answer
  feed); this is encode bookkeeping, not a counting theorem.
- **S2188** deterministic `encodeMatch` assembly on top of S2187: leftmost
  live depth-preserving feed selection, exact tree-trace synchronization,
  and packaged graded encode components (G1/G2/G3) for square hole-injective
  base matchings.

### Boundary (unchanged)

This release does **not** claim injectivity of the encode, a bad-set
cardinality bound, a PHP switching lemma, Frege/PHP lower bounds, NP/circuit
lower bounds, or any P-vs-NP statement. Gate A rung 4 remains open.
