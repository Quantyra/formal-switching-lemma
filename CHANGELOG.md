# Changelog

## Unreleased

### Added

- **S2223** path-geometry image/carrier bound: add the `(G1, β)`-only
  fixed-grade image and prove the mcode-only carrier bound
  `|image_j| ≤ |honest(ell-j)| * (2w)^j`, plus the fixed `searchD4mp`, `w = 2`
  package target with `C = 4`.  Structural β/G1/walked coupling is preserved on
  the bad-domain wrapper.  No side-bit/free-stream tax, no residual preimage
  grind, no new force gate, no GA-4, P-vs-NP, or `v0.11.0` claim.
- **S2222** concrete path-geometry PairCode encode step: instantiate the S2221
  packet target with existing deterministic `encodeExt`, β-blocks, and coupled
  walked pairs; prove β well-formedness, G1 honest-space landing, walked length,
  and fixed `searchD4mp` wrapper pins.  Structural only: no residual
  unique-preimage grind, no side-bit/free-stream product tax, no new force,
  no GA-4, switching, P-vs-NP, or `v0.11.0` claim.
- **S2221** path-geometry force pivot target: after S2220 stop-lossed side-bit
  product counting, pin the next force lane as packet-native path geometry /
  coupled walked-pair encode (no free `Fin t → _` stream, no side-bit `4^j`
  tax), with a strict encoded-bad force gate and abstract `H·C^j` grade target.
  Reuses Fin4 `6/16` as regression-only gate witness.  No walked-pair recovery,
  no new counting bound, no GA-4, switching, P-vs-NP, or `v0.11.0` claim.
- **S2220 STOP-LOSS** side-bit force freeze: the S2218 side-bit factor only
  weakens the fixed-package S2214 count, so force requires a pivot; walked-pair
  recovery remains open as the residual-class freeze.  The package oracle is
  still `3072` **TRIVIAL** / exact `6` **STRICT**.  No GA-4, switching,
  P-vs-NP, or `v0.11.0` claim.
- **S2218** side-bit encode image landing: deep traces now supply an
  ell-independent side-bit stream, whose fixed-grade image is bounded by
  `|honest| * (2w)^j * 4^j`; source bounds remain conditional on injectivity
  in general and are instantiated only for the fixed `searchD4mp` package via
  its existing `G1`/`G2` injectivity.  This is not general GA-4, switching, a
  lower bound, or a `v0.11.0` result; `Fin 4` `6/16` remains regression-only.
- **S2217** parametric redesign force: an ell-independent side-bit carrier
  target with abstract grade bound `|honest| * (2w)^j * 4^j`, plus a generic
  encoded-bad ratio interface and fixed `Fin 4` `6/16` regression pin.  This
  does not supply GA-4 bad-domain injectivity or any switching/lower-bound
  conclusion.
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
