# Formal Switching Lemma in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20757628.svg)](https://doi.org/10.5281/zenodo.20757628)

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

## Non-Claims Boundary

This artifact does **not** prove or imply:

- `P != NP` or `P = NP`;
- an NP or circuit lower bound;
- a Frege/PHP lower bound;
- arbitrary AC0 or arbitrary bounded-depth formula collapse;
- a general CNF switching lemma independent of the explicit dualization bridge.

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

## DOI

Version `v0.1.0` is archived on Zenodo under the repository concept DOI:

- DOI: `10.5281/zenodo.20757628`
- Release: `https://github.com/Quantyra/formal-switching-lemma/releases/tag/v0.1.0`

Version `v0.2.0` adds the audited CNF-dual bridge and explicit three-layer and
list-indexed k-layer schedule certificates. The release should be archived under
the same Zenodo concept DOI when the GitHub release is published.
