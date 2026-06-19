# Formal Switching Lemma in Lean 4

This repository is a curated Lean 4 publication artifact for the `PvNP`
SimpleDNF switching-lemma line and its bounded-depth formula bridge.

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

## Non-Claims Boundary

This artifact does **not** prove or imply:

- `P != NP` or `P = NP`;
- an NP or circuit lower bound;
- a Frege/PHP lower bound;
- arbitrary AC0 or arbitrary bounded-depth formula collapse.

The CNF side of the two-layer result is an explicit schedule/premise record, not
a proved general CNF switching lemma. The repository is P-vs-NP-relevant
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

## DOI Preparation

This repository includes `.zenodo.json` and is ready for Zenodo activation. After
Zenodo is enabled by the owner, create a version tag such as `v0.1.0` and publish
the GitHub release to mint the DOI.
