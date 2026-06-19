import PvNP.BoundedDepthIteratedCollapse

/-!
# Formal Switching Lemma Audit Surface

This module pins the axiom profile of the publication-facing theorem surface.
-/

/-- info: 'PvNP.SwitchingClose2.switchingLemmaTermSimple_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.SwitchingClose2.switchingLemmaTermSimple_proved

/-- info: 'PvNP.BoundedDepthFregeSwitchingBridge.bdDNF_switching_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFregeSwitchingBridge.bdDNF_switching_bridge

/-- info: 'PvNP.BoundedDepthLayerView.bdFormula_dnfView_switching_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthLayerView.bdFormula_dnfView_switching_collapse

/-- info: 'PvNP.BoundedDepthLayerView.emptyDNFView_switching_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthLayerView.emptyDNFView_switching_collapse

/-- info: 'PvNP.BoundedDepthIteratedCollapse.twoLayerCollapse_exists_from_stagePremises' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.twoLayerCollapse_exists_from_stagePremises

/-- info: 'PvNP.BoundedDepthIteratedCollapse.oneLitTwoLayerCollapse_example' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.oneLitTwoLayerCollapse_example
