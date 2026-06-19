import PvNP.BoundedDepthIteratedCollapse
import PvNP.CertifiedAffine
import PvNP.RestrictedPHPFloor

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

/-- info: 'PvNP.BoundedDepthIteratedCollapse.dnfEval_cnfDualDNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.dnfEval_cnfDualDNF

/-- info: 'PvNP.BoundedDepthIteratedCollapse.simpleDNF_cnfDualDNF_of_simpleCNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.simpleDNF_cnfDualDNF_of_simpleCNF

/-- info: 'PvNP.BoundedDepthIteratedCollapse.bdFormula_cnfView_dual_switching_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.bdFormula_cnfView_dual_switching_collapse

/-- info: 'PvNP.BoundedDepthIteratedCollapse.threeLayerCollapse_exists_from_stagePremises' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.threeLayerCollapse_exists_from_stagePremises

/-- info: 'PvNP.BoundedDepthIteratedCollapse.oneLitThreeLayerCollapse_example_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.oneLitThreeLayerCollapse_example_nonvacuous

/-- info: 'PvNP.BoundedDepthIteratedCollapse.kLayerCollapse_exists_from_schedule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.kLayerCollapse_exists_from_schedule

/-- info: 'PvNP.BoundedDepthIteratedCollapse.oneLitKLayerSchedule3_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.oneLitKLayerSchedule3_nonempty

/-- info: 'PvNP.CertifiedAffine.incidentExtractor_completeOn' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.CertifiedAffine.incidentExtractor_completeOn

/-- info: 'PvNP.CertifiedAffine.incident_collision_endpoints' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.CertifiedAffine.incident_collision_endpoints

/-- info: 'PvNP.CertifiedAffine.certifiedAffineExtraction_completeOn' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.CertifiedAffine.certifiedAffineExtraction_completeOn

/-- info: 'PvNP.RestrictedPHPFloor.phpBoundary_formula_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.phpBoundary_formula_eq
