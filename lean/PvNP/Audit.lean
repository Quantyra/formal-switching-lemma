import PvNP.BoundedDepthFrege
import PvNP.BDResourceNormalization
import PvNP.BDTraceToSearchPremise
import PvNP.BoundedDepthIteratedCollapse
import PvNP.CertifiedAffine
import PvNP.GraphIndexedBridge
import PvNP.ProfiledRoutePHPBoundary
import PvNP.RestrictedPHPFloor
import PvNP.GeneratedGoodRestriction
import PvNP.GeneratedIteratedCollapse
import PvNP.GeneratedOneStepDepthReduction
import PvNP.RestrictionComposition
import PvNP.GeneratedIteratedCollapseFinal
import PvNP.RefinedSubspace
import PvNP.SwitchingRelabel
import PvNP.GeneratedRefinedCollapse
import PvNP.RefinedTwoStageInstance
import PvNP.RefinedThreeStageInstance
import PvNP.PHPMatchingDistribution
import PvNP.PHPFullMatchingDistribution
import PvNP.PHPFullMatchingProbability
import PvNP.TreePathViews
import PvNP.AutoReviewedIteration
import PvNP.ScheduledAutoCollapse
import PvNP.FrozenProductSchedule
import PvNP.FrozenProductScheduleDemo
import PvNP.FrozenProductScheduleRatio
import PvNP.FormulaFamilyCollapse
import PvNP.FrozenDepthView
import PvNP.FormulaTruthTableView
import PvNP.FormulaStructuralSchedule
import PvNP.MixedFormulaFamilyCollapse
import PvNP.ScheduledCollapseDemo

/-!
# Formal Switching Lemma Audit Surface

This module pins the axiom profile of the publication-facing theorem surface.
-/

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace.erase' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace.erase

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace.size' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace.size

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace.lineCount' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace.lineCount

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace.derivationDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace.derivationDepth

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace.sequentMaxFormulaDepth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace.sequentMaxFormulaDepth

/-- info: 'PvNP.BoundedDepthFrege.BDProofTrace.maxFormulaDepth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDProofTrace.maxFormulaDepth

/-- info: 'PvNP.BoundedDepthFrege.bdProofTrace_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.bdProofTrace_sound

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTrace

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTrace.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTrace.erase

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTrace.size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTrace.size

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTrace.lineCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTrace.lineCount

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTrace.derivationDepth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTrace.derivationDepth

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTrace.maxFormulaDepth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTrace.maxFormulaDepth

/-- info: 'PvNP.BoundedDepthFrege.bdFregeTrace_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.bdFregeTrace_sound

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTraceProfile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTraceProfile

/-- info: 'PvNP.BoundedDepthFrege.BDRefutationTraceProfile.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.BDRefutationTraceProfile.erase

/-- info: 'PvNP.BoundedDepthFrege.bdFregeTraceProfile_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthFrege.bdFregeTraceProfile_sound

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

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedDNFStage_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedDNFStage_exists

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedCNFStage_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedCNFStage_exists

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedTwoLayerCollapse_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedTwoLayerCollapse_exists

/-- info: 'PvNP.BoundedDepthIteratedCollapse.threeLayerCollapse_exists_from_stagePremises' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.threeLayerCollapse_exists_from_stagePremises

/-- info: 'PvNP.BoundedDepthIteratedCollapse.oneLitThreeLayerCollapse_example_nonvacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.oneLitThreeLayerCollapse_example_nonvacuous

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedThreeLayerCollapse_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedThreeLayerCollapse_exists

/-- info: 'PvNP.BoundedDepthIteratedCollapse.kLayerCollapse_exists_from_schedule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.kLayerCollapse_exists_from_schedule

/-- info: 'PvNP.BoundedDepthIteratedCollapse.GeneratedExplicitLayerStage.toExplicit_depthBound_eq_stageS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.GeneratedExplicitLayerStage.toExplicit_depthBound_eq_stageS

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedKLayerCollapse_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedKLayerCollapse_exists

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedNonemptyKLayerCollapse_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedNonemptyKLayerCollapse_exists

/-- info: 'PvNP.BoundedDepthIteratedCollapse.defaultAssignmentOfRestriction' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.defaultAssignmentOfRestriction

/-- info: 'PvNP.BoundedDepthIteratedCollapse.agree_defaultAssignmentOfRestriction' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.agree_defaultAssignmentOfRestriction

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedCNFSingletonSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedCNFSingletonSchedule

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedCNFSingletonSchedule_certificateConnection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedCNFSingletonSchedule_certificateConnection

/-- info: 'PvNP.BoundedDepthIteratedCollapse.ExplicitStageGeneratedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.ExplicitStageGeneratedCNFStageAlignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.GeneratedScheduleGeneratedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.GeneratedScheduleGeneratedCNFStageAlignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.generatedScheduleGeneratedCNFStageAlignment_iff_each' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.generatedScheduleGeneratedCNFStageAlignment_iff_each

/-- info: 'PvNP.BoundedDepthIteratedCollapse.not_generatedScheduleGeneratedCNFStageAlignment_of_failing_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.not_generatedScheduleGeneratedCNFStageAlignment_of_failing_member

/-- info: 'PvNP.BoundedDepthIteratedCollapse.SameArityStageGeneratedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.SameArityStageGeneratedCNFStageAlignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.sameArityStageGeneratedCNFStageAlignment_toExplicitStageGeneratedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.sameArityStageGeneratedCNFStageAlignment_toExplicitStageGeneratedCNFStageAlignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.SameArityGeneratedScheduleGeneratedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.SameArityGeneratedScheduleGeneratedCNFStageAlignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.sameArityGeneratedScheduleGeneratedCNFStageAlignment_toGeneratedScheduleGeneratedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.sameArityGeneratedScheduleGeneratedCNFStageAlignment_toGeneratedScheduleGeneratedCNFStageAlignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleAlignmentFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleAlignmentFamily

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_nonempty

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_length_le

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_alignment

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleAlignmentFamily_certificate

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleTheoremShell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleTheoremShell

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleTheoremShell_familyData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleTheoremShell_familyData

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleTheoremShell_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleTheoremShell_conditional

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleHypothesisClass' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleHypothesisClass

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleNamedHypothesis' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleNamedHypothesis

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_remainingProofComplexityHypotheses' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_remainingProofComplexityHypotheses

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_conditionalTarget' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_conditionalTarget

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_conditional' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_conditional

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_classifications' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_classifications

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleRouteObligationClass' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleRouteObligationClass

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleRouteObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleRouteObligation

/-- info: 'PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleRouteObligations' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.BoundedPositiveSameArityGeneratedScheduleRouteObligations

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_remainingProofComplexityHypotheses' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_remainingProofComplexityHypotheses

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_conditionalTarget' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_conditionalTarget

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_conditional' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_conditional

/-- info: 'PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_classifications' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.boundedPositiveSameArityGeneratedScheduleRouteObligations_classifications

/-- info: 'PvNP.BoundedDepthIteratedCollapse.oneLitKLayerSchedule3_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.oneLitKLayerSchedule3_nonempty

/-- info: 'PvNP.BoundedDepthIteratedCollapse.emptyGeneratedKLayerSchedule3_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.emptyGeneratedKLayerSchedule3_nonempty

/-- info: 'PvNP.BoundedDepthIteratedCollapse.emptyGeneratedKLayerSchedule4_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BoundedDepthIteratedCollapse.emptyGeneratedKLayerSchedule4_nonempty

/-- info: 'PvNP.CertifiedAffine.incidentExtractor_completeOn' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.CertifiedAffine.incidentExtractor_completeOn

/-- info: 'PvNP.CertifiedAffine.incident_collision_endpoints' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.CertifiedAffine.incident_collision_endpoints

/-- info: 'PvNP.CertifiedAffine.certifiedAffineExtraction_completeOn' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.CertifiedAffine.certifiedAffineExtraction_completeOn

/-- info: 'PvNP.GraphIndexedBridge.bridgeWitness_completeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.bridgeWitness_completeOn

/-- info: 'PvNP.GraphIndexedBridge.bridgeWitness_generatedNonemptyKLayerCollapse_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.bridgeWitness_generatedNonemptyKLayerCollapse_exists

/-- info: 'PvNP.GraphIndexedBridge.emptyGeneratedBridgeWitness3_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.emptyGeneratedBridgeWitness3_nonempty

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_nonempty

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_zero

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3ChargeProfile_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3ChargeProfile_eq

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3LaneANatCharge_eq_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3LaneANatCharge_eq_zero

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_laneANatCharge' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_laneANatCharge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_fin5NatBridge' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_fin5NatBridge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_laneAChargeInterfaceShim' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_laneAChargeInterfaceShim

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_laneAChargeInterfaceShim_fin5NatBridge' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_laneAChargeInterfaceShim_fin5NatBridge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_importedLaneACharge' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_eq_importedLaneACharge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3Charge_imported_fin5NatBridge' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3Charge_imported_fin5NatBridge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3TseitinGraph_chargeProfile' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3TseitinGraph_chargeProfile

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3TseitinGraph_edges_eq_importedLaneAEndpoints' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3TseitinGraph_edges_eq_importedLaneAEndpoints

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection_eq_importedLaneA' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection_eq_importedLaneA

/-- info: 'PvNP.GraphIndexedBridge.projectedLiteralEval_cnfLiteralProjection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.projectedLiteralEval_cnfLiteralProjection

/-- info: 'PvNP.GraphIndexedBridge.projectedClauseEval_cnfClauseProjection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.projectedClauseEval_cnfClauseProjection

/-- info: 'PvNP.GraphIndexedBridge.projectedCNFEval_cnfViewClauseProjection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.projectedCNFEval_cnfViewClauseProjection

/-- info: 'PvNP.GraphIndexedBridge.projectedCNFClauseEvaluations_cnfViewClauseProjection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.projectedCNFClauseEvaluations_cnfViewClauseProjection

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfSemanticEval_eq_importedLaneA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfSemanticEval_eq_importedLaneA

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_clauseSemanticEval_eq_importedLaneA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_clauseSemanticEval_eq_importedLaneA

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_chargeProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_chargeProfile

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_eq_laneANatCharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_eq_laneANatCharge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_fin5NatBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_fin5NatBridge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_eq_laneAChargeInterfaceShim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_eq_laneAChargeInterfaceShim

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_laneAChargeInterfaceShim_fin5NatBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_laneAChargeInterfaceShim_fin5NatBridge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_eq_importedLaneACharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_eq_importedLaneACharge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_importedGraphChargeAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_importedGraphChargeAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_importedGraphChargeFormulaAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_importedGraphChargeFormulaAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_importedGraphChargeFormulaSemanticAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_importedGraphChargeFormulaSemanticAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_finiteCNFSemanticBridgeConsumer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_finiteCNFSemanticBridgeConsumer

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_sixCNFCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_sixCNFCompatible

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_not_sixCNFCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_not_sixCNFCompatible

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_finiteCNFCompatibilityGate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_finiteCNFCompatibilityGate

/-- info: 'PvNP.GraphIndexedBridge.eval_cnfToBD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.eval_cnfToBD

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfViewStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfViewStage

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage_compatible' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage_compatible

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_sixCNFConcreteInvariant' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_sixCNFConcreteInvariant

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_dualDNF_width_le_four' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_dualDNF_width_le_four

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_dnfSize' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_dnfSize

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_good

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_concreteInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_concreteInvariant

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_kLayerCompatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_kLayerCompatibility

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_reusableCertificateConnection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_reusableCertificateConnection

/-- info: 'PvNP.GraphIndexedBridge.ExplicitStageGeneratedCNFStageInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.ExplicitStageGeneratedCNFStageInvariant

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_generatedCNFStageInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_generatedCNFStageInvariant

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_certificateBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_certificateBoundary

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignmentObstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignmentObstruction

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignment_iff_each' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignment_iff_each

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_crossArityScheduleAlignmentBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_crossArityScheduleAlignmentBoundary

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_sameArityAssignmentLiftAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_sameArityAssignmentLiftAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_sameAritySelfAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_sameAritySelfAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_sameArityAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_sameArityAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_generatedCNFStageAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_generatedCNFStageAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_selfAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_selfAlignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_length

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_aligns_each' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_aligns_each

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_alignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveVsOldScheduleAlignmentBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveVsOldScheduleAlignmentBoundary

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_specializes

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_length_le

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_alignment

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamilyBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamilyBoundary

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedDataHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedDataHypothesis

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactHypothesis

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryHypothesis' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryHypothesis

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_localTheoremTargetHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_localTheoremTargetHypothesis

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlocker' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlocker

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerHypothesis' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerHypothesis

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomyClassifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomyClassifications

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy_classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy_classifications

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedFamilyDataRouteObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedFamilyDataRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactRouteObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryRouteObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTargetRouteObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTargetRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerRouteObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligationsClassifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligationsClassifications

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_classifications

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_firstLocalTheoremTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_firstLocalTheoremTarget

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell_nonvacuous

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShellBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShellBoundary

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget_proved

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_provedFirstLocalTargetAuditedFiniteFactRouteObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_provedFirstLocalTargetAuditedFiniteFactRouteObligation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts_proved

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RouteObligationBookkeeping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RouteObligationBookkeeping

/-- info: 'PvNP.GraphIndexedBridge.TwoCyclePath3PositiveAlignedSuppliedBDRefutationRoute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.TwoCyclePath3PositiveAlignedSuppliedBDRefutationRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute_of_refutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute_of_refutation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_suppliedBDRefutationRoute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_suppliedBDRefutationRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_normalization' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_normalization

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProof

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProofTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProofTrace

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_vars23FourMintermNegatedSequent_bdProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_vars23FourMintermNegatedSequent_bdProof

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProof

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProofTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProofTrace

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProof

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace_erases_to_bdProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace_erases_to_bdProof

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erasedBDRefutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erasedBDRefutation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erases_to_suppliedBDRefutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erases_to_suppliedBDRefutation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_size

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_lineCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_lineCount

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_derivationDepth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_derivationDepth

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_maxFormulaDepth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_maxFormulaDepth

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_erasedBDRefutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_erasedBDRefutation

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTraceProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTraceProfile

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTrace

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutation

/-- info: 'PvNP.GraphIndexedBridge.TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute_erases_to_suppliedBDRefutationRoute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute_erases_to_suppliedBDRefutationRoute

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_resourceNormalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_resourceNormalization

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetEqualities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetEqualities

/-- info: 'PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GraphIndexedBridge.twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_budgetPins

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile.ofCorrectTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile.ofCorrectTree

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile.ofEvalSelector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile.ofEvalSelector

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile.depthFloor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseForProfile.depthFloor

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.ofCorrectTree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.ofCorrectTree

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.ofEvalSelector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.ofEvalSelector

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.boundaryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteShell.boundaryFacts

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchRouteObligationClass' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchRouteObligationClass

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchRouteObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchRouteObligation

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchRouteObligations' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchRouteObligations

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_remainingRouteObligations' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_remainingRouteObligations

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_suppliedProfiledRouteResourceFacts' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_suppliedProfiledRouteResourceFacts

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_suppliedFixedFiniteSearchPremiseFacts' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_suppliedFixedFiniteSearchPremiseFacts

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_localFutureBridgeTarget' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_localFutureBridgeTarget

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_classifications' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchRouteObligations_classifications

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsRouteObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsRouteObligation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsRouteObligation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsRouteObligation

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligationNamed' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligationNamed

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_unresolvedProofComplexityBlockerRouteObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_unresolvedProofComplexityBlockerRouteObligation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligationsClassifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligationsClassifications

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations_classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseRouteObligations_classifications

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.ofCorrectTree' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.ofCorrectTree

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.ofEvalSelector' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.ofEvalSelector

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.toSearchPremise' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.toSearchPremise

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.depthFloor' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.depthFloor

/-- info: 'PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.toSearchPremise_tree' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.ThreeTwoPHPSearchPremiseInputsForProfile.toSearchPremise_tree

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.localBridgeObligation_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.localBridgeObligation_project

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.searchPremise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.searchPremise

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.routeShell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.routeShell

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.routeShell_boundaryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeEvidence.routeShell_boundaryFacts

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget_concrete

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchLocalBridgeAntecedentClass' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchLocalBridgeAntecedentClass

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchLocalBridgeAntecedent' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchLocalBridgeAntecedent

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchLocalBridgeAntecedents' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchLocalBridgeAntecedents

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_remainingAntecedents' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_remainingAntecedents

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_suppliedProfiledRouteResourceFacts' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_suppliedProfiledRouteResourceFacts

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_suppliedFixedFiniteSearchPremiseFacts' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_suppliedFixedFiniteSearchPremiseFacts

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_traceToSearchExtraction' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_traceToSearchExtraction

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_selectorTransfer' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_selectorTransfer

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_profileCompatibility' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_profileCompatibility

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_classifications' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchLocalBridgeAntecedents_classifications

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsAntecedent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFactsAntecedent

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsAntecedent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFactsAntecedent

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingTraceToSearchExtractionAntecedent' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingTraceToSearchExtractionAntecedent

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingSelectorTransferAntecedent' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingSelectorTransferAntecedent

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingProfileCompatibilityAntecedent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_missingProfileCompatibilityAntecedent

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedentsClassifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedentsClassifications

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents_classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents_classifications

/-- info: 'PvNP.BDTraceToSearchPremise.TraceProfileToQueryExtractionBridgeObligation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceProfileToQueryExtractionBridgeObligation

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.profile_eq_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.profile_eq_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.tree_eq_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.tree_eq_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.profileBudgetPins_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.profileBudgetPins_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.selectorEval_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.selectorEval_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.traceProfileToQueryBridge_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.traceProfileToQueryBridge_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.ofSemanticFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionConstructorFieldObligation.ofSemanticFields

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionRelation.constructorField_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionRelation.constructorField_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionRelation.ofConstructorField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionRelation.ofConstructorField

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchSelectorTransferEvidence' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchSelectorTransferEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchSelectorTransferEvidence.searchCorrect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchSelectorTransferEvidence.searchCorrect

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.extractionRelation_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.extractionRelation_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.selectorTransfer_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.selectorTransfer_project

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.toSearchPremiseInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.toSearchPremiseInputs

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.toSearchPremiseInputs_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.toSearchPremiseInputs_tree

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.toSearchPremise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.toSearchPremise

/-- info: 'PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.depthFloor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceToSearchExtractionWitnessForProfile.depthFloor

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchProfileCompatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchProfileCompatibility

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.profileCompatibility_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.profileCompatibility_project

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.extractionWitness_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.extractionWitness_project

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.toSearchPremiseInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.toSearchPremiseInputs

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.toSearchPremise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.toSearchPremise

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.routeShell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.routeShell

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.routeShell_boundaryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3TraceToSearchExtractionWitnessContract.routeShell_boundaryFacts

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteSelectorTransferEvidence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteSelectorTransferEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteProfileCompatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteProfileCompatibility

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileWitnessShell_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileWitnessShell_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeContractShell_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_tree_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremiseInputs_tree_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremise_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_searchPremise_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_boundaryFacts_of_suppliedConcreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_routeShell_boundaryFacts_of_suppliedConcreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationAntecedent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationAntecedent

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceToSearchExtractionObstructionMap

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_remainingExtractionObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_remainingExtractionObligation

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_selectorTransferEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_selectorTransferEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_profileCompatibilityEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_profileCompatibilityEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionObstructionMap_concreteExtractionRelation_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_remainingTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_remainingTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_selectorTransferEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_selectorTransferEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_profileCompatibilityEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_profileCompatibilityEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionObstructionMap_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_constructorField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_constructorField

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_constructorField_to_concreteTraceToSearchExtractionRelationTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_constructorField_to_concreteTraceToSearchExtractionRelationTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_iff_constructorFieldTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_iff_constructorFieldTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldAntecedent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldAntecedent

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldObstructionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldObstructionMap

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionConstructorFieldObstructionMap_remainingConstructorFieldObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionConstructorFieldObstructionMap_remainingConstructorFieldObligation

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionConstructorFieldObstructionMap_constructorField_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConcreteExtractionConstructorFieldObstructionMap_constructorField_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap_remainingTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap_remainingTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldObstructionMap_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_traceProfileToQueryBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_traceProfileToQueryBridge

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceProfileToQueryBridge_to_concreteConstructorFieldTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceProfileToQueryBridge_to_concreteConstructorFieldTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_iff_traceProfileToQueryBridgeTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldTarget_iff_traceProfileToQueryBridgeTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeAntecedent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeAntecedent

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceToSearchExtractionConstructorFieldSemanticDecomposition

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_remainingTraceProfileToQueryBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_remainingTraceProfileToQueryBridge

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_selectorTransferEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_selectorTransferEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_profileCompatibilityEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_profileCompatibilityEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_traceProfileToQueryBridge_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceToSearchConstructorFieldSemanticDecomposition_traceProfileToQueryBridge_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_remainingTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_remainingTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_selectorTransferEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_selectorTransferEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_profileCompatibilityEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteConstructorFieldSemanticDecomposition_profileCompatibilityEvidence

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSuppliedFiniteSemantics

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingBridgeObligation

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_traceProfileToQueryBridge_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_traceProfileToQueryBridge_classification

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_remainingTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_suppliedFiniteSemantics

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeSemanticFieldObstructionMap_classification

/-- info: 'PvNP.BDTraceToSearchPremise.TraceProfileToQueryBridgeRequirementClass' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceProfileToQueryBridgeRequirementClass

/-- info: 'PvNP.BDTraceToSearchPremise.TraceProfileToQueryBridgeRequirement' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceProfileToQueryBridgeRequirement

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFiniteSemanticsBridgeRequirement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFiniteSemanticsBridgeRequirement

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_remainingTraceProfileToQueryBridgeRequirement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_remainingTraceProfileToQueryBridgeRequirement

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityBridgeRequirement' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityBridgeRequirement

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureBridgeRequirement' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureBridgeRequirement

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationBridgeRequirement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationBridgeRequirement

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_familyGeneralizationBridgeRequirement' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_familyGeneralizationBridgeRequirement

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryBridgeRequirementsDecomposition

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_instanceCompatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_instanceCompatibility

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_extractionProcedure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_extractionProcedure

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_resourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_resourcePreservation

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_familyGeneralization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_familyGeneralization

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeRequirementsDecomposition_classifications

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingBridgeTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingBridgeTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_classifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_classifications

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements

/-- info: 'PvNP.BDTraceToSearchPremise.TraceProfileToQueryBridgeInterfaceContractFields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TraceProfileToQueryBridgeInterfaceContractFields

/-- info: 'PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.TwoCyclePath3ConcreteTraceProfileToQueryBridgeInterfaceContract

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_requiredFieldStatements

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_instanceCompatibilityStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_instanceCompatibilityStatement

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_extractionProcedureShapeStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_extractionProcedureShapeStatement

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_resourcePreservationStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_resourcePreservationStatement

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_familyGeneralizationTargetStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_familyGeneralizationTargetStatement

/-- info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_requirementClassifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryBridgeInterfaceContract_requirementClassifications

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_remainingBridgeTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_remainingBridgeTarget

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements

/-- info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requirementClassifications' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requirementClassifications

/-- info: 'PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary

/-- info: 'PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_of_evalSelector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_of_evalSelector

/-- info: 'PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree

/-- info: 'PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree_resourceBudgetPins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PvNP.twoCyclePath3GeneratedBridgeWitness_profiledRoute_threeTwoPHPSearchBoundary_concreteQueryTree_resourceBudgetPins

/-- info: 'PvNP.RestrictedPHPFloor.phpBoundary_formula_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.phpBoundary_formula_eq

/-- info: 'PvNP.RestrictedPHPFloor.eval_tinyOneOneRestrictedPHPFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.eval_tinyOneOneRestrictedPHPFormula

/-- info: 'PvNP.RestrictedPHPFloor.tinyOneOnePHPDepthFloor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.tinyOneOnePHPDepthFloor

/-- info: 'PvNP.RestrictedPHPFloor.twoOnePHPFalsifiedClauseSearchDepthFloor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.twoOnePHPFalsifiedClauseSearchDepthFloor

/-- info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSelector' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSelector

/-- info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSelector_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSelector_valid

/-- info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector

/-- info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseQueryTree' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseQueryTree

/-- info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseQueryTree_evalSelector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseQueryTree_evalSelector

/-- info: 'PvNP.RestrictedPHPFloor.queryTree_depth_ge_two_of_two_unqueried_ambiguity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.queryTree_depth_ge_two_of_two_unqueried_ambiguity

/-- info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor

/-! ## S2065/S2066 proved concrete extraction bridge and `3 x 2` search floor of three

Pins for the S2065 trace/profile-to-query extraction bridge (module
`PvNP.BDTraceToSearchExtraction` and the proved S2052-S2064 obligations in
`PvNP.BDTraceToSearchPremise`) and the S2066 `3 x 2` falsified-clause
search depth floor of three (`PvNP.RestrictedPHPFloor`).  These are finite
concrete-instance results only: not lower bounds, not Frege/PHP results, and
not P vs NP statements.  The genuine open proof-complexity route obligation
remains the untouched empty
`twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation`.
-/

/-- info: 'PvNP.BDTraceToSearchExtraction.phpVarEmbedding' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.phpVarEmbedding

/-- info: 'PvNP.BDTraceToSearchExtraction.phpVarEmbedding_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.phpVarEmbedding_injective

/-- info: 'PvNP.BDTraceToSearchExtraction.traceQueryOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.traceQueryOrder

/-- info: 'PvNP.BDTraceToSearchExtraction.buildTree' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.buildTree

/-- info: 'PvNP.BDTraceToSearchExtraction.buildTree_evalSelector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.buildTree_evalSelector

/-- info: 'PvNP.BDTraceToSearchExtraction.extractQueryTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.extractQueryTree

/--
info: 'PvNP.BDTraceToSearchExtraction.extractQueryTree_evalSelector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.extractQueryTree_evalSelector

/--
info: 'PvNP.BDTraceToSearchExtraction.extractQueryTree_matchesFixedTree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.extractQueryTree_matchesFixedTree

/--
info: 'PvNP.BDTraceToSearchExtraction.extractQueryTree_searchCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.extractQueryTree_searchCorrect

/-- info: 'PvNP.BDTraceToSearchExtraction.extractQueryTree_depthFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.extractQueryTree_depthFloor

/--
info: 'PvNP.BDTraceToSearchExtraction.extractQueryTree_depthFloor_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.extractQueryTree_depthFloor_three

/-- info: 'PvNP.BDTraceToSearchExtraction.twoCyclePath3_cnfBDFormula_eval_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.twoCyclePath3_cnfBDFormula_eval_false

/-- info: 'PvNP.BDTraceToSearchExtraction.twoCyclePath3ThreeTwoPHP_commonExtension' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.twoCyclePath3ThreeTwoPHP_commonExtension

/-- info: 'PvNP.BDTraceToSearchExtraction.fixedTree_queryDepth_eq_six' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchExtraction.fixedTree_queryDepth_eq_six

/--
info: 'PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridge_toFixedTree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.traceProfileToQueryExtractionBridge_toFixedTree

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryExtractionBridgeTarget_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionConstructorFieldTarget_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceToSearchExtractionRelationTarget_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionWitnessContractTarget_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell_boundaryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_provedRouteShell_boundaryFacts

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_localFutureBridgeRouteObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_explicitLocalFutureBridgeTarget_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceToSearchExtractionObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_selectorTransferObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_profileCompatibilityObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedProfiledRouteResourceFacts_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts_proved' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_suppliedFixedFiniteSearchPremiseFacts_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents_remainingAntecedents_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremiseLocalBridgeAntecedents_remainingAntecedents_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_instanceCompatibilityObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_extractionProcedureObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_resourcePreservationObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_traceFamilyGeneralizationObligation_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeRequirementsDecomposition_remainingMissingRequirements_proved

/--
info: 'PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTraceToSearchPremise.twoCyclePath3TraceToThreeTwoPHPSearchPremise_concreteTraceProfileToQueryBridgeInterfaceContract_requiredFieldStatements_proved

/--
info: 'PvNP.RestrictedPHPFloor.queryTree_depth_ge_three_of_adversary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.queryTree_depth_ge_three_of_adversary

/--
info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_three

/--
info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseQueryTree_depth_ge_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseQueryTree_depth_ge_three

/-- info: 'PvNP.RestrictedPHPFloor.FalsifiedClauseSearchDepthFloorStatement' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.FalsifiedClauseSearchDepthFloorStatement

/-- info: 'PvNP.RestrictedPHPFloor.twoOnePHPFalsifiedClauseSearchDepthFloorStatement_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.twoOnePHPFalsifiedClauseSearchDepthFloorStatement_two

/--
info: 'PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloorStatement_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictedPHPFloor.threeTwoPHPFalsifiedClauseSearchDepthFloorStatement_three

/-! ## M-C1: variable-coverage floors, parameterized PHP search floor of `2h`,
and the genuinely trace-dependent extraction

Pins for the M-C1 milestone: non-standard-semantics soundness and the
variable-coverage theorem (`PvNP.BDVariableCoverage`), the PHP CNF and its
concrete `3 x 2` full-coverage floors (`PvNP.PHPCNFCoverage`), the
parameterized `p x h` falsified-clause search depth floor of `2 * h` via a
reusable generic stateful adversary with `3 x 2` non-vacuity and the
strengthened bespoke floor of four (`PvNP.PHPSearchFloor`), the unpadded
trace-dependent extraction and the composed refutation-to-search route
(`PvNP.TraceSearchConnection`), and the growing-family coverage floors for
`phpCNF (h+1) h` (`PvNP.PHPFamilyCoverage`).

HONEST SCOPE: coverage floors are variable-coverage floors, LINEAR in the number of PHP variables, on
refutation traces of the LOCAL cut-free bounded-depth Tait system; the search
floor is a decision-tree bound for the falsified-clause SEARCH family.  None
of these is a Frege/PHP proof-size lower bound for a system with cut, an
NP/circuit lower bound, or a statement about P vs NP.  The genuine open
proof-complexity route obligation remains the untouched empty
`twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation`.
-/

/--
info: 'PvNP.BDVariableCoverage.evalNS' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDVariableCoverage.evalNS

/--
info: 'PvNP.BDVariableCoverage.bdProofTrace_sound_nonstandard' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDVariableCoverage.bdProofTrace_sound_nonstandard

/--
info: 'PvNP.BDVariableCoverage.evalNS_neg_cnf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDVariableCoverage.evalNS_neg_cnf

/--
info: 'PvNP.BDVariableCoverage.refutationTrace_falsifiedClause_in_cover' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDVariableCoverage.refutationTrace_falsifiedClause_in_cover

/--
info: 'PvNP.BDVariableCoverage.refutationTrace_queries_var' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDVariableCoverage.refutationTrace_queries_var

/--
info: 'PvNP.BDVariableCoverage.traceQueryOrder_length_le_size' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms PvNP.BDVariableCoverage.traceQueryOrder_length_le_size

/--
info: 'PvNP.PHPCNFCoverage.phpCNF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPCNFCoverage.phpCNF

/--
info: 'PvNP.PHPCNFCoverage.phpCNF32_refutationTrace_queries_all' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPCNFCoverage.phpCNF32_refutationTrace_queries_all

/--
info: 'PvNP.PHPCNFCoverage.phpCNF32_traceQueryOrder_length_ge_six' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPCNFCoverage.phpCNF32_traceQueryOrder_length_ge_six

/--
info: 'PvNP.PHPCNFCoverage.phpCNF32_traceSize_ge_six' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPCNFCoverage.phpCNF32_traceSize_ge_six

/-- info: 'PvNP.PHPSearchFloor.PHPFalsifiedClause.Valid' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.PHPFalsifiedClause.Valid

/--
info: 'PvNP.PHPSearchFloor.queryTree_depth_floor_of_stateful_adversary' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.queryTree_depth_floor_of_stateful_adversary

/--
info: 'PvNP.PHPSearchFloor.phpInv_update' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.phpInv_update

/--
info: 'PvNP.PHPSearchFloor.phpLeaf_refutable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.phpLeaf_refutable

/--
info: 'PvNP.PHPSearchFloor.phpFalsifiedClauseSearchDepthFloor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.phpFalsifiedClauseSearchDepthFloor

/--
info: 'PvNP.PHPSearchFloor.phpFalsifiedClauseSearchDepthFloorStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.phpFalsifiedClauseSearchDepthFloorStatement

/--
info: 'PvNP.PHPSearchFloor.phpFalsifiedClause32_correctTree_exists' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.phpFalsifiedClause32_correctTree_exists

/--
info: 'PvNP.PHPSearchFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_four

/--
info: 'PvNP.TraceSearchConnection.extractQueryTreeUnpadded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.TraceSearchConnection.extractQueryTreeUnpadded

/--
info: 'PvNP.TraceSearchConnection.extractQueryTreeUnpadded_evalSelector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.TraceSearchConnection.extractQueryTreeUnpadded_evalSelector

/--
info: 'PvNP.TraceSearchConnection.extractQueryTreeUnpadded_searchCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.TraceSearchConnection.extractQueryTreeUnpadded_searchCorrect

/-- info: 'PvNP.TraceSearchConnection.buildTree_nil_incorrect' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.TraceSearchConnection.buildTree_nil_incorrect

/--
info: 'PvNP.TraceSearchConnection.extractQueryTreeUnpadded_depth' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.TraceSearchConnection.extractQueryTreeUnpadded_depth

/--
info: 'PvNP.TraceSearchConnection.phpCNF32_traceQueryOrder_length_ge_four_via_search' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.TraceSearchConnection.phpCNF32_traceQueryOrder_length_ge_four_via_search

/--
info: 'PvNP.PHPFamilyCoverage.phpCNF_family_refutationTrace_queries_var' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyCoverage.phpCNF_family_refutationTrace_queries_var

/--
info: 'PvNP.PHPFamilyCoverage.phpCNF_family_traceQueryOrder_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyCoverage.phpCNF_family_traceQueryOrder_length

/--
info: 'PvNP.PHPFamilyCoverage.phpCNF_family_traceSize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyCoverage.phpCNF_family_traceSize

/-! ## S2068: completeness of the local Tait system, PHP-family non-vacuity,
and formalized `3 x 2` search-floor tightness

Pins for `PvNP.BDTaitCompleteness` (every unsatisfiable CNF admits a
bounded-depth refutation trace; `PHP(h+1,h)` unsatisfiability via the finite
pigeonhole principle; nonemptiness of the refutation-trace types the M-C1
coverage floors quantify over) and `PvNP.PHPSearchFloorTightness` (explicit
correct depth-four `3 x 2` search tree; optimal worst-case query count exactly
four).  Completeness alone proves no hardness; none of this is a Frege/PHP,
NP/circuit, or P vs NP statement.
-/

/--
info: 'PvNP.BDTaitCompleteness.tait_cubes_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTaitCompleteness.tait_cubes_complete

/-- info: 'PvNP.BDTaitCompleteness.neg_cnfToBD_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.BDTaitCompleteness.neg_cnfToBD_eq

/--
info: 'PvNP.BDTaitCompleteness.bdTait_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTaitCompleteness.bdTait_complete

/--
info: 'PvNP.BDTaitCompleteness.phpCNF_family_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTaitCompleteness.phpCNF_family_unsat

/--
info: 'PvNP.BDTaitCompleteness.phpCNF_family_refutationTrace_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTaitCompleteness.phpCNF_family_refutationTrace_nonempty

/--
info: 'PvNP.BDTaitCompleteness.phpCNF32_refutationTrace_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.BDTaitCompleteness.phpCNF32_refutationTrace_nonempty

/-- info: 'PvNP.PHPSearchFloorTightness.optimalThreeTwoTree' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.PHPSearchFloorTightness.optimalThreeTwoTree

/--
info: 'PvNP.PHPSearchFloorTightness.optimalThreeTwoTree_searchCorrect' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloorTightness.optimalThreeTwoTree_searchCorrect

/-- info: 'PvNP.PHPSearchFloorTightness.optimalThreeTwoTree_depth' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.PHPSearchFloorTightness.optimalThreeTwoTree_depth

/--
info: 'PvNP.PHPSearchFloorTightness.threeTwoPHPFalsifiedClauseSearch_optimal_depth_eq_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPSearchFloorTightness.threeTwoPHPFalsifiedClauseSearch_optimal_depth_eq_four

/-! ## S2069: the family trace-to-search route

Pins for `PvNP.PHPFamilyTraceSearchRoute`: the total valid selector for the
`(h+1) x h` falsified-clause search problem (finite pigeonhole), the family
unpadded extraction whose depth is exactly the trace's `litEM` query-order
length, and the composed family bounds `2*h <=` query-order length / trace
size THROUGH the search connection.  Variable-coverage-grade bounds for the
LOCAL cut-free Tait trace system; NOT Frege/PHP, NP/circuit, or P vs NP
statements.
-/

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpFalsifiedClause_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpFalsifiedClause_exists

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpSelector_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpSelector_valid

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpBuildTree_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpBuildTree_eval

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpExtractTree_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpExtractTree_eval

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpExtractTree_searchCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpExtractTree_searchCorrect

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpExtractTree_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpExtractTree_depth

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpCNF_family_traceQueryOrder_length_ge_two_h_via_search' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpCNF_family_traceQueryOrder_length_ge_two_h_via_search

/--
info: 'PvNP.PHPFamilyTraceSearchRoute.phpCNF_family_traceSize_ge_two_h_via_search' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFamilyTraceSearchRoute.phpCNF_family_traceSize_ge_two_h_via_search

/-! ## S2071: family Boolean depth floor for satisfiable PHP (evasiveness)

Pins for `PvNP.PHPBooleanDepthFloor`: the first FAMILY instance of
`RestrictedPHPFloor.PHPDepthFloorStatement` beyond the `1 x 1` boundary — for
every `h`, any decision tree computing the SATISFIABLE `h x h` pigeonhole
Boolean function under the empty restriction has depth at least `h * h`
(evasiveness, by full sensitivity at the identity permutation point), with a
correct tree of depth `h*h + 1` witnessing non-vacuity.  Empty restriction
family only; elementary/classical mathematics; NOT a Frege/PHP proof-size
bound, NOT an NP/circuit bound, NOT P vs NP.
-/

/--
info: 'PvNP.PHPBooleanDepthFloor.eval_idAssignment_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.eval_idAssignment_true

/--
info: 'PvNP.PHPBooleanDepthFloor.eval_flip_idAssignment_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.eval_flip_idAssignment_false

/--
info: 'PvNP.PHPBooleanDepthFloor.dtPathVars_length_le_depth' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.dtPathVars_length_le_depth

/--
info: 'PvNP.PHPBooleanDepthFloor.dtEval_flipAt_of_not_mem_path' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.dtEval_flipAt_of_not_mem_path

/--
info: 'PvNP.PHPBooleanDepthFloor.fullPHPBoundary_depthFloor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.fullPHPBoundary_depthFloor

/--
info: 'PvNP.PHPBooleanDepthFloor.fullPHPBoundary_correctTree_exists' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.fullPHPBoundary_correctTree_exists

/--
info: 'PvNP.PHPBooleanDepthFloor.dtOfFun_eval' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPBooleanDepthFloor.dtOfFun_eval

/-! ## S2072: depth floors under partial-matching restrictions

Pins for `PvNP.PHPRestrictedDepthFloor`: the Gate A rung after S2071 —
`PHPDepthFloorStatement` instances with NONTRIVIAL restriction families.  The
master theorem gives, for EVERY partial-matching restriction (any fixed pigeon
set `S`, any permutation `f`), a depth floor equal to the number of free
variables (the restricted function stays evasive on its free grid, by full
sensitivity at the permutation point of `f`); the canonical two-parameter
boundary family fixes the first `s` pigeons along the identity with floor
`(h - s) * h`.  Worst-case per-restriction floors; NOT the probabilistic
random-restriction statements the switching lemma consumes, NOT a Frege/PHP
proof-size bound, NOT NP/circuit, NOT P vs NP.
-/

/--
info: 'PvNP.PHPRestrictedDepthFloor.eval_permAssignment_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.eval_permAssignment_true

/--
info: 'PvNP.PHPRestrictedDepthFloor.eval_flip_permAssignment_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.eval_flip_permAssignment_false

/--
info: 'PvNP.PHPRestrictedDepthFloor.permAssignment_agrees' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.permAssignment_agrees

/--
info: 'PvNP.PHPRestrictedDepthFloor.flip_agrees' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.flip_agrees

/--
info: 'PvNP.PHPRestrictedDepthFloor.matchingRestriction_depthFloor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.matchingRestriction_depthFloor

/--
info: 'PvNP.PHPRestrictedDepthFloor.matchingBoundary_depthFloor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.matchingBoundary_depthFloor

/--
info: 'PvNP.PHPRestrictedDepthFloor.matchingBoundary_correctTree_exists' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.matchingBoundary_correctTree_exists

/--
info: 'PvNP.PHPRestrictedDepthFloor.freeRows_thresholdS_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPRestrictedDepthFloor.freeRows_thresholdS_length

/-! ## S2073: the uniform matching-restriction space with exact star counting

Pins for `PvNP.PHPMatchingDistribution` (Gate A rung 3, first increment): the
uniform `s`-subset restriction space (`choose h s` elements), the exact
star/fix counts per variable (`choose (h-1) s` free /
`choose h s - choose (h-1) s` fixed), the exact star-probability ratio in
counting form (`h * choose (h-1) s = (h - s) * choose h s`), and the
probability-one transfer of the S2072 floor (every point of the space keeps
depth >= (h-s)*h for correct trees), with per-point non-vacuity.  Counting
form only — NOT a switching lemma (no collapse-probability upper bound is
stated), NOT Frege/PHP proof-size, NOT NP/circuit, NOT P vs NP.
-/

/--
info: 'PvNP.PHPMatchingDistribution.card_subsetSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.card_subsetSpace

/--
info: 'PvNP.PHPMatchingDistribution.restrictionOf_phpVar_eq_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.restrictionOf_phpVar_eq_none_iff

/--
info: 'PvNP.PHPMatchingDistribution.freeCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.freeCount_eq

/--
info: 'PvNP.PHPMatchingDistribution.fixCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.fixCount_eq

/--
info: 'PvNP.PHPMatchingDistribution.star_ratio' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.star_ratio

/--
info: 'PvNP.PHPMatchingDistribution.phpVar_freeCount' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.phpVar_freeCount

/--
info: 'PvNP.PHPMatchingDistribution.subsetSpace_depthFloor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.subsetSpace_depthFloor

/--
info: 'PvNP.PHPMatchingDistribution.subsetSpace_correctTree_exists' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPMatchingDistribution.subsetSpace_correctTree_exists

/-! ## Gate A rung 3: full square matching-restriction distribution

Pins for `PvNP.PHPFullMatchingDistribution`: the full square `h x h`
matching-restriction space as `subsetSpace h s x Equiv.Perm (Fin h)`, exact
cardinality and per-variable star counts with the permutation factor, the
same star-ratio counting identity over that richer space, probability-one
transfer of the S2072 floor to every point, and per-point non-vacuity. Counting
form only -- NOT a switching lemma (no collapse-probability upper bound is
stated), NOT the rectangular `p > h` injection space, NOT Frege/PHP proof-size,
NOT NP/circuit, NOT P vs NP.
-/

/--
info: 'PvNP.PHPFullMatchingDistribution.card_fullMatchingSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.card_fullMatchingSpace

/--
info: 'PvNP.PHPFullMatchingDistribution.fullRestrictionOf_phpVar_eq_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.fullRestrictionOf_phpVar_eq_none_iff

/--
info: 'PvNP.PHPFullMatchingDistribution.phpVar_freeCount_full' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.phpVar_freeCount_full

/--
info: 'PvNP.PHPFullMatchingDistribution.star_ratio_full' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.star_ratio_full

/--
info: 'PvNP.PHPFullMatchingDistribution.phpVar_star_ratio_full' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.phpVar_star_ratio_full

/--
info: 'PvNP.PHPFullMatchingDistribution.fullMatchingSpace_depthFloor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.fullMatchingSpace_depthFloor

/--
info: 'PvNP.PHPFullMatchingDistribution.fullMatchingSpace_correctTree_exists' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingDistribution.fullMatchingSpace_correctTree_exists

/-! ## Gate A probability interface over full square matchings

Pins for `PvNP.PHPFullMatchingProbability`: exact finite event/probability
bookkeeping over the full square matching space.  `EventProbEq` and
`EventProbLe` are cross-multiplied counting statements, not measure theory.
The star event is now packaged as probability `(h-s)/h`, and the PHP
depth-floor obstruction is packaged as a probability-one collapse-bad event.
This is interface progress toward Gate A rung 4 only: it still proves no
collapse-probability upper bound and no PHP switching lemma.
-/

/--
info: 'PvNP.PHPFullMatchingProbability.fullStarEvent_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingProbability.fullStarEvent_count

/--
info: 'PvNP.PHPFullMatchingProbability.fullStarEvent_probability_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingProbability.fullStarEvent_probability_eq

/--
info: 'PvNP.PHPFullMatchingProbability.fullStarEvent_probability_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingProbability.fullStarEvent_probability_le

/--
info: 'PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_holds

/--
info: 'PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_count

/--
info: 'PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_probability_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.PHPFullMatchingProbability.fullPHPCollapseBad_depthFloor_probability_one

/-! ## Gate B stages B1-B2: good restrictions generated by counting

Pins for `PvNP.GeneratedGoodRestriction`: the first theorems where the proved
switching lemma's COUNTING produces restrictions instead of consuming them.
Joint bad set of a gate list with the explicit union bound
(m * |restrictionsWithStars n (l-s)| * (8w)^s); good-restriction existence
when the bound beats the l-star space; SIMULTANEOUS collapse of every gate
formula to depth < s under ONE counting-generated restriction; interop with
the generated-stage machinery (shared restriction); non-vacuity via the
direct cardinality hypothesis.  Formula-collapse counting results only — NOT
a Frege/PHP proof-size bound, NOT NP/circuit, NOT P vs NP; Gate A rung 4
(the matching switching lemma) remains open.
-/

/--
info: 'PvNP.GeneratedGoodRestriction.GateSpec.theDNF_simple' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.GateSpec.theDNF_simple

/--
info: 'PvNP.GeneratedGoodRestriction.mem_jointBadSet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.mem_jointBadSet

/--
info: 'PvNP.GeneratedGoodRestriction.jointBadSet_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.jointBadSet_card_le

/--
info: 'PvNP.GeneratedGoodRestriction.goodRestriction_exists_of_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.goodRestriction_exists_of_card

/--
info: 'PvNP.GeneratedGoodRestriction.goodRestriction_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.goodRestriction_exists

/--
info: 'PvNP.GeneratedGoodRestriction.gate_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.gate_collapse

/--
info: 'PvNP.GeneratedGoodRestriction.simultaneousCollapse_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.simultaneousCollapse_exists

/--
info: 'PvNP.GeneratedGoodRestriction.generatedSimultaneousDNFStages_exist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.generatedSimultaneousDNFStages_exist

/--
info: 'PvNP.GeneratedGoodRestriction.generatedSimultaneousCNFStages_exist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.generatedSimultaneousCNFStages_exist

/--
info: 'PvNP.GeneratedGoodRestriction.generatedSimultaneousMixedStages_exist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.generatedSimultaneousMixedStages_exist

/--
info: 'PvNP.GeneratedGoodRestriction.restrictionsWithStars_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.restrictionsWithStars_nonempty

/--
info: 'PvNP.GeneratedGoodRestriction.goodRestriction_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.goodRestriction_nonvacuous

/--
info: 'PvNP.GeneratedGoodRestriction.generatedMixedEmptyStages_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedGoodRestriction.generatedMixedEmptyStages_nonvacuous

/-! ## Gate B obstruction map: generated shared-layer wrapper only

Pins for `PvNP.GeneratedIteratedCollapse`.  This module records the checked
shared-layer certificate currently available from the mixed generated-stage route
and names the missing B3/B4 obligations.  It does not state or prove
`generatedIteratedCollapse`; formula-collapse infrastructure only — NOT
Frege/PHP, NOT NP/circuit, NOT P vs NP; Gate A rung 4 remains open.
-/

/--
info: 'PvNP.GeneratedIteratedCollapse.GeneratedSharedLayerInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.GeneratedSharedLayerInput

/--
info: 'PvNP.GeneratedIteratedCollapse.GeneratedSharedLayerCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.GeneratedSharedLayerCertificate

/--
info: 'PvNP.GeneratedIteratedCollapse.generatedSharedLayerCertificate_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.generatedSharedLayerCertificate_exists

/-- info: 'PvNP.GeneratedIteratedCollapse.OpenObligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.OpenObligation

/-- info: 'PvNP.GeneratedIteratedCollapse.openObligations' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.openObligations

/-- info: 'PvNP.GeneratedIteratedCollapse.openObligations_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.openObligations_nonempty

/--
info: 'PvNP.GeneratedIteratedCollapse.emptyMixedSharedLayerInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.emptyMixedSharedLayerInput

/--
info: 'PvNP.GeneratedIteratedCollapse.generatedSharedLayerCertificate_empty_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapse.generatedSharedLayerCertificate_empty_nonvacuous

/-!
Pins for `PvNP.GeneratedOneStepDepthReduction`: the minimal B3 parent-merge
replacement step over an explicit one-parent bottom-layer view.
-/

/-- info: 'PvNP.GeneratedOneStepDepthReduction.ParentKind' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.ParentKind

/-- info: 'PvNP.GeneratedOneStepDepthReduction.MinimalLayeredFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.MinimalLayeredFormula

/--
info: 'PvNP.GeneratedOneStepDepthReduction.GeneratedOneStepInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.GeneratedOneStepInput

/--
info: 'PvNP.GeneratedOneStepDepthReduction.GeneratedOneStepCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.GeneratedOneStepCertificate

/--
info: 'PvNP.GeneratedOneStepDepthReduction.GeneratedOneStepCertificate.semantic_preservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.GeneratedOneStepCertificate.semantic_preservation

/--
info: 'PvNP.GeneratedOneStepDepthReduction.generatedOneStepDepthReduction_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.generatedOneStepDepthReduction_exists

/--
info: 'PvNP.GeneratedOneStepDepthReduction.singletonEmptyDNFOr_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedOneStepDepthReduction.singletonEmptyDNFOr_nonvacuous

/-!
Pins for `PvNP.RestrictionComposition`: B4 restriction-sequence composition,
consistent-subspace counting, and the closed-form star-space cardinality.
-/

/-- info: 'PvNP.RestrictionComposition.compose' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.compose

/-- info: 'PvNP.RestrictionComposition.ConsistentWith' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.ConsistentWith

/-- info: 'PvNP.RestrictionComposition.restrict_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.restrict_compose

/-- info: 'PvNP.RestrictionComposition.agree_compose_left' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.agree_compose_left

/-- info: 'PvNP.RestrictionComposition.agree_compose_right' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.agree_compose_right

/-- info: 'PvNP.RestrictionComposition.consistentSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.consistentSubspace

/--
info: 'PvNP.RestrictionComposition.consistentSubspace_freeRestriction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.consistentSubspace_freeRestriction

/-- info: 'PvNP.RestrictionComposition.consistentSubspace_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.consistentSubspace_nonempty

/--
info: 'PvNP.RestrictionComposition.goodRestriction_exists_of_subspace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.goodRestriction_exists_of_subspace

/--
info: 'PvNP.RestrictionComposition.simultaneousCollapse_exists_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.simultaneousCollapse_exists_consistent

/-- info: 'PvNP.RestrictionComposition.restrictionsWithStars_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RestrictionComposition.restrictionsWithStars_card

/-!
Pins for `PvNP.GeneratedIteratedCollapseFinal`: the B4 final generated
iterated-collapse theorem with per-stage depth/size accounting, consistent
generated restriction sequences, the last-stage combined decision tree, and
concrete non-vacuity.
-/

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.formulaSize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.formulaSize

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.formulaSize_treeToFormula_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.formulaSize_treeToFormula_le

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.reducedFormula_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.reducedFormula_size_le

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.certTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.certTree

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.dtEval_certTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.dtEval_certTree

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.dtDepth_certTree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.dtDepth_certTree_le

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedConsistentStepInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedConsistentStepInput

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.generatedConsistentOneStep_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.generatedConsistentOneStep_exists

/-- info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedCollapsePlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedCollapsePlan

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.finalFormula_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.finalFormula_eval

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.finalFormula_restrict_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.finalFormula_restrict_eval

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.finalComposed_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.finalComposed_extension

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageRestrictions_consistentSeq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageRestrictions_consistentSeq

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageRestrictions_stars' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageRestrictions_stars

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageOutputs_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageOutputs_depth

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageOutputs_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.stageOutputs_size

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.lastStage_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.GeneratedIteratedCertificate.lastStage_spec

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCertificate_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCertificate_exists

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse_singleton_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse_singleton_nonvacuous

/--
info: 'PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse_twoStage_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedIteratedCollapseFinal.generatedIteratedCollapse_twoStage_nonvacuous

/-!
Pins for `PvNP.RefinedSubspace`, `PvNP.SwitchingRelabel`,
`PvNP.GeneratedRefinedCollapse`, and `PvNP.RefinedTwoStageInstance`: the
renormalized (free-subcube) counting route closing the B4 satisfiability gap,
and its concrete nonempty-gate two-stage instance.
-/

/-- info: 'PvNP.RefinedSubspace.RefinesWith' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RefinedSubspace.RefinesWith

/-- info: 'PvNP.RefinedSubspace.refinesSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedSubspace.refinesSubspace

/-- info: 'PvNP.RefinedSubspace.refinesSubspace_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedSubspace.refinesSubspace_card

/-- info: 'PvNP.RefinedSubspace.refinesSubspace_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedSubspace.refinesSubspace_nonempty

/-- info: 'PvNP.RefinedSubspace.stars_downRestriction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedSubspace.stars_downRestriction

/-- info: 'PvNP.SwitchingRelabel.dnfRestrict_refinesWith' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.SwitchingRelabel.dnfRestrict_refinesWith

/-- info: 'PvNP.SwitchingRelabel.termCanonicalDT_mapDNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.SwitchingRelabel.termCanonicalDT_mapDNF

/-- info: 'PvNP.SwitchingRelabel.dtDepth_termCanonicalDT_mapDNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.SwitchingRelabel.dtDepth_termCanonicalDT_mapDNF

/-- info: 'PvNP.GeneratedRefinedCollapse.badSetTerm_refines_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.badSetTerm_refines_card_le

/-- info: 'PvNP.GeneratedRefinedCollapse.jointBadSet_refines_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.jointBadSet_refines_card_le

/--
info: 'PvNP.GeneratedRefinedCollapse.simultaneousCollapse_exists_refined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.simultaneousCollapse_exists_refined

/-- info: 'PvNP.GeneratedRefinedCollapse.GeneratedRefinedStepInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.GeneratedRefinedStepInput

/--
info: 'PvNP.GeneratedRefinedCollapse.generatedRefinedOneStep_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.generatedRefinedOneStep_exists

/-- info: 'PvNP.GeneratedRefinedCollapse.GeneratedRefinedCollapsePlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.GeneratedRefinedCollapsePlan

/--
info: 'PvNP.GeneratedRefinedCollapse.GeneratedRefinedIteratedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.GeneratedRefinedIteratedCertificate

/--
info: 'PvNP.GeneratedRefinedCollapse.generatedRefinedIteratedCertificate_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.generatedRefinedIteratedCertificate_exists

/--
info: 'PvNP.GeneratedRefinedCollapse.generatedRefinedIteratedCollapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.GeneratedRefinedCollapse.generatedRefinedIteratedCollapse

/-- info: 'PvNP.RefinedTwoStageInstance.depthOneDNFView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedTwoStageInstance.depthOneDNFView

/-- info: 'PvNP.RefinedTwoStageInstance.refinedTwoStagePlan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedTwoStageInstance.refinedTwoStagePlan

/--
info: 'PvNP.RefinedTwoStageInstance.refinedTwoStage_nonemptyGates_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RefinedTwoStageInstance.refinedTwoStage_nonemptyGates_nonvacuous

/-!
Pins for `PvNP.TreePathViews` and `PvNP.AutoReviewedIteration`: general
tree-to-DNF/CNF representation re-viewing and the automatic one-step next-layer
scaffold.  These pins do not claim frozen-form B4 closure or an implemented
three-stage/nonempty-gate theorem.
-/

/-- info: 'PvNP.TreePathViews.dnfEval_treePathDNF₀' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.dnfEval_treePathDNF₀

/-- info: 'PvNP.TreePathViews.treePathDNF₀_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.treePathDNF₀_simple

/-- info: 'PvNP.TreePathViews.widthDNF_treePathDNF₀_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.widthDNF_treePathDNF₀_le

/-- info: 'PvNP.TreePathViews.treeDNFView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.treeDNFView

/-- info: 'PvNP.TreePathViews.widthDNF_treeDNFView_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.widthDNF_treeDNFView_le

/-- info: 'PvNP.TreePathViews.cnfEval_treePathCNF₀' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.cnfEval_treePathCNF₀

/-- info: 'PvNP.TreePathViews.treePathCNF₀_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.treePathCNF₀_simple

/-- info: 'PvNP.TreePathViews.cnfDualDNF_treePathCNF₀' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.cnfDualDNF_treePathCNF₀

/-- info: 'PvNP.TreePathViews.widthDNF_cnfDualDNF_treePathCNF₀_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.widthDNF_cnfDualDNF_treePathCNF₀_le

/-- info: 'PvNP.TreePathViews.treeCNFView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.TreePathViews.treeCNFView

/-- info: 'PvNP.AutoReviewedIteration.nextLayer_originalFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.AutoReviewedIteration.nextLayer_originalFormula

/-- info: 'PvNP.AutoReviewedIteration.nextLayer_gateCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.AutoReviewedIteration.nextLayer_gateCount

/-- info: 'PvNP.AutoReviewedIteration.nextLayer_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.AutoReviewedIteration.nextLayer_width

/-!
Pins for `PvNP.ScheduledAutoCollapse` (schedule-driven automatic many-round
iterated collapse: numeric `ScheduleStage`/`BeatArith`/`ValidFrom`,
`stepInput` packaging, `castFormula` bookkeeping transport, and the headline
`autoIteratedCollapse`) and `PvNP.ScheduledCollapseDemo` (the concrete
`[(3, 561), (2, 17), (1, 1)]` schedule over `n = 10000` with a
counting-beat-backed budget-3 first stage).
-/

/-- info: 'PvNP.ScheduledAutoCollapse.stepInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.ScheduledAutoCollapse.stepInput

/-- info: 'PvNP.ScheduledAutoCollapse.castFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.ScheduledAutoCollapse.castFormula

/-- info: 'PvNP.ScheduledAutoCollapse.castFormula_stageGateCounts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.ScheduledAutoCollapse.castFormula_stageGateCounts

/-- info: 'PvNP.ScheduledAutoCollapse.castFormula_stageBudgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.ScheduledAutoCollapse.castFormula_stageBudgets

/-- info: 'PvNP.ScheduledAutoCollapse.castFormula_stageStarCounts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.ScheduledAutoCollapse.castFormula_stageStarCounts

/-- info: 'PvNP.ScheduledAutoCollapse.autoIteratedCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.ScheduledAutoCollapse.autoIteratedCollapse

/-!
Pins for `PvNP.FrozenProductSchedule`: the narrow frozen-product schedule
synthesis bridge from one product-bound family `B` and tree-budget family `t`
to the existing `ValidFrom` obligations, plus a tiny one-stage non-vacuity
witness.  These pins do not claim arbitrary layered decomposition, a global
frozen-form B4 theorem, a Frege/PHP lower bound, or any P-vs-NP consequence.
-/

/-- info: 'PvNP.FrozenProductSchedule.productBeat_to_beatArith' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.productBeat_to_beatArith

/-- info: 'PvNP.FrozenProductSchedule.productValidFrom_validFrom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.productValidFrom_validFrom

/-- info: 'PvNP.FrozenProductSchedule.frozenProductHypothesis_validFrom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.frozenProductHypothesis_validFrom

/--
info: 'PvNP.FrozenProductSchedule.autoIteratedCollapse_of_frozenProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.autoIteratedCollapse_of_frozenProduct

/-- info: 'PvNP.FrozenProductSchedule.oneStageProductHypothesis_nonvacuous' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.oneStageProductHypothesis_nonvacuous

/-- info: 'PvNP.FrozenProductSchedule.oneStageLayer_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.oneStageLayer_width

/--
info: 'PvNP.FrozenProductSchedule.frozenProductSchedule_oneStage_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductSchedule.frozenProductSchedule_oneStage_nonvacuous

/-!
Pins for `PvNP.FrozenProductScheduleDemo`: a small named `n = 17` width-1
two-stage instantiation of the frozen-product bridge with explicit
`B(1,1,1,2) = 2^20`, `B(1,0,1,1) = 0`, and `t = 0`.  The second stage is
the width-budget-0 tail after an `s = 1` first stage, so this remains a finite
demo instance only; it is not full B4 closure or an asymptotic theorem.
-/

/-- info: 'PvNP.FrozenProductScheduleDemo.seventeenLayer_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleDemo.seventeenLayer_width

/-- info: 'PvNP.FrozenProductScheduleDemo.seventeenProductHypothesis' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleDemo.seventeenProductHypothesis

/-- info: 'PvNP.FrozenProductScheduleDemo.seventeenProduct_validFrom' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleDemo.seventeenProduct_validFrom

/--
info: 'PvNP.FrozenProductScheduleDemo.frozenProductSchedule_seventeenTwoStage_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleDemo.frozenProductSchedule_seventeenTwoStage_nonvacuous

/--
info: 'PvNP.ScheduledCollapseDemo.scheduledThreeStage_budget3_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.ScheduledCollapseDemo.scheduledThreeStage_budget3_nonvacuous

/-!
Pins for `PvNP.FrozenProductScheduleRatio`: the ratio-form (space-aware)
replacement for the frozen-product bridge's supplied `B(m,w,s,d)` family.
Per-stage `BeatArith` obligations are PROVED from the regime condition
`32*m*w*l <= p` by fully symbolic binomial-ratio arithmetic; the named
geometric star schedule (all budgets `2`, star counts dividing by `64*m`)
satisfies the regime at every stage; `geometricFamilyCollapse` is the
artifact's first asymptotic-FAMILY scheduled statement (every round count
`k + 1`, every `n >= 2 * 64^(k+1)`, every stage entering with width budget
`>= 1` — no width-0 tail).  Start layers remain supplied simple families;
frozen-form B4 and Gate A rung 4 remain OPEN; realized widths of re-viewed
gates remain budget claims.
-/

/-- info: 'PvNP.FrozenProductScheduleRatio.choose_step_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.choose_step_lt

/-- info: 'PvNP.FrozenProductScheduleRatio.choose_ratio_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.choose_ratio_pow

/-- info: 'PvNP.FrozenProductScheduleRatio.ratio_beat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.ratio_beat

/-- info: 'PvNP.FrozenProductScheduleRatio.ratioRegime_beat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.ratioRegime_beat

/-- info: 'PvNP.FrozenProductScheduleRatio.regimeFrom_validFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.regimeFrom_validFrom

/--
info: 'PvNP.FrozenProductScheduleRatio.autoIteratedCollapse_of_ratioRegime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.autoIteratedCollapse_of_ratioRegime

/-- info: 'PvNP.FrozenProductScheduleRatio.geometricSchedule_regime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometricSchedule_regime

/-- info: 'PvNP.FrozenProductScheduleRatio.geometricSchedule_treeBudget' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometricSchedule_treeBudget

/-- info: 'PvNP.FrozenProductScheduleRatio.familyLayer_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.familyLayer_width

/-- info: 'PvNP.FrozenProductScheduleRatio.familyGate_width_realized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.familyGate_width_realized

/-- info: 'PvNP.FrozenProductScheduleRatio.geometricFamilyCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometricFamilyCollapse

/--
info: 'PvNP.FrozenProductScheduleRatio.geometricFamily_eightK_twoStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometricFamily_eightK_twoStage

/-!
Pins for the universal-layer extension of `PvNP.FrozenProductScheduleRatio`:
EVERY supplied start layer with `m >= 1` gates of width `<= w` (`w >= 1`)
admits the `(k+1)`-stage geometric-schedule certificate once
`n >= 2 * (64*m)^k * (64*m*w)` (entry stars `n / (64*m*w)`); only the gate
count and width bound enter the regime arithmetic.  The named two-gate
witness family (`pairLayer`, variables `0` and `1`, realized width `1`
each) inhabits the multi-gate case at the exact boundary `n = 32768`.
Start layers remain supplied; frozen-form B4 and Gate A rung 4 remain
OPEN.
-/

/-- info: 'PvNP.FrozenProductScheduleRatio.geometric_regime_of_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometric_regime_of_bound

/--
info: 'PvNP.FrozenProductScheduleRatio.geometricFamilyCollapse_universal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometricFamilyCollapse_universal

/-- info: 'PvNP.FrozenProductScheduleRatio.pairLayer_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.pairLayer_width

/-- info: 'PvNP.FrozenProductScheduleRatio.pairGate0_width_realized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.pairGate0_width_realized

/-- info: 'PvNP.FrozenProductScheduleRatio.pairGate1_width_realized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.pairGate1_width_realized

/--
info: 'PvNP.FrozenProductScheduleRatio.geometricFamily_pair_twoStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenProductScheduleRatio.geometricFamily_pair_twoStage

/-!
Pins for `PvNP.RefinedThreeStageInstance` (+ its arithmetic companion
`RefinedThreeStageArith`, same namespace): the resumed S2075 material — a
concrete finite three-stage auto-reviewed generated-collapse instance at
`n = 5193`, budgets `[2, 2, 1]`, star counts `[306, 17, 1]`, one gate per
stage, with the second and third layers automatically re-viewed by
`nextLayer`.  The counting beats were re-proved on resume through the
fully symbolic `beat_from_ratio` assembly (revision disclosed in the
module docstring); the stated inequalities are unchanged.  Single finite
instance with an `s = 1` final stage; NOT an asymptotic family, NOT
frozen-form B4, NOT Frege/PHP, NOT NP/circuit, NOT P vs NP.
-/

/-- info: 'PvNP.RefinedThreeStageInstance.choose_ratio_two_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedThreeStageInstance.choose_ratio_two_step

/-- info: 'PvNP.RefinedThreeStageInstance.stage1_beat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedThreeStageInstance.stage1_beat

/-- info: 'PvNP.RefinedThreeStageInstance.stage2_refined_beat_base306' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.RefinedThreeStageInstance.stage2_refined_beat_base306

/-- info: 'PvNP.RefinedThreeStageInstance.requestedParameters_recorded' does not depend on any axioms -/
#guard_msgs in
#print axioms PvNP.RefinedThreeStageInstance.requestedParameters_recorded

/--
info: 'PvNP.RefinedThreeStageInstance.refinedThreeStage_autoReviewed_nonemptyGates_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.RefinedThreeStageInstance.refinedThreeStage_autoReviewed_nonemptyGates_nonvacuous

/-!
Pins for `PvNP.FormulaFamilyCollapse`: synthesized start views for the
parent-merged embedded-DNF class (`p.merge (Ds.map dnfToBD)`; for `and`
parents the merged syntax tree has three alternation levels; bare DNFs
and CNF-shaped children are outside the class).  From a raw list of
simple DNFs, each gate's SEMANTIC view (`eval` equality) is CONSTRUCTED
(`dnfGate`/`synthGates`/`synthLayer` via the canonical `dnfToBD_dnfView`);
simplicity remains a decidable, purely syntactic hypothesis (distinct
variables per term).  The family statement quantifies over formulas of
the class with no supplied semantic view.  Witness instance at
`n = 16384` with a start DNF of one realized width-2 term.  Arbitrary
layered decomposition of general bounded-depth formulas is NOT performed;
frozen-form B4 in full and Gate A rung 4 remain OPEN.
-/

/-- info: 'PvNP.FormulaFamilyCollapse.synthGates_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaFamilyCollapse.synthGates_length

/-- info: 'PvNP.FormulaFamilyCollapse.synthGates_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaFamilyCollapse.synthGates_width

/-- info: 'PvNP.FormulaFamilyCollapse.synthLayer_originalFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaFamilyCollapse.synthLayer_originalFormula

/-- info: 'PvNP.FormulaFamilyCollapse.formulaFamilyCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaFamilyCollapse.formulaFamilyCollapse

/-- info: 'PvNP.FormulaFamilyCollapse.witnessDNF_width_realized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaFamilyCollapse.witnessDNF_width_realized

/-- info: 'PvNP.FormulaFamilyCollapse.formulaFamily_widthTwo_twoStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaFamilyCollapse.formulaFamily_widthTwo_twoStage

/-!
Pins for `PvNP.MixedFormulaFamilyCollapse`: the bottom-layer synthesis
surface completed for BOTH `GateSpec` constructors.  `cnfChildToBD` embeds
a raw CNF as a real `and`-of-`or`s formula with constructed semantics
(`cnfChildToBD_cnfView`, the CNF-side counterpart of `dnfToBD_dnfView`);
`widthDNF_cnfDualDNF` shows the dual-DNF switching width equals the raw
list's `widthDNF`, so both child kinds take the same uniform decidable
syntactic hypotheses.  `mixedFormulaFamilyCollapse` extends the
formula-level family to parent-merges of arbitrary mixtures of embedded
simple DNF and CNF children; `cnfFormulaFamilyCollapse` is the all-CNF
corollary; the witness at `n = 32768` exercises both constructors with a
genuinely two-clause CNF child.  Depth-`d` decomposition and the global
`t(d,s)` theorem (frozen-form B4 in full) and Gate A rung 4 remain OPEN.
-/

/-- info: 'PvNP.MixedFormulaFamilyCollapse.eval_cnfChildToBD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.eval_cnfChildToBD

/-- info: 'PvNP.MixedFormulaFamilyCollapse.widthDNF_cnfDualDNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.widthDNF_cnfDualDNF

/-- info: 'PvNP.MixedFormulaFamilyCollapse.RawGate.toGate_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.RawGate.toGate_width

/-- info: 'PvNP.MixedFormulaFamilyCollapse.mixedSynthLayer_originalFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.mixedSynthLayer_originalFormula

/-- info: 'PvNP.MixedFormulaFamilyCollapse.mixedFormulaFamilyCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.mixedFormulaFamilyCollapse

/-- info: 'PvNP.MixedFormulaFamilyCollapse.cnfFormulaFamilyCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.cnfFormulaFamilyCollapse

/-- info: 'PvNP.MixedFormulaFamilyCollapse.mixedFamily_dnfCnf_twoStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.MixedFormulaFamilyCollapse.mixedFamily_dnfCnf_twoStage

/-!
Pins for `PvNP.FrozenDepthView`: the explicit structural B4 interface.
`FrozenDepthView` packages a supplied layer for a real formula together
with a depth bound.  The consumer theorem proves that any such explicit view
whose gates satisfy the geometric-entry hypotheses yields the scheduled
generated refined certificate plus an actual final decision tree bounded by
the global budget `t(d,s) = gateCount * (s - 1)`.  The mixed-bottom
corollary shows the already-proved raw DNF/CNF bottom-layer class inhabits
the interface at its computed depth.  This is NOT automatic decomposition of
arbitrary bounded-depth formulas, NOT full frozen-form B4, NOT Gate A rung 4,
NOT Frege/PHP, NOT NP/circuit, and NOT P vs NP.
-/

/-- info: 'PvNP.FrozenDepthView.geometricSchedule_frozenGlobalTreeBudget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FrozenDepthView.geometricSchedule_frozenGlobalTreeBudget

/--
info: 'PvNP.FrozenDepthView.lastStage_gateCount_of_stageGateCounts_replicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenDepthView.lastStage_gateCount_of_stageGateCounts_replicate

/--
info: 'PvNP.FrozenDepthView.frozenDepthView_geometricCollapseWithGlobalTreeBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenDepthView.frozenDepthView_geometricCollapseWithGlobalTreeBudget

/--
info: 'PvNP.FrozenDepthView.mixedBottomFrozenDepthView_geometricCollapseWithGlobalTreeBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FrozenDepthView.mixedBottomFrozenDepthView_geometricCollapseWithGlobalTreeBudget

/-!
Pins for `PvNP.FormulaTruthTableView`: a broad semantic fallback that
synthesizes a simple DNF view for any formula by querying every variable in a
full decision tree and converting tree paths to a DNF.  Exact top-level
`and`/`or` raw formulas `p.merge children` then receive an automatically
constructed `FrozenDepthView` from those immediate child views, and inherit
the supplied-view global-budget consumer under an explicit caller-supplied
width bound.  The fallback width bound is only `<= n`, so this is NOT an
efficient arbitrary AC0 depth-`d` decomposition, NOT full frozen-form B4, NOT
Gate A rung 4, NOT Frege/PHP, NOT NP/circuit, and NOT P vs NP.
-/

/-- info: 'PvNP.FormulaTruthTableView.dtOfFun_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.dtOfFun_eval

/-- info: 'PvNP.FormulaTruthTableView.formulaDecisionTree_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.formulaDecisionTree_eval

/-- info: 'PvNP.FormulaTruthTableView.widthDNF_formulaDNFView_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.widthDNF_formulaDNFView_le

/-- info: 'PvNP.FormulaTruthTableView.map_formulaGate_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.map_formulaGate_formula

/-- info: 'PvNP.FormulaTruthTableView.topConnectiveLayer_originalFormula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.topConnectiveLayer_originalFormula

/-- info: 'PvNP.FormulaTruthTableView.topConnectiveFrozenDepthView_gateCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.topConnectiveFrozenDepthView_gateCount

/--
info: 'PvNP.FormulaTruthTableView.topConnectiveFormula_geometricCollapseWithGlobalTreeBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.topConnectiveFormula_geometricCollapseWithGlobalTreeBudget

/-!
Additional pins for `PvNP.FormulaTruthTableView`: the raw positive-depth
wrapper.  Every positive-depth `BDFormula` has a top `and`/`or` constructor, so
the module can synthesize a `FrozenDepthView` directly from raw formula syntax
by exposing that constructor and using the same truth-table child DNF views.
This removes a manual top-constructor decomposition step, but it remains the
truth-table fallback: child width is not efficiently bounded beyond `<= n`, and
leaves/constants still have no exact identity parent in `MinimalLayeredFormula`.
NOT full frozen-form B4, NOT Gate A rung 4, NOT Frege/PHP, NOT NP/circuit, and
NOT P vs NP.
-/

/-- info: 'PvNP.FormulaTruthTableView.positiveDepthFrozenDepthView_gateCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.positiveDepthFrozenDepthView_gateCount

/-- info: 'PvNP.FormulaTruthTableView.positiveDepthFrozenDepthView_width_le_vars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.positiveDepthFrozenDepthView_width_le_vars

/--
info: 'PvNP.FormulaTruthTableView.positiveDepthFormula_geometricCollapseWithGlobalTreeBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FormulaTruthTableView.positiveDepthFormula_geometricCollapseWithGlobalTreeBudget

/-!
Pins for `PvNP.FormulaStructuralSchedule`: the structural raw-formula schedule
surface now consumes arbitrary ratio-regime schedules, not only the fixed
geometric schedule, while preserving the global last-tree budget
`t(d,s)=gateCount*(s-1)`.  The positive-depth theorem synthesizes the start
view from raw non-leaf formula syntax, but it still uses truth-table/path-DNF
child views and supplied ratio-regime hypotheses.  NOT full frozen-form B4, NOT
efficient arbitrary AC0 decomposition, NOT Gate A rung 4, NOT Frege/PHP, NOT
NP/circuit, and NOT P vs NP.
-/

/-- info: 'PvNP.FormulaStructuralSchedule.constantGateTreeBudget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PvNP.FormulaStructuralSchedule.constantGateTreeBudget

/-- info: 'PvNP.FormulaStructuralSchedule.schedule_frozenGlobalTreeBudget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaStructuralSchedule.schedule_frozenGlobalTreeBudget

/--
info: 'PvNP.FormulaStructuralSchedule.frozenDepthView_ratioRegimeCollapseWithGlobalTreeBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FormulaStructuralSchedule.frozenDepthView_ratioRegimeCollapseWithGlobalTreeBudget

/-- info: 'PvNP.FormulaStructuralSchedule.positiveDepthFrozenDepthView_width_of_children' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PvNP.FormulaStructuralSchedule.positiveDepthFrozenDepthView_width_of_children

/--
info: 'PvNP.FormulaStructuralSchedule.positiveDepthFormula_ratioRegimeCollapseWithGlobalTreeBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PvNP.FormulaStructuralSchedule.positiveDepthFormula_ratioRegimeCollapseWithGlobalTreeBudget
