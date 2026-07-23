import PvNP.PHPMatchingEncodePackageOracleFreeze
import PvNP.PHPMatchingEncodeSideBitForceFreeze
import PvNP.PHPMatchingEncodePathGeometryForceBridge
import PvNP.FrozenProductScheduleRatio

/-!
# S2225 Gate A force exhaustion / Gate B weight decision pin

This module is a bounded route-decision pin after S2216, S2220, and S2224.
It records that the residual/preimage grind, side-bit product tax, and
path-geometry image force bridge are frozen or stop-lossed under the current
fixed package carrier: the best product-shaped package bound remains
**TRIVIAL** versus denominator `16`, while the exact `6/16` package result is
kept only as a regression witness.

The continuation anchor is Gate B schedule/weight infrastructure from
`FrozenProductScheduleRatio`.  This is not a global Gate A impossibility
theorem: a future Gate A route would require a qualitatively new invariant,
denominator, or counting target.

No GA-4, switching lemma, P-vs-NP, or `v0.11.0` conclusion is claimed.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeGateAForceExhaustion

open Classical
open BoundedDepthIteratedCollapse
open BoundedDepthRestriction
open GeneratedRefinedCollapse
open GeneratedRefinedIteratedCertificate
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeAnswerAlphabetLengthTwo
open PHPMatchingEncodePackageCount
open PHPMatchingEncodePackageDenomCompare
open PHPMatchingEncodeSideBitPackage
open PHPMatchingEncodePathGeometryImage
open PHPMatchingEncodePackageOracleFreeze
open PHPMatchingEncodeSideBitForceFreeze
open PHPMatchingEncodePathGeometryForceBridge
open FrozenProductScheduleRatio

/-- Local alias for the S2216 package-oracle freeze proposition. -/
def PackageOracleFreezeS2216Pinned : Prop :=
  (∀ ell : Nat,
    EncodeMatchG1G2LengthTwoPathExitEqResidual (p := 4) (h := 4) (w := 2)
      (t := 3) (ell := ell) rfl searchD4mp searchD4mp_width) ∧
    (vbadMatchings searchD4mp 2 3).card ≤ 3072 ∧
    (honestMatchingSpace 4 4 3).card < 3072 ∧
    (vbadMatchings searchD4mp 2 3).card = 6 ∧
    6 < (honestMatchingSpace 4 4 3).card

/-- Local alias for the S2220 side-bit force-freeze proposition. -/
def SideBitForceFreezeS2220Pinned : Prop :=
  (∀ ell j, (badGrade ell j).card ≤
    (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j) ∧
  (∀ ell j, (badGrade ell j).card ≤
    (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j) ∧
  (∀ ell j, (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j ≤
    (honestMatchingSpace 4 4 (ell - j)).card * (2 * 2) ^ j * 4 ^ j) ∧
  (vbadMatchings searchD4mp 2 3).card ≤ 3072 ∧
  (honestMatchingSpace 4 4 3).card < 3072 ∧
  (vbadMatchings searchD4mp 2 3).card = 6 ∧
  6 < (honestMatchingSpace 4 4 3).card

/-- Local alias for the S2224 path-geometry force-bridge stop-loss proposition. -/
def PathGeometryForceBridgeS2224Pinned : Prop :=
  (∀ {h w t ell j K : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w),
    PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K →
      (pathGeometryBadGrade t ell D hw j).card ≤
        K * (pathGeometryBadGradeImage t ell D hw j).card) ∧
  (∀ {h w t ell j K : Nat} (D : MDNF h h)
    (hw : ∀ term ∈ D, term.length ≤ w),
    PathGeometryImageFiberBound (t := t) (ell := ell) (j := j) D hw K →
      (pathGeometryBadGrade t ell D hw j).card ≤
        K * ((honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j)) ∧
  (packagePathGeometryBadGradeImage 3 2).card +
    (packagePathGeometryBadGradeImage 3 3).card ≤ 3072 ∧
  (honestMatchingSpace 4 4 3).card < 3072 ∧
  ¬ (3072 < (honestMatchingSpace 4 4 3).card) ∧
  (vbadMatchings searchD4mp 2 3).card = 6 ∧
  6 < (honestMatchingSpace 4 4 3).card ∧
  PHPMatchingEncodePathGeometryTarget.PathGeometryForceGate
    (Finset.univ : Finset (SearchD4mpBad 3)) packageEncode
    (honestMatchingSpace 4 4 3) 6 16

/-- Local bounded handoff proposition: after the current Gate A carrier has
only stop-loss/product-shape evidence, the route continues through Gate B
weight/schedule infrastructure rather than another force theorem on the same
carrier. -/
def GateBWeightDecisionAnchor : Prop :=
  ∃ cert : GeneratedRefinedIteratedCertificate 32768
      (freeRestriction 32768) (pairLayer 32766).originalFormula 2,
    cert.stageGateCounts = [2, 2] ∧
    cert.stageBudgets = [2, 2] ∧
    cert.stageStarCounts = [256, 2] ∧
    FrozenProductSchedule.TreeBudgetFrom (fun _ _ => 2) 2 2
      (geometricSchedule 2 256 2)

/-- The imported Gate B continuation witness, restated under the S2225 name. -/
theorem gateB_weight_decision_anchor : GateBWeightDecisionAnchor := by
  simpa [GateBWeightDecisionAnchor] using geometricFamily_pair_twoStage

/-- S2225 bounded route-decision summary: S2216/S2220/S2224 are all pinned, and
the next continuation anchor is Gate B weight/schedule infrastructure.  This is
not a global Gate A impossibility theorem. -/
theorem gateA_force_exhaustion_after_s2224_summary :
    PackageOracleFreezeS2216Pinned ∧
    SideBitForceFreezeS2220Pinned ∧
    PathGeometryForceBridgeS2224Pinned ∧
    GateBWeightDecisionAnchor := by
  exact ⟨package_oracle_freeze_s2216_summary,
    sidebit_force_freeze_s2220_summary,
    path_geometry_force_bridge_s2224_stop_loss_summary,
    gateB_weight_decision_anchor⟩

end PHPMatchingEncodeGateAForceExhaustion
end PvNP
