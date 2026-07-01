import PvNP.CertifiedAffine
import PvNP.BoundedDepthIteratedCollapse
import CertifiedAffine.FiniteChargeSurface
import CertifiedAffine.FiniteGraphWitnessSurface
import CertifiedAffine.FiniteFormulaWitnessSurface

/-!
# Graph-indexed bridge witness surface

This module packages the existing certified-affine graph/extractor metadata next
to the generated bounded-depth collapse schedule infrastructure.  It is only a
shared witness surface: it does not assert graph expansion, Tseitin
unsatisfiability, proof-complexity lower bounds, arbitrary graph extraction, or
any P-vs-NP consequence.
-/

namespace PvNP
namespace GraphIndexedBridge

open CertifiedAffine
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthIteratedCollapse
open BoundedDepthRestriction

/-- A graph-indexed bridge witness couples certified-affine extraction metadata
with an already generated k-layer schedule over the same variable index type.
The generated schedule is imported from the bounded-depth infrastructure rather
than re-proved here. -/
structure BridgeWitness (n d : Nat) where
  affine : CertifiedAffineExtraction n d
  schedule : GeneratedKLayerSchedule n

/-- The affine side of a bridge witness exposes the certified extractor theorem
on any selected vertex domain. -/
theorem bridgeWitness_completeOn {n d : Nat} (W : BridgeWitness n d)
    (domain : Fin n → Prop) :
    SemanticExtractorCompleteOn W.affine.graph domain
      (incidentExtractor W.affine.graph) :=
  certifiedAffineExtraction_completeOn W.affine domain

/-- Generated nonempty k-layer schedules attached to a graph-indexed bridge
witness produce exactly the corresponding generated schedule certificate.  This
is a wrapper around the existing generated schedule theorem, not a new collapse
claim for arbitrary formulas or graphs. -/
theorem bridgeWitness_generatedNonemptyKLayerCollapse_exists {n d : Nat}
    (W : BridgeWitness n d) (hnonempty : W.schedule.generatedStages ≠ []) :
    ∃ C : KLayerCollapseCertificate n,
      W.schedule.generatedStages ≠ [] ∧
        C.stages = W.schedule.generatedStages.map (fun G => G.toExplicit) ∧
        (∀ G, G ∈ W.schedule.generatedStages →
          ∃ H, H ∈ C.stages ∧ H = G.toExplicit ∧ H.depthBound = G.stageS) ∧
        stageDepthSum C.stages =
          GeneratedExplicitLayerStage.stageDepthSum W.schedule.generatedStages ∧
        (∃ a : CNFModel.Assignment n, ∀ H, H ∈ C.stages → Agree H.ρ a) :=
  generatedNonemptyKLayerCollapse_exists W.schedule hnonempty

/-- Empty graph metadata used only as a concrete bridge witness carrier. -/
def emptyTseitinGraph (n : Nat) : TseitinGraph n where
  edges := []
  charge := fun _ => false

/-- Project a finite edge list to Nat-valued endpoint pairs.  This is only a
bridge comparison helper; the actual graph still uses `Fin n` endpoints. -/
def edgeEndpointValues {n : Nat} (edges : List (Edge n)) : List (Nat × Nat) :=
  edges.map (fun e => (e.u.val, e.v.val))

/-- Project a local CNF literal to its edge-index value and sign. -/
def cnfLiteralProjection {n : Nat} (l : CNFModel.Literal n) : Nat × Bool :=
  (l.var.val, l.sign)

/-- Project a local CNF clause to Nat-valued edge-index/sign pairs. -/
def cnfClauseProjection {n : Nat} (c : CNFModel.Clause n) : List (Nat × Bool) :=
  c.map cnfLiteralProjection

/-- Project a local CNF view to a stable finite list of Nat-valued clauses. -/
def cnfViewClauseProjection {n : Nat} (F : CNFModel.CNF n) : List (List (Nat × Bool)) :=
  F.map cnfClauseProjection

/-- Evaluate a projected Nat-valued literal under a finite assignment. Out-of-range
indices evaluate to `false`; the concrete S2012 witness uses only valid indices
`0,...,5`. -/
def projectedLiteralEval {n : Nat} (a : CNFModel.Assignment n) (l : Nat × Bool) : Bool :=
  if h : l.1 < n then
    if l.2 then a ⟨l.1, h⟩ else !a ⟨l.1, h⟩
  else
    false

/-- Evaluate a projected Nat-valued clause under a finite assignment. -/
def projectedClauseEval {n : Nat} (a : CNFModel.Assignment n)
    (c : List (Nat × Bool)) : Bool :=
  c.any (projectedLiteralEval a)

/-- Evaluate a projected finite CNF under a finite assignment. -/
def projectedCNFEval {n : Nat} (a : CNFModel.Assignment n)
    (F : List (List (Nat × Bool))) : Bool :=
  F.all (projectedClauseEval a)

/-- Evaluate every clause of a local CNF view under a finite assignment. -/
def cnfViewClauseEvaluations {n : Nat} (a : CNFModel.Assignment n)
    (F : CNFModel.CNF n) : List Bool :=
  F.map (BoundedDepthIteratedCollapse.clauseEval a)

/-- Evaluate every projected clause under a finite assignment. -/
def projectedCNFClauseEvaluations {n : Nat} (a : CNFModel.Assignment n)
    (F : List (List (Nat × Bool))) : List Bool :=
  F.map (projectedClauseEval a)

/-- Projecting a local literal to Nat/Bool pairs preserves its evaluation. -/
theorem projectedLiteralEval_cnfLiteralProjection {n : Nat}
    (a : CNFModel.Assignment n) (l : CNFModel.Literal n) :
    projectedLiteralEval a (cnfLiteralProjection l) = CNFModel.litEval a l := by
  cases l with
  | mk var sign =>
      cases sign <;> simp [projectedLiteralEval, cnfLiteralProjection, CNFModel.litEval]

/-- Projecting a local clause to Nat/Bool pairs preserves its evaluation. -/
theorem projectedClauseEval_cnfClauseProjection {n : Nat}
    (a : CNFModel.Assignment n) (c : CNFModel.Clause n) :
    projectedClauseEval a (cnfClauseProjection c) =
      BoundedDepthIteratedCollapse.clauseEval a c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      simp only [projectedClauseEval, cnfClauseProjection,
        BoundedDepthIteratedCollapse.clauseEval, List.map_cons, List.any_cons,
        projectedLiteralEval_cnfLiteralProjection]
      change (CNFModel.litEval a l || projectedClauseEval a (cnfClauseProjection c)) =
        (CNFModel.litEval a l || BoundedDepthIteratedCollapse.clauseEval a c)
      exact congrArg (fun b => CNFModel.litEval a l || b) ih

/-- Projecting a local CNF view to Nat/Bool pairs preserves its evaluation. -/
theorem projectedCNFEval_cnfViewClauseProjection {n : Nat}
    (a : CNFModel.Assignment n) (F : CNFModel.CNF n) :
    projectedCNFEval a (cnfViewClauseProjection F) =
      BoundedDepthIteratedCollapse.cnfEval a F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
      simp only [projectedCNFEval, cnfViewClauseProjection,
        BoundedDepthIteratedCollapse.cnfEval, List.map_cons, List.all_cons]
      change (projectedClauseEval a (cnfClauseProjection c) &&
          projectedCNFEval a (cnfViewClauseProjection F)) =
        (BoundedDepthIteratedCollapse.clauseEval a c &&
          BoundedDepthIteratedCollapse.cnfEval a F)
      rw [projectedClauseEval_cnfClauseProjection]
      exact congrArg (fun b => BoundedDepthIteratedCollapse.clauseEval a c && b) ih

/-- Projecting a local CNF view preserves the per-clause evaluation list. -/
theorem projectedCNFClauseEvaluations_cnfViewClauseProjection {n : Nat}
    (a : CNFModel.Assignment n) (F : CNFModel.CNF n) :
    projectedCNFClauseEvaluations a (cnfViewClauseProjection F) =
      cnfViewClauseEvaluations a F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
      change (projectedClauseEval a (cnfClauseProjection c) ::
          projectedCNFClauseEvaluations a (cnfViewClauseProjection F)) =
        (BoundedDepthIteratedCollapse.clauseEval a c :: cnfViewClauseEvaluations a F)
      rw [projectedClauseEval_cnfClauseProjection, ih]

/-- Charge profile matching the certified-affine two-cycle-plus-path witness:
only vertex `0` is charged.  This is a bounded alignment profile for the shared
finite witness, not a statement about arbitrary Tseitin instances. -/
def twoCyclePath3Charge (v : Fin 5) : Bool :=
  v.val = 0

/-- The exported charge profile over vertices `0,1,2,3,4`. -/
def twoCyclePath3ChargeProfile : List Bool :=
  [true, false, false, false, false]

/-- The bridge charge function is the same zero-vertex indicator used by the
Lane A charge witness, transported from `Nat` to `Fin 5`. -/
theorem twoCyclePath3Charge_eq_zero (v : Fin 5) :
    twoCyclePath3Charge v = decide (v.val = 0) := by
  rfl

/-- The bridge charge function realizes the exported five-vertex profile. -/
theorem twoCyclePath3ChargeProfile_eq :
    [twoCyclePath3Charge ⟨0, by decide⟩,
      twoCyclePath3Charge ⟨1, by decide⟩,
      twoCyclePath3Charge ⟨2, by decide⟩,
      twoCyclePath3Charge ⟨3, by decide⟩,
      twoCyclePath3Charge ⟨4, by decide⟩] =
      twoCyclePath3ChargeProfile := by
  decide

/-- A finite pointwise transport witness between a Nat-indexed charge and a
`Fin 5` charge.  It records transport in both directions over the valid
five-vertex domain only; it is not a claim about arbitrary graph instances. -/
structure Fin5NatChargeBridge (natCharge : Nat → Bool) (finCharge : Fin 5 → Bool) : Prop where
  fin_to_nat : ∀ v : Fin 5, finCharge v = natCharge v.val
  nat_to_fin : ∀ (v : Nat), (hv : v < 5) → natCharge v = finCharge ⟨v, hv⟩

/-- Local Nat-indexed copy of the Lane A charge definition, included only to
make the finite `Nat`/`Fin 5` transport explicit in this repository. -/
def twoCyclePath3LaneANatCharge (v : Nat) : Bool :=
  v = 0

/-- The local Nat-indexed copy is exactly the zero-vertex indicator. -/
theorem twoCyclePath3LaneANatCharge_eq_zero (v : Nat) :
    twoCyclePath3LaneANatCharge v = decide (v = 0) := by
  rfl

/-- The Lane B `Fin 5` charge is the pointwise transport of the Nat-indexed
charge used by the Lane A witness, not merely an equal five-entry profile. -/
theorem twoCyclePath3Charge_eq_laneANatCharge (v : Fin 5) :
    twoCyclePath3Charge v = twoCyclePath3LaneANatCharge v.val := by
  rfl

/-- The Lane B charge and the Nat-indexed Lane A charge copy are pointwise equal
on the valid five-vertex domain. -/
theorem twoCyclePath3Charge_fin5NatBridge :
    Fin5NatChargeBridge twoCyclePath3LaneANatCharge twoCyclePath3Charge := by
  refine ⟨?_, ?_⟩
  · intro v
    rfl
  · intro v _hv
    rfl

/-- Compatibility shim retained from the pre-import finite-charge interface
spike. It records the exact Nat-indexed charge shape used by the imported Lane A
surface, while the direct imported facts below bind to Lane A's actual constant. -/
structure LaneAFiniteChargeInterfaceShim where
  natCharge : Nat → Bool
  natCharge_eq_zero : ∀ v : Nat, natCharge v = decide (v = 0)

/-- Shim instance matching the exported Lane A `twoCyclePath3_charge` shape:
charged only at vertex `0` on the valid five-vertex witness. -/
def twoCyclePath3LaneAChargeInterfaceShim : LaneAFiniteChargeInterfaceShim where
  natCharge := fun v => v = 0
  natCharge_eq_zero := by
    intro v
    rfl

/-- The Lane B `Fin 5` charge is pointwise the shimmed Lane A charge shape on
the valid five-vertex domain. -/
theorem twoCyclePath3Charge_eq_laneAChargeInterfaceShim (v : Fin 5) :
    twoCyclePath3Charge v = twoCyclePath3LaneAChargeInterfaceShim.natCharge v.val := by
  rfl

/-- The Lane B charge and the shimmed Lane A charge shape are pointwise equal on
the valid five-vertex domain. -/
theorem twoCyclePath3Charge_laneAChargeInterfaceShim_fin5NatBridge :
    Fin5NatChargeBridge twoCyclePath3LaneAChargeInterfaceShim.natCharge twoCyclePath3Charge := by
  refine ⟨?_, ?_⟩
  · intro v
    rfl
  · intro v _hv
    rfl

/-- The Lane B `Fin 5` charge is pointwise the imported Lane A
`twoCyclePath3_charge` constant on the valid five-vertex domain. -/
theorem twoCyclePath3Charge_eq_importedLaneACharge (v : Fin 5) :
    twoCyclePath3Charge v =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge v.val := by
  rfl

/-- The Lane B charge and the imported Lane A `twoCyclePath3_charge` constant are
pointwise equal on the valid five-vertex domain. -/
theorem twoCyclePath3Charge_imported_fin5NatBridge :
    _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.Fin5NatChargeBridge
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge
      twoCyclePath3Charge := by
  refine ⟨?_, ?_⟩
  · intro v
    rfl
  · intro v _hv
    rfl

/-- The empty graph has certified affine extraction metadata. -/
def emptyCertifiedAffineExtraction (n d : Nat) : CertifiedAffineExtraction n d where
  graph := emptyTseitinGraph n
  noLoops := by
    intro e h
    cases h
  simpleEdges := by
    simp [emptyTseitinGraph, SimpleEdgeList]
  lowDegree := by
    intro _x
    simp [LowDegree, incidentEdgeIndices, emptyTseitinGraph]

/-- A concrete five-vertex graph carrier matching the shared witness shape used
by the extraction lane: a two-cycle on vertices `0,1` plus the undirected path
`2-3-4`, represented as directed edge records in both orientations.  This is
only graph/extractor metadata; it carries no expansion, satisfiability, or
lower-bound claim. -/
def twoCyclePath3TseitinGraph : TseitinGraph 5 where
  edges :=
    [ { u := ⟨0, by decide⟩, v := ⟨1, by decide⟩ }
    , { u := ⟨1, by decide⟩, v := ⟨0, by decide⟩ }
    , { u := ⟨2, by decide⟩, v := ⟨3, by decide⟩ }
    , { u := ⟨3, by decide⟩, v := ⟨2, by decide⟩ }
    , { u := ⟨3, by decide⟩, v := ⟨4, by decide⟩ }
    , { u := ⟨4, by decide⟩, v := ⟨3, by decide⟩ } ]
  charge := twoCyclePath3Charge

/-- The concrete Lane B graph carrier has exactly the imported Lane A finite
endpoint list.  This is a six-record finite equality, not a statement about
arbitrary graph extraction. -/
theorem twoCyclePath3TseitinGraph_edges_eq_importedLaneAEndpoints :
    edgeEndpointValues twoCyclePath3TseitinGraph.edges =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_edgeEndpoints := by
  rfl

/-- The actual two-cycle-plus-path graph carrier has the charge profile aligned
with the certified-affine extraction witness. -/
theorem twoCyclePath3TseitinGraph_chargeProfile :
    [twoCyclePath3TseitinGraph.charge ⟨0, by decide⟩,
      twoCyclePath3TseitinGraph.charge ⟨1, by decide⟩,
      twoCyclePath3TseitinGraph.charge ⟨2, by decide⟩,
      twoCyclePath3TseitinGraph.charge ⟨3, by decide⟩,
      twoCyclePath3TseitinGraph.charge ⟨4, by decide⟩] =
      twoCyclePath3ChargeProfile := by
  decide

/-- Certified affine extraction metadata for the concrete two-cycle-plus-path
carrier.  The explicit safe degree bound is `6`, the length of the concrete
edge list. -/
def twoCyclePath3CertifiedAffineExtraction : CertifiedAffineExtraction 5 6 where
  graph := twoCyclePath3TseitinGraph
  noLoops := by
    intro e h
    simp [twoCyclePath3TseitinGraph] at h
    rcases h with h | h | h | h | h | h <;> subst e <;> decide
  simpleEdges := by
    simp [SimpleEdgeList, twoCyclePath3TseitinGraph]
  lowDegree := by
    intro x
    have h := List.length_filter_le
      (fun p : Nat × Edge 5 => decide (p.snd.u = x) || decide (p.snd.v = x))
      twoCyclePath3TseitinGraph.edges.enum
    simpa [LowDegree, incidentEdgeIndices, twoCyclePath3TseitinGraph] using h

/-- Concrete graph-indexed bridge witness carrying the existing nonempty
generated three-layer empty DNF/CNF/DNF schedule. -/
def emptyGeneratedBridgeWitness3 (n d : Nat) : BridgeWitness n d where
  affine := emptyCertifiedAffineExtraction n d
  schedule := emptyGeneratedKLayerSchedule3 n

/-- Concrete nonempty graph-indexed bridge witness using the shared
two-cycle-plus-path graph carrier and the existing generated three-layer
schedule infrastructure. -/
def twoCyclePath3GeneratedBridgeWitness : BridgeWitness 5 6 where
  affine := twoCyclePath3CertifiedAffineExtraction
  schedule := emptyGeneratedKLayerSchedule3 5

/-- Concrete CNF view for the generated bridge witness. The clause order follows
the five graph vertices `0,1,2,3,4`, and the formula variables are the six
edge-record indices of `twoCyclePath3TseitinGraph.edges`. -/
def twoCyclePath3GeneratedBridgeWitness_cnfView : CNFModel.CNF 6 :=
  [ [ { var := ⟨0, by decide⟩, sign := true }
      , { var := ⟨1, by decide⟩, sign := true } ]
  , [ { var := ⟨0, by decide⟩, sign := false }
      , { var := ⟨1, by decide⟩, sign := false } ]
  , [ { var := ⟨0, by decide⟩, sign := true }
      , { var := ⟨1, by decide⟩, sign := false } ]
  , [ { var := ⟨0, by decide⟩, sign := false }
      , { var := ⟨1, by decide⟩, sign := true } ]
  , [ { var := ⟨2, by decide⟩, sign := true }
      , { var := ⟨3, by decide⟩, sign := false } ]
  , [ { var := ⟨2, by decide⟩, sign := false }
      , { var := ⟨3, by decide⟩, sign := true } ]
  , [ { var := ⟨2, by decide⟩, sign := true }
      , { var := ⟨3, by decide⟩, sign := true }
      , { var := ⟨4, by decide⟩, sign := true }
      , { var := ⟨5, by decide⟩, sign := false } ]
  , [ { var := ⟨2, by decide⟩, sign := true }
      , { var := ⟨3, by decide⟩, sign := true }
      , { var := ⟨4, by decide⟩, sign := false }
      , { var := ⟨5, by decide⟩, sign := true } ]
  , [ { var := ⟨2, by decide⟩, sign := true }
      , { var := ⟨3, by decide⟩, sign := false }
      , { var := ⟨4, by decide⟩, sign := true }
      , { var := ⟨5, by decide⟩, sign := true } ]
  , [ { var := ⟨2, by decide⟩, sign := true }
      , { var := ⟨3, by decide⟩, sign := false }
      , { var := ⟨4, by decide⟩, sign := false }
      , { var := ⟨5, by decide⟩, sign := false } ]
  , [ { var := ⟨2, by decide⟩, sign := false }
      , { var := ⟨3, by decide⟩, sign := true }
      , { var := ⟨4, by decide⟩, sign := true }
      , { var := ⟨5, by decide⟩, sign := true } ]
  , [ { var := ⟨2, by decide⟩, sign := false }
      , { var := ⟨3, by decide⟩, sign := true }
      , { var := ⟨4, by decide⟩, sign := false }
      , { var := ⟨5, by decide⟩, sign := false } ]
  , [ { var := ⟨2, by decide⟩, sign := false }
      , { var := ⟨3, by decide⟩, sign := false }
      , { var := ⟨4, by decide⟩, sign := true }
      , { var := ⟨5, by decide⟩, sign := false } ]
  , [ { var := ⟨2, by decide⟩, sign := false }
      , { var := ⟨3, by decide⟩, sign := false }
      , { var := ⟨4, by decide⟩, sign := false }
      , { var := ⟨5, by decide⟩, sign := true } ]
  , [ { var := ⟨4, by decide⟩, sign := true }
      , { var := ⟨5, by decide⟩, sign := false } ]
  , [ { var := ⟨4, by decide⟩, sign := false }
      , { var := ⟨5, by decide⟩, sign := true } ] ]

/-- Stable finite projection of the generated bridge witness CNF view. -/
def twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection : List (List (Nat × Bool)) :=
  cnfViewClauseProjection twoCyclePath3GeneratedBridgeWitness_cnfView

/-- The generated bridge witness CNF view has exactly the imported Lane A finite
clause projection. This is a concrete sixteen-clause equality over six
edge-record variables, not a formula theorem for arbitrary graphs. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection_eq_importedLaneA :
    twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection := by
  rw [_root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection_eq_explicit]
  rfl

/-- The concrete generated bridge witness CNF view and the imported Lane A finite
projection have the same Boolean evaluation under every assignment to the six
edge-record variables. This is a finite semantic bridge for the concrete witness,
not an arbitrary formula-extraction or SAT-solving theorem. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfSemanticEval_eq_importedLaneA
    (a : CNFModel.Assignment 6) :
    BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView =
      projectedCNFEval a
        _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection := by
  rw [← projectedCNFEval_cnfViewClauseProjection a twoCyclePath3GeneratedBridgeWitness_cnfView]
  change projectedCNFEval a twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection =
    projectedCNFEval a
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection
  rw [twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection_eq_importedLaneA]

/-- The concrete generated bridge witness CNF view and the imported Lane A finite
projection have the same per-clause Boolean evaluations under every assignment to
the six edge-record variables. -/
theorem twoCyclePath3GeneratedBridgeWitness_clauseSemanticEval_eq_importedLaneA
    (a : CNFModel.Assignment 6) :
    cnfViewClauseEvaluations a twoCyclePath3GeneratedBridgeWitness_cnfView =
      projectedCNFClauseEvaluations a
        _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection := by
  rw [← projectedCNFClauseEvaluations_cnfViewClauseProjection a
    twoCyclePath3GeneratedBridgeWitness_cnfView]
  change projectedCNFClauseEvaluations a twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection =
    projectedCNFClauseEvaluations a
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection
  rw [twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection_eq_importedLaneA]

/-- The generated bridge witness exposes the same finite edge endpoint list as
the imported Lane A graph witness surface. -/
theorem twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints :
    edgeEndpointValues twoCyclePath3GeneratedBridgeWitness.affine.graph.edges =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_edgeEndpoints := by
  rfl

/-- Concrete nonempty graph-indexed bridge certificate.  The graph side is the
empty certified-affine carrier; the schedule side is the existing generated
three-layer schedule witness. -/
theorem emptyGeneratedBridgeWitness3_nonempty (n d : Nat) :
    ∃ C : KLayerCollapseCertificate n,
      (emptyGeneratedBridgeWitness3 n d).schedule.generatedStages ≠ [] ∧
        C.stages =
          (emptyGeneratedBridgeWitness3 n d).schedule.generatedStages.map
            (fun G => G.toExplicit) ∧
        ∃ a : CNFModel.Assignment n, ∀ H, H ∈ C.stages → Agree H.ρ a := by
  have hnonempty : (emptyGeneratedBridgeWitness3 n d).schedule.generatedStages ≠ [] := by
    simp [emptyGeneratedBridgeWitness3, emptyGeneratedKLayerSchedule3]
  rcases bridgeWitness_generatedNonemptyKLayerCollapse_exists
      (emptyGeneratedBridgeWitness3 n d) hnonempty with
    ⟨C, hne, hstages, _hdepthEach, _hsum, hcompat⟩
  exact ⟨C, hne, hstages, hcompat⟩

/-- The concrete two-cycle-plus-path graph carrier can be paired with the
existing nonempty generated three-layer schedule certificate.  This remains a
shared witness statement only, not a graph hardness or lower-bound theorem. -/
theorem twoCyclePath3GeneratedBridgeWitness_nonempty :
    ∃ C : KLayerCollapseCertificate 5,
      twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages ≠ [] ∧
        C.stages =
          twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages.map
            (fun G => G.toExplicit) ∧
        ∃ a : CNFModel.Assignment 5, ∀ H, H ∈ C.stages → Agree H.ρ a := by
  have hnonempty : twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages ≠ [] := by
    simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3]
  rcases bridgeWitness_generatedNonemptyKLayerCollapse_exists
      twoCyclePath3GeneratedBridgeWitness hnonempty with
    ⟨C, hne, hstages, _hdepthEach, _hsum, hcompat⟩
  exact ⟨C, hne, hstages, hcompat⟩

/-- The concrete generated-witness alignment carries the same finite charge profile
as the certified-affine graph-quotient witness: charged at vertex `0` and
uncharged at vertices `1,2,3,4`. -/
theorem twoCyclePath3GeneratedBridgeWitness_chargeProfile :
    [twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ⟨0, by decide⟩,
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ⟨1, by decide⟩,
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ⟨2, by decide⟩,
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ⟨3, by decide⟩,
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ⟨4, by decide⟩] =
      twoCyclePath3ChargeProfile := by
  decide

/-- The generated-witness alignment charge is pointwise the Nat-indexed charge
copy transported through the `Fin 5` vertex carrier. -/
theorem twoCyclePath3GeneratedBridgeWitness_charge_eq_laneANatCharge (v : Fin 5) :
    twoCyclePath3GeneratedBridgeWitness.affine.graph.charge v =
      twoCyclePath3LaneANatCharge v.val := by
  rfl

/-- The generated-witness alignment charge and the Nat-indexed Lane A charge copy
are pointwise equal on the valid five-vertex domain. -/
theorem twoCyclePath3GeneratedBridgeWitness_charge_fin5NatBridge :
    Fin5NatChargeBridge twoCyclePath3LaneANatCharge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge := by
  refine ⟨?_, ?_⟩
  · intro v
    rfl
  · intro v _hv
    rfl

/-- The generated-witness charge is pointwise the shimmed Lane A charge shape on
the valid five-vertex domain. -/
theorem twoCyclePath3GeneratedBridgeWitness_charge_eq_laneAChargeInterfaceShim (v : Fin 5) :
    twoCyclePath3GeneratedBridgeWitness.affine.graph.charge v =
      twoCyclePath3LaneAChargeInterfaceShim.natCharge v.val := by
  rfl

/-- The generated-witness charge and the shimmed Lane A charge shape are
pointwise equal on the valid five-vertex domain. -/
theorem twoCyclePath3GeneratedBridgeWitness_charge_laneAChargeInterfaceShim_fin5NatBridge :
    Fin5NatChargeBridge twoCyclePath3LaneAChargeInterfaceShim.natCharge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge := by
  refine ⟨?_, ?_⟩
  · intro v
    rfl
  · intro v _hv
    rfl

/-- The generated-witness charge is pointwise the imported Lane A
`twoCyclePath3_charge` constant on the valid five-vertex domain. -/
theorem twoCyclePath3GeneratedBridgeWitness_charge_eq_importedLaneACharge (v : Fin 5) :
    twoCyclePath3GeneratedBridgeWitness.affine.graph.charge v =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge v.val := by
  rfl

/-- The generated-witness charge and the imported Lane A `twoCyclePath3_charge`
constant are pointwise equal on the valid five-vertex domain. -/
theorem twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge :
    _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.Fin5NatChargeBridge
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge := by
  refine ⟨?_, ?_⟩
  · intro v
    rfl
  · intro v _hv
    rfl

/-- The generated bridge witness aligns with the imported Lane A finite graph
and charge witness: the edge endpoint list matches and the charge transports
pointwise over the valid five-vertex carrier. -/
theorem twoCyclePath3GeneratedBridgeWitness_importedGraphChargeAlignment :
    edgeEndpointValues twoCyclePath3GeneratedBridgeWitness.affine.graph.edges =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_edgeEndpoints ∧
    _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.Fin5NatChargeBridge
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge := by
  exact ⟨twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints,
    twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge⟩

/-- The generated bridge witness aligns with the imported Lane A finite graph,
charge, and CNF projection: edge endpoints match, charge transports pointwise,
and the concrete sixteen-clause formula projection is the same. -/
theorem twoCyclePath3GeneratedBridgeWitness_importedGraphChargeFormulaAlignment :
    edgeEndpointValues twoCyclePath3GeneratedBridgeWitness.affine.graph.edges =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_edgeEndpoints ∧
    _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.Fin5NatChargeBridge
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ∧
    twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection := by
  exact ⟨twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints,
    twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge,
    twoCyclePath3GeneratedBridgeWitness_cnfClauseProjection_eq_importedLaneA⟩

/-- The generated bridge witness aligns with the imported Lane A finite graph,
charge, and concrete CNF projection semantics: edge endpoints match, charge
transports pointwise, and every six-variable assignment gives the same CNF
evaluation on the generated witness view and on the imported finite projection. -/
theorem twoCyclePath3GeneratedBridgeWitness_importedGraphChargeFormulaSemanticAlignment :
    edgeEndpointValues twoCyclePath3GeneratedBridgeWitness.affine.graph.edges =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_edgeEndpoints ∧
    _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.Fin5NatChargeBridge
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ∧
    (∀ a : CNFModel.Assignment 6,
      cnfViewClauseEvaluations a twoCyclePath3GeneratedBridgeWitness_cnfView =
        projectedCNFClauseEvaluations a
          _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection) ∧
    (∀ a : CNFModel.Assignment 6,
      BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView =
        projectedCNFEval a
          _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection) := by
  exact ⟨twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints,
    twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge,
    twoCyclePath3GeneratedBridgeWitness_clauseSemanticEval_eq_importedLaneA,
    twoCyclePath3GeneratedBridgeWitness_cnfSemanticEval_eq_importedLaneA⟩

/-- First bounded consumer of the S2012 finite CNF semantic bridge.  The concrete
`twoCyclePath3GeneratedBridgeWitness` packages the imported Lane A endpoint list,
the imported finite `Fin 5` charge transport, six-variable per-clause and whole-CNF
semantic alignment, and the existing generated nonempty k-layer collapse
certificate.  This remains a finite witness-consumer theorem, not an arbitrary
formula extraction, Tseitin semantics, SAT-solving, lower-bound, or P-vs-NP claim. -/
theorem twoCyclePath3GeneratedBridgeWitness_finiteCNFSemanticBridgeConsumer :
    edgeEndpointValues twoCyclePath3GeneratedBridgeWitness.affine.graph.edges =
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_edgeEndpoints ∧
    _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.Fin5NatChargeBridge
      _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_charge
      twoCyclePath3GeneratedBridgeWitness.affine.graph.charge ∧
    (∀ a : CNFModel.Assignment 6,
      cnfViewClauseEvaluations a twoCyclePath3GeneratedBridgeWitness_cnfView =
        projectedCNFClauseEvaluations a
          _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection) ∧
    (∀ a : CNFModel.Assignment 6,
      BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView =
        projectedCNFEval a
          _root_.CertifiedAffine.TseitinCNFData.AtomicClassBridge.twoCyclePath3_cnfClauseProjection) ∧
    (∃ C : KLayerCollapseCertificate 5,
      twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages ≠ [] ∧
        C.stages =
          twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages.map
            (fun G => G.toExplicit) ∧
        (∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
          ∃ H, H ∈ C.stages ∧ H = G.toExplicit ∧ H.depthBound = G.stageS) ∧
        stageDepthSum C.stages =
          GeneratedExplicitLayerStage.stageDepthSum
            twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages ∧
        (∃ a : CNFModel.Assignment 5, ∀ H, H ∈ C.stages → Agree H.ρ a)) := by
  have hnonempty : twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages ≠ [] := by
    simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3]
  rcases bridgeWitness_generatedNonemptyKLayerCollapse_exists
      twoCyclePath3GeneratedBridgeWitness hnonempty with
    ⟨C, hne, hstages, hstageEach, hsum, hcompat⟩
  exact ⟨twoCyclePath3GeneratedBridgeWitness_edges_eq_importedLaneAEndpoints,
    twoCyclePath3GeneratedBridgeWitness_charge_imported_fin5NatBridge,
    twoCyclePath3GeneratedBridgeWitness_clauseSemanticEval_eq_importedLaneA,
    twoCyclePath3GeneratedBridgeWitness_cnfSemanticEval_eq_importedLaneA,
    ⟨C, hne, hstages, hstageEach, hsum, hcompat⟩⟩

/-- The concrete six-variable CNF view paired with
`twoCyclePath3GeneratedBridgeWitness` evaluates to `false` under every finite
assignment.  This is a closed finite fact about the displayed sixteen-clause
view; it is not a theorem about arbitrary imported CNFs. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false
    (a : CNFModel.Assignment 6) :
    BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView =
      false := by
  cases h0 : a (0 : Fin 6) <;> cases h1 : a (1 : Fin 6) <;>
    simp [twoCyclePath3GeneratedBridgeWitness_cnfView,
      BoundedDepthIteratedCollapse.cnfEval, BoundedDepthIteratedCollapse.clauseEval,
      CNFModel.litEval, h0, h1]

/-! S2016: local CNF-to-bounded-depth formula view for the concrete bridge CNF. -/

/-- Local representation helper: view a CNF literal as a bounded-depth literal. -/
def cnfLiteralToBD {n : Nat} (l : CNFModel.Literal n) : BDFormula n :=
  BDFormula.lit l

/-- Local representation helper: view a CNF clause as a bounded-depth disjunction. -/
def cnfClauseToBD {n : Nat} (c : CNFModel.Clause n) : BDFormula n :=
  BDFormula.or (c.map cnfLiteralToBD)

/-- Local representation helper: view a CNF as a bounded-depth conjunction. -/
def cnfToBD {n : Nat} (C : CNFModel.CNF n) : BDFormula n :=
  BDFormula.and (C.map cnfClauseToBD)

/-- The local literal representation has the same finite Boolean semantics as the
CNF literal evaluator. -/
theorem eval_cnfLiteralToBD {n : Nat} (a : CNFModel.Assignment n)
    (l : CNFModel.Literal n) :
    BoundedDepthFrege.eval a (cnfLiteralToBD l) = CNFModel.litEval a l := by
  simp [cnfLiteralToBD, BoundedDepthFrege.eval_lit]

/-- The local clause representation has the same finite Boolean semantics as the
CNF clause evaluator. -/
theorem eval_cnfClauseToBD {n : Nat} (a : CNFModel.Assignment n)
    (c : CNFModel.Clause n) :
    BoundedDepthFrege.eval a (cnfClauseToBD c) =
      BoundedDepthIteratedCollapse.clauseEval a c := by
  induction c with
  | nil =>
      simp [cnfClauseToBD, BoundedDepthFrege.eval_or,
        BoundedDepthIteratedCollapse.clauseEval]
  | cons l c ih =>
      have htail : (c.map cnfLiteralToBD).any (fun f => BoundedDepthFrege.eval a f) =
          c.any (fun l => CNFModel.litEval a l) := by
        simpa [cnfClauseToBD, BoundedDepthFrege.eval_or,
          BoundedDepthIteratedCollapse.clauseEval] using ih
      simp [cnfClauseToBD, BoundedDepthFrege.eval_or,
        BoundedDepthIteratedCollapse.clauseEval, eval_cnfLiteralToBD, htail]

/-- The local CNF representation has the same finite Boolean semantics as the CNF
evaluator. -/
theorem eval_cnfToBD {n : Nat} (a : CNFModel.Assignment n)
    (C : CNFModel.CNF n) :
    BoundedDepthFrege.eval a (cnfToBD C) =
      BoundedDepthIteratedCollapse.cnfEval a C := by
  induction C with
  | nil =>
      simp [cnfToBD, BoundedDepthFrege.eval_and,
        BoundedDepthIteratedCollapse.cnfEval]
  | cons c C ih =>
      have htail : (C.map cnfClauseToBD).all (fun f => BoundedDepthFrege.eval a f) =
          C.all (fun c => BoundedDepthIteratedCollapse.clauseEval a c) := by
        simpa [cnfToBD, BoundedDepthFrege.eval_and,
          BoundedDepthIteratedCollapse.cnfEval] using ih
      simp [cnfToBD, BoundedDepthFrege.eval_and,
        BoundedDepthIteratedCollapse.cnfEval, eval_cnfClauseToBD, htail]

/-- Bounded-depth formula representation of the concrete six-variable CNF view. -/
def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula : BDFormula 6 :=
  cnfToBD twoCyclePath3GeneratedBridgeWitness_cnfView

/-- The concrete bounded-depth CNF representation computes exactly the displayed
six-variable CNF view. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics
    (a : CNFModel.Assignment 6) :
    BoundedDepthFrege.eval a twoCyclePath3GeneratedBridgeWitness_cnfBDFormula =
      BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView := by
  simp [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula, eval_cnfToBD]

/-- Concrete CNF-view package for the bounded-depth representation of the
`twoCyclePath3GeneratedBridgeWitness` CNF only. -/
def twoCyclePath3GeneratedBridgeWitness_cnfViewStage :
    CNFView twoCyclePath3GeneratedBridgeWitness_cnfBDFormula where
  C := twoCyclePath3GeneratedBridgeWitness_cnfView
  sem_eq := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics
  simple := by
    simp [BoundedDepthIteratedCollapse.SimpleCNF,
      BoundedDepthIteratedCollapse.SimpleClause,
      twoCyclePath3GeneratedBridgeWitness_cnfView]

/-- Concrete six-variable explicit CNF stage for the displayed bridge CNF.  The
leaf-false tree is correct because this finite CNF view is constantly false. -/
def twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage : ExplicitLayerStage 6 where
  kind := LayerKind.cnf
  F := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula
  ρ := freeRestriction 6
  T := DTree.leaf false
  depthBound := 1
  depth_lt := by simp
  computes := by
    intro a hagree
    calc
      dtEval a (DTree.leaf false : DTree 6) = false := by simp
      _ = BoundedDepthFrege.eval a
          (BoundedDepthRestriction.restrict (freeRestriction 6)
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) := by
          rw [BoundedDepthRestriction.eval_restrict (freeRestriction 6) a
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula hagree,
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics,
            twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false]

/-- The concrete six-variable explicit CNF stage has the same restricted-formula
semantics as the displayed bridge CNF evaluator. -/
theorem twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage_compatible :
    ∀ a : CNFModel.Assignment 6,
      BoundedDepthFrege.eval a
          (BoundedDepthRestriction.restrict
            twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.ρ
            twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.F) =
        BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView := by
  intro a
  rw [BoundedDepthRestriction.eval_restrict]
  · exact twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics a
  · exact agree_freeRestriction a

/-- S2016 concrete invariant package: the displayed six-variable bridge CNF has a
bounded-depth formula view, a CNF-view record, an explicit leaf-false CNF stage,
and restricted-stage semantics compatible with the same concrete CNF evaluator. -/
theorem twoCyclePath3GeneratedBridgeWitness_sixCNFConcreteInvariant :
    (∀ a : CNFModel.Assignment 6,
      BoundedDepthFrege.eval a twoCyclePath3GeneratedBridgeWitness_cnfBDFormula =
        BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView) ∧
    (twoCyclePath3GeneratedBridgeWitness_cnfViewStage.C =
      twoCyclePath3GeneratedBridgeWitness_cnfView) ∧
    (twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.kind = LayerKind.cnf) ∧
    (∀ a : CNFModel.Assignment 6,
      dtEval a twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.T =
        BoundedDepthFrege.eval a
          (BoundedDepthRestriction.restrict
            twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.ρ
            twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.F)) ∧
    (∀ a : CNFModel.Assignment 6,
      BoundedDepthFrege.eval a
          (BoundedDepthRestriction.restrict
            twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.ρ
            twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.F) =
        BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView) := by
  refine ⟨twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics, rfl, rfl, ?_,
    twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage_compatible⟩
  intro a
  exact twoCyclePath3GeneratedBridgeWitness_sixCNFExplicitStage.computes a
    (agree_freeRestriction a)

/-! S2017: concrete generated CNF-stage compatibility for the six-variable view. -/

open BoundedDepthCanonicalDT
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct

/-- The dual DNF of the concrete six-variable CNF view has clause/term width at
most four.  This is a finite syntax fact about the displayed witness only. -/
theorem twoCyclePath3GeneratedBridgeWitness_dualDNF_width_le_four :
    widthDNF (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_cnfView) ≤ 4 := by
  simp [twoCyclePath3GeneratedBridgeWitness_cnfView, cnfDualDNF, clauseDualTerm,
    negLit, widthDNF, termWidth]

/-- Under the free six-variable restriction, the concrete dual DNF has exactly
forty-eight literal occurrences. -/
theorem twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_dnfSize :
    dnfSize (dnfRestrict (freeRestriction 6)
      (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_cnfView)) = 48 := by
  simp [twoCyclePath3GeneratedBridgeWitness_cnfView, cnfDualDNF, clauseDualTerm,
    negLit, dnfRestrict, termRestrict, freeRestriction, dnfSize]

/-- The free six-variable restriction is good for the concrete dual DNF at
threshold `49`: the canonical tree depth is bounded by the forty-eight literal
occurrences of the restricted dual DNF. -/
theorem twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_good :
    freeRestriction 6 ∉ badSetTerm
      (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_cnfView) 49 6 := by
  rw [mem_badSetTerm]
  intro hbad
  have hle : dtDepth (termCanonicalDT
      (dnfRestrict (freeRestriction 6)
        (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_cnfView))) ≤ 48 := by
    calc
      dtDepth (termCanonicalDT
          (dnfRestrict (freeRestriction 6)
            (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_cnfView)))
          ≤ dnfSize (dnfRestrict (freeRestriction 6)
            (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_cnfView)) :=
            dtDepth_termCanonicalDT_le _
      _ = 48 := twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_dnfSize
  have hcontra : ¬ 49 ≤ 48 := by omega
  exact hcontra (le_trans hbad.2 hle)

/-- Concrete generated CNF-stage record for the six-variable bridge CNF view.  The
decision tree is the leaf-false tree already justified by the S2016 finite
unsatisfiability fact; the generated-stage fields record the concrete dual-DNF
width and goodness premises. -/
def twoCyclePath3GeneratedBridgeWitness_generatedCNFStage :
    GeneratedCNFLayerStage twoCyclePath3GeneratedBridgeWitness_cnfBDFormula where
  view := twoCyclePath3GeneratedBridgeWitness_cnfViewStage
  w := 4
  s := 49
  ℓ := 6
  width_le := by
    exact twoCyclePath3GeneratedBridgeWitness_dualDNF_width_le_four
  ρ := freeRestriction 6
  stars := by
    rw [mem_restrictionsWithStars]
    exact stars_freeRestriction 6
  good := by
    exact twoCyclePath3GeneratedBridgeWitness_dualDNF_freeRestriction_good
  T := DTree.leaf false
  depthBound := 49
  depthBound_eq := rfl
  depth_lt := by simp
  computes := by
    intro a hagree
    calc
      dtEval a (DTree.leaf false : DTree 6) = false := by simp
      _ = BoundedDepthFrege.eval a
          (BoundedDepthRestriction.restrict (freeRestriction 6)
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) := by
          rw [BoundedDepthRestriction.eval_restrict (freeRestriction 6) a
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula hagree,
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics,
            twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false]

/-- S2017 concrete generated-stage compatibility package.  This only connects the
displayed six-variable CNF view to the existing generated CNF-stage record shape;
it does not assert extraction or collapse for arbitrary CNFs or graphs. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_concreteInvariant :
    (twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view =
      twoCyclePath3GeneratedBridgeWitness_cnfViewStage) ∧
    (twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ = freeRestriction 6) ∧
    (twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ℓ = 6) ∧
    (twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.depthBound = 49) ∧
    (twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ ∉ badSetTerm
      (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C)
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.s
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ℓ) ∧
    (∀ a : CNFModel.Assignment 6,
      Agree twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ a →
        dtEval a twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.T =
          BoundedDepthFrege.eval a
            (BoundedDepthRestriction.restrict
              twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
              twoCyclePath3GeneratedBridgeWitness_cnfBDFormula)) ∧
    (∀ a : CNFModel.Assignment 6,
      BoundedDepthFrege.eval a
          (BoundedDepthRestriction.restrict
            twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) =
        BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.good
  · intro a hagree
    exact twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.computes a hagree
  · intro a
    rw [BoundedDepthRestriction.eval_restrict]
    · exact twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics a
    · exact agree_freeRestriction a

/-- A concrete S2015 compatibility predicate: an explicit five-variable
certificate stage is compatible with the six-variable CNF bridge when every
agreeing five-variable stage assignment gives the same restricted-stage formula
value as every six-variable CNF assignment.  The intentionally universal shape
makes any missing stage-to-CNF assignment invariant visible in the theorem
statement. -/
def ExplicitStageSixCNFCompatible (S : ExplicitLayerStage 5) : Prop :=
  ∀ (aStage : CNFModel.Assignment 5) (aCNF : CNFModel.Assignment 6),
    Agree S.ρ aStage →
      BoundedDepthFrege.eval aStage (BoundedDepthRestriction.restrict S.ρ S.F) =
        BoundedDepthIteratedCollapse.cnfEval aCNF twoCyclePath3GeneratedBridgeWitness_cnfView

/-- The concrete empty generated DNF stage is compatible with the finite CNF
semantics because both sides evaluate to `false` for this witness. -/
theorem twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_sixCNFCompatible :
    ExplicitStageSixCNFCompatible
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5))) := by
  intro aStage aCNF hagree
  rw [twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false]
  simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
    emptyGeneratedDNFStage]
  rw [eval_restrict]
  · rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
    rfl
  · exact hagree

/-- The concrete empty generated CNF stage is not compatible with the finite CNF
semantics: its restricted stage formula is `tru`, while the displayed CNF view is
constantly `false`.  This is the Lean-checked limitation for whole-certificate
stage compatibility. -/
theorem twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_not_sixCNFCompatible :
    ¬ ExplicitStageSixCNFCompatible
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))) := by
  intro hcompat
  let aStage : CNFModel.Assignment 5 := fun _ => false
  let aCNF : CNFModel.Assignment 6 := fun _ => false
  have hagree : Agree
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))).ρ aStage := by
    simpa [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedCNF,
      emptyGeneratedCNFStage, aStage] using agree_freeRestriction aStage
  have h := hcompat aStage aCNF hagree
  have htf : true = false := by
    simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedCNF,
      emptyGeneratedCNFStage, ExplicitStageSixCNFCompatible, aStage, aCNF,
      BoundedDepthFrege.eval, BoundedDepthRestriction.restrict_tru,
      twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false] at h
  cases htf

/-- S2015 concrete finite compatibility gate for the certificate packaged by
`twoCyclePath3GeneratedBridgeWitness_finiteCNFSemanticBridgeConsumer`.  The
generated schedule is exactly the empty DNF/CNF/DNF stage list; the two empty DNF
stages are compatible with the six-variable CNF semantics, while the middle
`tru` CNF stage is not.  Therefore the present certificate does not carry a
whole-stage-list invariant tying every explicit stage to the six-variable CNF
bridge. -/
theorem twoCyclePath3GeneratedBridgeWitness_finiteCNFCompatibilityGate :
    (∀ a : CNFModel.Assignment 6,
      BoundedDepthIteratedCollapse.cnfEval a twoCyclePath3GeneratedBridgeWitness_cnfView =
        false) ∧
    twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages =
      [GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5),
        GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5),
        GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5)] ∧
    ExplicitStageSixCNFCompatible
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5))) ∧
    ¬ ExplicitStageSixCNFCompatible
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))) ∧
    ¬ (∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
      ExplicitStageSixCNFCompatible G.toExplicit) := by
  refine ⟨twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_sixCNFCompatible
  · exact twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_not_sixCNFCompatible
  · intro hall
    apply twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_not_sixCNFCompatible
    apply hall
    simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3]

/-! S2018: generated CNF-stage schedule connection and whole-certificate boundary. -/

/-- Singleton generated k-layer schedule containing exactly the S2017 concrete
generated CNF stage.  This connects the named six-variable CNF stage to the
existing generated k-layer certificate infrastructure without asserting any
whole-certificate claim for the older five-variable bridge schedule. -/
def twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule :
    GeneratedKLayerSchedule 6 :=
  generatedCNFSingletonSchedule twoCyclePath3GeneratedBridgeWitness_generatedCNFStage

/-! S2019: reusable generated CNF singleton theorem instantiated on the bridge. -/

/-- S2019 instantiation of the reusable singleton generated-CNF-stage certificate
connection on the concrete S2017 generated CNF stage.  The theorem keeps the
generic `S.s`, restriction-stars, goodness, common-extension, and assignment
semantics facts before the later concrete theorem specializes the accounting to
`49` and the restriction to `freeRestriction 6`. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_reusableCertificateConnection :
    ∃ C : KLayerCollapseCertificate 6,
      twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule.generatedStages ≠ [] ∧
        C.stages =
          twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule.generatedStages.map
            (fun G => G.toExplicit) ∧
        stageDepthSum C.stages =
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.s ∧
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ ∈
          restrictionsWithStars 6 twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ℓ ∧
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ ∉ badSetTerm
          (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C)
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.s
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ℓ ∧
        (∃ a : CNFModel.Assignment 6, ∀ H, H ∈ C.stages → Agree H.ρ a) ∧
        (∀ a : CNFModel.Assignment 6,
          Agree twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ a →
            dtEval a twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.T =
              BoundedDepthFrege.eval a
                (BoundedDepthRestriction.restrict
                  twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
                  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) ∧
            BoundedDepthFrege.eval a
                (BoundedDepthRestriction.restrict
                  twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
                  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) =
              BoundedDepthIteratedCollapse.cnfEval a
                twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C) := by
  simpa [twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule] using
    generatedCNFSingletonSchedule_certificateConnection
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage

/-- S2018 concrete k-layer compatibility package for the S2017 generated CNF
stage.  The certificate is a singleton generated schedule over the six CNF
variables; it records the explicit free restriction, good-restriction premise,
whole-schedule common extension, and restricted-formula/CNF evaluator invariant. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_kLayerCompatibility :
    ∃ C : KLayerCollapseCertificate 6,
      twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule.generatedStages ≠ [] ∧
        C.stages =
          twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule.generatedStages.map
            (fun G => G.toExplicit) ∧
        stageDepthSum C.stages = 49 ∧
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ = freeRestriction 6 ∧
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ ∉ badSetTerm
          (cnfDualDNF twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C)
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.s
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ℓ ∧
        (∃ a : CNFModel.Assignment 6, ∀ H, H ∈ C.stages → Agree H.ρ a) ∧
        (∀ a : CNFModel.Assignment 6,
          Agree twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ a →
            dtEval a twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.T =
              BoundedDepthFrege.eval a
                (BoundedDepthRestriction.restrict
                  twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
                  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) ∧
            BoundedDepthFrege.eval a
                (BoundedDepthRestriction.restrict
                  twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
                  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) =
              BoundedDepthIteratedCollapse.cnfEval a
                twoCyclePath3GeneratedBridgeWitness_cnfView) := by
  rcases twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_reusableCertificateConnection with
    ⟨C, hne, hstages, hsum, _hstars, hgood, hcompat, hsem⟩
  refine ⟨C, hne, hstages, ?_, rfl, hgood, hcompat, ?_⟩
  · calc
      stageDepthSum C.stages = twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.s := hsum
      _ = 49 := by
          simp [twoCyclePath3GeneratedBridgeWitness_generatedCNFStage]
  · intro a hagree
    simpa [twoCyclePath3GeneratedBridgeWitness_generatedCNFStage] using hsem a hagree

/-! S2020: cross-arity schedule-to-generated-CNF alignment. -/

/-- The old concrete assignment-lift invariant is now a specialization of the
reusable cross-arity alignment predicate from a five-variable explicit stage to
the S2017 six-variable generated CNF stage. -/
def ExplicitStageGeneratedCNFStageInvariant (S : ExplicitLayerStage 5) : Prop :=
  ExplicitStageGeneratedCNFStageAlignment S
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage

/-- The empty generated DNF stage admits the concrete assignment-lift invariant:
both the five-variable restricted stage and the six-variable generated CNF stage
compute `false`. -/
theorem twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_generatedCNFStageInvariant :
    ExplicitStageGeneratedCNFStageInvariant
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5))) := by
  refine ⟨fun _ => fun _ => false, ?_⟩
  intro aStage hagree
  refine ⟨?_, ?_, ?_⟩
  · simpa [twoCyclePath3GeneratedBridgeWitness_generatedCNFStage] using
      agree_freeRestriction (fun _ : Fin 6 => false)
  · simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
      emptyGeneratedDNFStage, twoCyclePath3GeneratedBridgeWitness_generatedCNFStage]
    rw [BoundedDepthRestriction.eval_restrict]
    · rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
      rfl
    · exact hagree
  · simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
      emptyGeneratedDNFStage, twoCyclePath3GeneratedBridgeWitness_generatedCNFStage,
      twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false]
    rw [BoundedDepthRestriction.eval_restrict]
    · rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
      rfl
    · exact hagree

/-- The middle empty generated CNF stage cannot satisfy the assignment-lift
invariant: its restricted five-variable stage formula is `tru`, while the S2017
generated six-variable CNF stage and displayed CNF evaluator are constantly
`false`. -/
theorem twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant :
    ¬ ExplicitStageGeneratedCNFStageInvariant
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))) := by
  intro hcompat
  rcases hcompat with ⟨lift, hlift⟩
  let aStage : CNFModel.Assignment 5 := fun _ => false
  have hagree : Agree
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))).ρ aStage := by
    simpa [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedCNF,
      emptyGeneratedCNFStage, aStage] using agree_freeRestriction aStage
  have h := hlift aStage hagree
  have htf : true = false := by
    have hfalse :
        BoundedDepthIteratedCollapse.cnfEval (lift aStage)
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C = false := by
      simpa [twoCyclePath3GeneratedBridgeWitness_generatedCNFStage] using
        twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false (lift aStage)
    have hleft :
        BoundedDepthFrege.eval aStage
          (BoundedDepthRestriction.restrict
            (GeneratedExplicitLayerStage.toExplicit
              (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))).ρ
            (GeneratedExplicitLayerStage.toExplicit
              (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))).F) = true := by
      simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedCNF,
        emptyGeneratedCNFStage, aStage, BoundedDepthRestriction.restrict_tru,
        BoundedDepthFrege.eval_tru]
    calc
      true = BoundedDepthFrege.eval aStage
          (BoundedDepthRestriction.restrict
            (GeneratedExplicitLayerStage.toExplicit
              (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))).ρ
            (GeneratedExplicitLayerStage.toExplicit
              (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))).F) := hleft.symm
      _ = BoundedDepthIteratedCollapse.cnfEval (lift aStage)
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C := h.2.2
      _ = false := hfalse
  cases htf

/-- S2018 boundary theorem: the S2017 generated CNF stage connects to the
six-variable generated k-layer certificate infrastructure as a singleton schedule,
but the pre-existing three-stage `twoCyclePath3GeneratedBridgeWitness` schedule
does not carry a whole-certificate assignment-lift invariant to that CNF stage.
The exact obstruction is the middle empty-CNF/`tru` stage. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_certificateBoundary :
    (∃ C : KLayerCollapseCertificate 6,
      twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule.generatedStages ≠ [] ∧
        C.stages =
          twoCyclePath3GeneratedBridgeWitness_generatedCNFSingletonSchedule.generatedStages.map
            (fun G => G.toExplicit) ∧
        stageDepthSum C.stages = 49 ∧
        (∃ a : CNFModel.Assignment 6, ∀ H, H ∈ C.stages → Agree H.ρ a)) ∧
    ¬ (∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
      ExplicitStageGeneratedCNFStageInvariant G.toExplicit) := by
  refine ⟨?_, ?_⟩
  · rcases twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_kLayerCompatibility with
      ⟨C, hne, hstages, hsum, _hrho, _hgood, hcompat, _hsem⟩
    exact ⟨C, hne, hstages, hsum, hcompat⟩
  · intro hall
    apply twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant
    apply hall
    simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3]

/-- S2019 schedule-alignment classification for the old bridge schedule.  The
reusable singleton theorem provides the generated-CNF certificate connection;
what remains for the old five-variable schedule is the missing assignment-lift
invariant, with the concrete failing member being the middle empty-CNF/`tru`
stage. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignmentObstruction :
    (∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
      G = GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5) ∨
        G = GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5)) ∧
    ExplicitStageGeneratedCNFStageInvariant
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5))) ∧
    ¬ ExplicitStageGeneratedCNFStageInvariant
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))) ∧
    ¬ (∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
      ExplicitStageGeneratedCNFStageInvariant G.toExplicit) := by
  refine ⟨?_,
    twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_generatedCNFStageInvariant,
    twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant,
    ?_⟩
  · intro G hG
    simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3] at hG
    rcases hG with hG | hG | hG
    · exact Or.inl hG
    · exact Or.inr hG
    · exact Or.inl hG
  · intro hall
    apply twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant
    apply hall
    simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3]

/-- The reusable whole-schedule alignment predicate specializes to the old
`twoCyclePath3GeneratedBridgeWitness` schedule exactly as the concrete invariant
over every generated member of that schedule. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignment_iff_each :
    GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage ↔
      ∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
        ExplicitStageGeneratedCNFStageInvariant G.toExplicit := by
  rfl

/-- Under the reusable cross-arity schedule-alignment invariant, the old
five-variable generated DNF/CNF/DNF bridge schedule does not align to the S2017
six-variable generated CNF stage.  The generic obstruction lemma is instantiated
with the middle empty-CNF/`tru` member as the failing stage. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment :
    ¬ GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  apply not_generatedScheduleGeneratedCNFStageAlignment_of_failing_member
    twoCyclePath3GeneratedBridgeWitness.schedule
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
    (H := GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))
  · simp [twoCyclePath3GeneratedBridgeWitness, emptyGeneratedKLayerSchedule3]
  · exact twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant

/-- S2020 theorem-local boundary package: the generic cross-arity schedule
alignment predicate agrees with per-member alignment on the old schedule, the old
empty-DNF member aligns, the middle empty-CNF/`tru` member fails, and that failing
member blocks whole-schedule alignment by the reusable obstruction lemma. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_crossArityScheduleAlignmentBoundary :
    (GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage ↔
      ∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness.schedule.generatedStages →
        ExplicitStageGeneratedCNFStageInvariant G.toExplicit) ∧
    ExplicitStageGeneratedCNFStageInvariant
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 5))) ∧
    ¬ ExplicitStageGeneratedCNFStageInvariant
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf (emptyGeneratedCNFStage 5))) ∧
    ¬ GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact ⟨twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_scheduleAlignment_iff_each,
    twoCyclePath3GeneratedBridgeWitness_emptyDNFStage_generatedCNFStageInvariant,
    twoCyclePath3GeneratedBridgeWitness_emptyCNFStage_no_generatedCNFStageInvariant,
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment⟩

/-! S2021: first positive non-singleton generated-schedule alignment example. -/

/-- Same-arity positive alignment for the six-variable empty-DNF generated member.
The lift is the identity on six-variable assignments; both the source empty-DNF
stage and the target generated CNF stage compute `false` for the displayed
bridge witness. -/
def twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_sameArityAssignmentLiftAlignment :
    SameArityStageGeneratedCNFStageAlignment
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 6)))
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  refine
    { lift := fun a => a
      lift_agree := ?_
      lift_tree_eval := ?_
      lift_cnf_eval := ?_ }
  · intro aStage hagree
    simpa [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
      emptyGeneratedDNFStage, twoCyclePath3GeneratedBridgeWitness_generatedCNFStage]
      using hagree
  · intro aStage hagree
    simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
      emptyGeneratedDNFStage, twoCyclePath3GeneratedBridgeWitness_generatedCNFStage]
    rw [BoundedDepthRestriction.eval_restrict]
    · rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
      rfl
    · exact hagree
  · intro aStage hagree
    have hsource :
        BoundedDepthFrege.eval aStage
          (BoundedDepthRestriction.restrict
            (GeneratedExplicitLayerStage.toExplicit
              (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 6))).ρ
            (GeneratedExplicitLayerStage.toExplicit
              (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 6))).F) = false := by
      simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
        emptyGeneratedDNFStage]
      rw [BoundedDepthRestriction.eval_restrict]
      · rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
        rfl
      · exact hagree
    have htarget :
        BoundedDepthIteratedCollapse.cnfEval aStage
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C = false := by
      simpa [twoCyclePath3GeneratedBridgeWitness_generatedCNFStage] using
        twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false aStage
    exact hsource.trans htarget.symm

/-- The structured identity lift for the six-variable empty-DNF member forgets to
the existing S2020 existential alignment predicate. -/
theorem twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_generatedCNFStageAlignment :
    ExplicitStageGeneratedCNFStageAlignment
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 6)))
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact sameArityStageGeneratedCNFStageAlignment_toExplicitStageGeneratedCNFStageAlignment
    twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_sameArityAssignmentLiftAlignment

/-- Same-arity self-alignment for the S2017 generated CNF stage.  The identity
lift preserves the generated restriction, the generated decision-tree semantics,
and the concrete CNF-view semantics. -/
def twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_sameAritySelfAlignment :
    SameArityStageGeneratedCNFStageAlignment
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage))
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  refine
    { lift := fun a => a
      lift_agree := ?_
      lift_tree_eval := ?_
      lift_cnf_eval := ?_ }
  · intro aStage hagree
    exact hagree
  · intro aStage hagree
    exact (twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.computes
      aStage hagree).symm
  · intro aStage hagree
    calc
      BoundedDepthFrege.eval aStage
          (BoundedDepthRestriction.restrict
            twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula) =
          BoundedDepthFrege.eval aStage
            twoCyclePath3GeneratedBridgeWitness_cnfBDFormula :=
            BoundedDepthRestriction.eval_restrict
              twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.ρ aStage
              twoCyclePath3GeneratedBridgeWitness_cnfBDFormula hagree
      _ = BoundedDepthIteratedCollapse.cnfEval aStage
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.C := by
          exact twoCyclePath3GeneratedBridgeWitness_generatedCNFStage.view.sem_eq aStage

/-- The structured identity self-lift for the generated CNF member forgets to the
existing S2020 existential alignment predicate. -/
theorem twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_selfAlignment :
    ExplicitStageGeneratedCNFStageAlignment
      (GeneratedExplicitLayerStage.toExplicit
        (GeneratedExplicitLayerStage.cnf
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage))
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact sameArityStageGeneratedCNFStageAlignment_toExplicitStageGeneratedCNFStageAlignment
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_sameAritySelfAlignment

/-- First positive non-singleton generated schedule aligned to the S2017 generated
CNF stage.  It stays in the same six-variable arity and uses the existing free
restrictions, so common-extension compatibility is witnessed directly. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule :
    GeneratedKLayerSchedule 6 where
  generatedStages :=
    [GeneratedExplicitLayerStage.dnf (emptyGeneratedDNFStage 6),
      GeneratedExplicitLayerStage.cnf twoCyclePath3GeneratedBridgeWitness_generatedCNFStage]
  alternating := by
    simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
      explicitStageOfGeneratedCNF, emptyGeneratedDNFStage,
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage, LayerKind.Alternating]
  compatible := by
    refine ⟨fun _ => false, ?_⟩
    intro G hG
    simp [GeneratedExplicitLayerStage.toExplicit, explicitStageOfGeneratedDNF,
      explicitStageOfGeneratedCNF, emptyGeneratedDNFStage,
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage] at hG ⊢
    rcases hG with hG | hG
    · subst G
      exact agree_freeRestriction (fun _ : Fin 6 => false)
    · subst G
      exact agree_freeRestriction (fun _ : Fin 6 => false)

/-- The positive aligned schedule is genuinely non-singleton: it contains the
empty-DNF six-variable member and the concrete generated CNF member. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_length :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule.generatedStages.length = 2 := by
  rfl

/-- Every generated member of the positive two-stage schedule aligns to the S2017
generated CNF stage through structured same-arity lift data. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_sameArityAlignment :
    SameArityGeneratedScheduleGeneratedCNFStageAlignment
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  intro G hG
  simp [twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule] at hG
  rcases hG with hG | hG
  · subst G
    exact ⟨twoCyclePath3GeneratedBridgeWitness_emptyDNFStage6_sameArityAssignmentLiftAlignment⟩
  · subst G
    exact ⟨twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_sameAritySelfAlignment⟩

/-- Every generated member of the positive two-stage schedule aligns to the S2017
generated CNF stage after forgetting the structured same-arity lift records to the
S2020 existential predicate. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_aligns_each :
    ∀ G, G ∈ twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule.generatedStages →
      ExplicitStageGeneratedCNFStageAlignment G.toExplicit
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact sameArityGeneratedScheduleGeneratedCNFStageAlignment_toGeneratedScheduleGeneratedCNFStageAlignment
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_sameArityAlignment

/-- The positive non-singleton schedule satisfies the reusable S2020 whole-schedule
alignment predicate by forgetting the S2022 structured same-arity lift data. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_alignment :
    GeneratedScheduleGeneratedCNFStageAlignment
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact sameArityGeneratedScheduleGeneratedCNFStageAlignment_toGeneratedScheduleGeneratedCNFStageAlignment
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_sameArityAlignment

/-- S2021 theorem-local contrast: a same-arity two-stage generated schedule is
non-singleton and aligned to the S2017 generated CNF stage, while the older
five-variable bridge schedule remains blocked by the S2020 middle empty-CNF/`tru`
obstruction. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveVsOldScheduleAlignmentBoundary :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule.generatedStages.length = 2 ∧
    GeneratedScheduleGeneratedCNFStageAlignment
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage ∧
    ¬ GeneratedScheduleGeneratedCNFStageAlignment
      twoCyclePath3GeneratedBridgeWitness.schedule
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact ⟨twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_length,
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_alignment,
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment⟩

/-! S2023: bounded parameterized positive same-arity alignment family. -/

/-- The concrete S2021/S2022 positive aligned schedule as a one-index bounded
same-arity family.  The bound is the exact two-stage length of the supplied
schedule; this is a family record specialization, not an arbitrary compatibility
claim for generated schedules. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily :
    BoundedPositiveSameArityGeneratedScheduleAlignmentFamily Unit 2 where
  arity := fun _ => 6
  formula := fun _ => twoCyclePath3GeneratedBridgeWitness_cnfBDFormula
  target := fun _ => twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
  schedule := fun _ => twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule
  schedule_nonempty := by
    intro _
    simp [twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule]
  schedule_length_le := by
    intro _
    rw [twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_length]
  sameArityAlignment := by
    intro _
    exact twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_sameArityAlignment

/-- The bounded family specializes back to the concrete `twoCyclePath3` positive
aligned schedule and generated CNF target. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_specializes :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule () =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target () =
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.arity () = 6 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The concrete family member inherits the uniform length-two bound. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_length_le :
    (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages.length ≤
      2 := by
  exact boundedPositiveSameArityGeneratedScheduleAlignmentFamily_length_le
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily ()

/-- The concrete family member inherits whole-schedule alignment by forgetting the
S2022 structured same-arity lift data. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_alignment :
    GeneratedScheduleGeneratedCNFStageAlignment
      (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
      (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ()) := by
  exact boundedPositiveSameArityGeneratedScheduleAlignmentFamily_alignment
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily ()

/-- S2023 theorem-local boundary package: the supplied one-index family is
nonempty, uniformly length-bounded by two, specializes to the concrete positive
schedule, aligns through structured same-arity lift data, and leaves the old
five-variable schedule obstruction unchanged. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamilyBoundary :
    (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages ≠ [] ∧
    (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages.length ≤ 2 ∧
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule () =
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule ∧
    GeneratedScheduleGeneratedCNFStageAlignment
      (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
      (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ()) ∧
    ¬ GeneratedScheduleGeneratedCNFStageAlignment
      twoCyclePath3GeneratedBridgeWitness.schedule
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  exact ⟨
    boundedPositiveSameArityGeneratedScheduleAlignmentFamily_nonempty
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily (),
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_length_le,
    rfl,
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_alignment,
    twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment⟩

/-! S2025: theorem-local remaining-hypothesis taxonomy. -/

/-- Supplied data hypothesis: the S2023 `Unit`-indexed family specializes back to
the concrete positive schedule, generated CNF target, and arity. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedDataHypothesis :
    BoundedPositiveSameArityGeneratedScheduleNamedHypothesis where
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule () =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target () =
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.arity () = 6
  classification :=
    BoundedPositiveSameArityGeneratedScheduleHypothesisClass.suppliedData

/-- Already-audited finite bridge facts: the concrete family member is nonempty,
has the length-two bound, aligns to the target, and leaves the old five-variable
schedule blocked by the audited obstruction. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactHypothesis :
    BoundedPositiveSameArityGeneratedScheduleNamedHypothesis where
  proposition :=
    (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages ≠ [] ∧
      (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages.length ≤ 2 ∧
      GeneratedScheduleGeneratedCNFStageAlignment
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ()) ∧
      ¬ GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
  classification :=
    BoundedPositiveSameArityGeneratedScheduleHypothesisClass.alreadyAuditedFiniteBridgeFact

/-- Imported/classical boundary for this theorem-local route.  This names the
ambient classical boundary explicitly without treating it as a proof-complexity
result. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryHypothesis :
    BoundedPositiveSameArityGeneratedScheduleNamedHypothesis where
  proposition := ∀ P : Prop, P ∨ ¬ P
  classification :=
    BoundedPositiveSameArityGeneratedScheduleHypothesisClass.importedClassicalBoundary

/-- Local theorem target exposed by the S2025 shell: the concrete supplied family
member aligns while the old five-variable schedule obstruction remains.  This is
still a finite theorem-local target, not a lower-bound or P-vs-NP claim. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_localTheoremTargetHypothesis :
    BoundedPositiveSameArityGeneratedScheduleNamedHypothesis where
  proposition :=
    GeneratedScheduleGeneratedCNFStageAlignment
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ()) ∧
      ¬ GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
  classification :=
    BoundedPositiveSameArityGeneratedScheduleHypothesisClass.localTheoremTarget

/-- No constructors are provided: this names the unresolved mathematical blocker
without discharging it in the concrete non-vacuity theorem. -/
inductive twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlocker : Prop

/-- Unresolved mathematical blocker for the bounded positive same-arity route. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerHypothesis :
    BoundedPositiveSameArityGeneratedScheduleNamedHypothesis where
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlocker
  classification :=
    BoundedPositiveSameArityGeneratedScheduleHypothesisClass.unresolvedMathematicalBlocker

/-- S2025 theorem-local taxonomy of all named remaining hypotheses for the
bounded positive same-arity generated-schedule route. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy :
    BoundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy where
  suppliedData :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedDataHypothesis
  alreadyAuditedFiniteBridgeFact :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactHypothesis
  importedClassicalBoundary :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryHypothesis
  localTheoremTarget :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_localTheoremTargetHypothesis
  unresolvedMathematicalBlocker :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerHypothesis
  suppliedData_classification := rfl
  alreadyAuditedFiniteBridgeFact_classification := rfl
  importedClassicalBoundary_classification := rfl
  localTheoremTarget_classification := rfl
  unresolvedMathematicalBlocker_classification := rfl

/-- The classification proposition for the concrete S2025 taxonomy. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomyClassifications : Prop :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy.suppliedData.classification =
        BoundedPositiveSameArityGeneratedScheduleHypothesisClass.suppliedData ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy.alreadyAuditedFiniteBridgeFact.classification =
        BoundedPositiveSameArityGeneratedScheduleHypothesisClass.alreadyAuditedFiniteBridgeFact ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy.importedClassicalBoundary.classification =
        BoundedPositiveSameArityGeneratedScheduleHypothesisClass.importedClassicalBoundary ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy.localTheoremTarget.classification =
        BoundedPositiveSameArityGeneratedScheduleHypothesisClass.localTheoremTarget ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy.unresolvedMathematicalBlocker.classification =
        BoundedPositiveSameArityGeneratedScheduleHypothesisClass.unresolvedMathematicalBlocker

/-- The concrete S2025 taxonomy records the intended class for every named
remaining hypothesis. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy_classifications :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomyClassifications := by
  exact boundedPositiveSameArityGeneratedScheduleHypothesisTaxonomy_classifications
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRemainingHypothesisTaxonomy

/-! S2026: theorem-local route obligations for the bounded positive same-arity route. -/

/-- Supplied family-data route obligation: the S2023 `Unit`-indexed family
specializes back to the concrete positive schedule, generated CNF target, and
arity.  It is classified with supplied/audited finite bridge facts for the route
record; this definition records the obligation but does not prove it. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedFamilyDataRouteObligation :
    BoundedPositiveSameArityGeneratedScheduleRouteObligation where
  name := "twoCyclePath3 supplied Unit-indexed family data"
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule () =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target () =
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.arity () = 6
  classification :=
    BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.suppliedAuditedFiniteBridgeFact

/-- Audited finite bridge-fact route obligation: nonemptiness, the length-two
bound, same-arity alignment, and the old five-variable obstruction are the finite
facts already audited before this theorem shell.  The route record names them
without using them to prove the remaining route obligations. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactRouteObligation :
    BoundedPositiveSameArityGeneratedScheduleRouteObligation where
  name := "twoCyclePath3 audited finite nonvacuity, alignment, and old obstruction"
  proposition :=
    (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages ≠ [] ∧
      (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages.length ≤ 2 ∧
      GeneratedScheduleGeneratedCNFStageAlignment
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ()) ∧
      ¬ GeneratedScheduleGeneratedCNFStageAlignment
        twoCyclePath3GeneratedBridgeWitness.schedule
        twoCyclePath3GeneratedBridgeWitness_generatedCNFStage
  classification :=
    BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.suppliedAuditedFiniteBridgeFact

/-- Imported/classical route boundary named explicitly rather than hidden inside a
blocker. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryRouteObligation :
    BoundedPositiveSameArityGeneratedScheduleRouteObligation where
  name := "classical excluded-middle boundary for theorem-local bookkeeping"
  proposition := ∀ P : Prop, P ∨ ¬ P
  classification :=
    BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.importedClassicalBoundary

/-- First local theorem target selected for the next attack: package the positive
same-arity generated schedule as a concrete k-layer certificate with exact
aggregate generated-depth accounting and a common-extension witness.  This is a
local schedule/certificate target only; it is not a lower-bound, SAT-solving, or
P-vs-NP claim. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget : Prop :=
  ∃ C : KLayerCollapseCertificate 6,
    C.stages =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule.generatedStages.map
          (fun G => G.toExplicit) ∧
      stageDepthSum C.stages =
        GeneratedExplicitLayerStage.stageDepthSum
          twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule.generatedStages ∧
      ∃ a : CNFModel.Assignment 6, ∀ H, H ∈ C.stages → Agree H.ρ a

/-- Named first local theorem-target route obligation. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTargetRouteObligation :
    BoundedPositiveSameArityGeneratedScheduleRouteObligation where
  name := "prove positive aligned schedule certificate package"
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget
  classification :=
    BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.localTheoremTarget

/-- No constructors are provided: this names the remaining theorem-facing
proof-complexity route blocker after the finite positive schedule target.  The
record around it supplies the audited name and classification that the old opaque
shell blocker lacked. -/
inductive twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation : Prop

/-- Named unresolved mathematical blocker for the route beyond the finite local
schedule/certificate target. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerRouteObligation :
    BoundedPositiveSameArityGeneratedScheduleRouteObligation where
  name := "unresolved proof-complexity route beyond finite schedule certificate"
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation
  classification :=
    BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.unresolvedMathematicalBlocker

/-- S2026 theorem-local route-obligations record replacing the shell's previous
opaque unresolved-blocker dependency with named obligations and audited
classification fields. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations :
    BoundedPositiveSameArityGeneratedScheduleRouteObligations where
  suppliedFamilyData :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedFamilyDataRouteObligation
  auditedFiniteBridgeFact :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactRouteObligation
  importedClassicalBoundary :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_importedClassicalBoundaryRouteObligation
  firstLocalTheoremTarget :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTargetRouteObligation
  unresolvedMathematicalBlocker :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerRouteObligation
  suppliedFamilyData_classification := rfl
  auditedFiniteBridgeFact_classification := rfl
  importedClassicalBoundary_classification := rfl
  firstLocalTheoremTarget_classification := rfl
  unresolvedMathematicalBlocker_classification := rfl

/-- The classification proposition for the concrete S2026 route-obligations
record. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligationsClassifications : Prop :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.suppliedFamilyData.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.suppliedAuditedFiniteBridgeFact ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.auditedFiniteBridgeFact.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.suppliedAuditedFiniteBridgeFact ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.importedClassicalBoundary.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.importedClassicalBoundary ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.firstLocalTheoremTarget.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.localTheoremTarget ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.unresolvedMathematicalBlocker.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.unresolvedMathematicalBlocker

/-- The concrete S2026 route-obligations record preserves the intended class for
every named obligation. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_classifications :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligationsClassifications := by
  exact boundedPositiveSameArityGeneratedScheduleRouteObligations_classifications
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations

/-- The route record explicitly selects the first local theorem target to attack
next. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_firstLocalTheoremTarget :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.firstLocalTheoremTarget.name =
        "prove positive aligned schedule certificate package" ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.firstLocalTheoremTarget.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.localTheoremTarget ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.firstLocalTheoremTarget.proposition =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget := by
  exact ⟨rfl, rfl, rfl⟩

/-- Concrete theorem shell over the `twoCyclePath3` `Unit`-indexed supplied family.
The shell now points to the S2026 named route-obligations record.  No route
obligation is discharged by constructing this shell. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell :
    BoundedPositiveSameArityGeneratedScheduleTheoremShell
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily where
  remainingProofComplexityHypotheses :=
    boundedPositiveSameArityGeneratedScheduleRouteObligations_remainingProofComplexityHypotheses
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations
  conditionalTarget :=
    boundedPositiveSameArityGeneratedScheduleRouteObligations_conditionalTarget
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations
  conditionalStep :=
    boundedPositiveSameArityGeneratedScheduleRouteObligations_conditional
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations

/-- The concrete theorem shell is non-vacuous: it is inhabited by the explicit
`twoCyclePath3` `Unit`-indexed family, and the supplied family data recovers the
nonempty schedule, the length-two bound, and whole-schedule alignment.  The proof
also preserves the old five-variable obstruction as an audited finite boundary
fact, but it does not inhabit the S2026 remaining route-obligations conjunction. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell_nonvacuous :
    ∃ shell : BoundedPositiveSameArityGeneratedScheduleTheoremShell
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily,
      shell.remainingProofComplexityHypotheses =
          boundedPositiveSameArityGeneratedScheduleRouteObligations_remainingProofComplexityHypotheses
            twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations ∧
        shell.conditionalTarget =
          boundedPositiveSameArityGeneratedScheduleRouteObligations_conditionalTarget
            twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations ∧
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligationsClassifications ∧
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.firstLocalTheoremTarget.name =
          "prove positive aligned schedule certificate package" ∧
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages ≠ [] ∧
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages.length ≤ 2 ∧
        GeneratedScheduleGeneratedCNFStageAlignment
          (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
          (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ()) ∧
        ¬ GeneratedScheduleGeneratedCNFStageAlignment
          twoCyclePath3GeneratedBridgeWitness.schedule
          twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  refine ⟨twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell,
    rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations_classifications
  · exact boundedPositiveSameArityGeneratedScheduleAlignmentFamily_nonempty
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily ()
  · exact twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_length_le
  · exact twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_alignment
  · exact twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment

/-- S2026 theorem-local boundary package: the theorem shell consumes the explicit
finite `twoCyclePath3` family data and records named route obligations while the
old five-variable schedule remains blocked by the already-audited alignment
obstruction. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShellBoundary :
    (∃ shell : BoundedPositiveSameArityGeneratedScheduleTheoremShell
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily,
      shell.remainingProofComplexityHypotheses =
          boundedPositiveSameArityGeneratedScheduleRouteObligations_remainingProofComplexityHypotheses
            twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations ∧
        shell.conditionalTarget =
          boundedPositiveSameArityGeneratedScheduleRouteObligations_conditionalTarget
            twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations ∧
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligationsClassifications ∧
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleRouteObligations.firstLocalTheoremTarget.name =
          "prove positive aligned schedule certificate package" ∧
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages ≠ [] ∧
        (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ()).generatedStages.length ≤ 2 ∧
        GeneratedScheduleGeneratedCNFStageAlignment
          (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.schedule ())
          (twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily.target ())) ∧
    ¬ GeneratedScheduleGeneratedCNFStageAlignment
      twoCyclePath3GeneratedBridgeWitness.schedule
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage := by
  refine ⟨?_, twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment⟩
  rcases twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleTheoremShell_nonvacuous with
    ⟨shell, hremaining, htarget, hclassifications, hfirstTarget, hnonempty, hlen, halign,
      _holdObstruction⟩
  exact ⟨shell, hremaining, htarget, hclassifications, hfirstTarget, hnonempty, hlen, halign⟩

/-! S2027: discharge the selected finite local schedule-certificate target. -/

/-- S2027 proves exactly the selected local target from the S2026 route record:
the positive aligned schedule has a generated k-layer certificate preserving its
exact stage list, aggregate generated-depth accounting, and common-extension
witness.  This is finite schedule/certificate infrastructure only. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget_proved :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget := by
  have hnonempty :
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule.generatedStages ≠ [] := by
    simp [twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule]
  rcases generatedNonemptyKLayerCollapse_exists
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule hnonempty with
    ⟨C, _hne, hstages, _hstageEach, hsum, hcompat⟩
  exact ⟨C, hstages, hsum, hcompat⟩

/-! S2028: move the proved local target into audited finite-route status. -/

/-- After S2027, the previously selected first local target is no longer a route
target to attack: it is tracked as an audited finite schedule/certificate fact.
This bookkeeping declaration does not touch the remaining proof-complexity route. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_provedFirstLocalTargetAuditedFiniteFactRouteObligation :
    BoundedPositiveSameArityGeneratedScheduleRouteObligation where
  name := "proved positive aligned schedule certificate package"
  proposition :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget
  classification :=
    BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.suppliedAuditedFiniteBridgeFact

/-- S2028 audited local finite facts now include supplied family data, the prior
finite bridge facts, and the S2027-proved positive schedule certificate package. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts : Prop :=
  twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedFamilyDataRouteObligation.proposition ∧
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_auditedFiniteBridgeFactRouteObligation.proposition ∧
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_provedFirstLocalTargetAuditedFiniteFactRouteObligation.proposition

/-- The post-S2027 audited local finite fact bundle is proved without touching the
remaining proof-complexity route blocker. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts_proved :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨
      boundedPositiveSameArityGeneratedScheduleAlignmentFamily_nonempty
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily (),
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_length_le,
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedScheduleFamily_alignment,
      twoCyclePath3GeneratedBridgeWitness_generatedCNFStage_no_scheduleAlignment⟩
  · exact twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget_proved

/-- The only remaining route after the audited finite facts is the named unresolved
proof-complexity blocker.  This is an isolation label, not a proof of the blocker. -/
def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute : Prop :=
  twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation

/-- S2028 bookkeeping boundary: the S2027-proved target is classified with the
audited finite facts, and the only remaining route proposition is the previously
named unresolved proof-complexity blocker. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RouteObligationBookkeeping :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_provedFirstLocalTargetAuditedFiniteFactRouteObligation.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.suppliedAuditedFiniteBridgeFact ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerRouteObligation.classification =
        BoundedPositiveSameArityGeneratedScheduleRouteObligationClass.unresolvedMathematicalBlocker ∧
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedMathematicalBlockerRouteObligation.proposition := by
  exact ⟨rfl,
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts_proved,
    rfl, rfl⟩

/-! S2030: supplied-refutation finite route contract. -/

/-- S2030 supplied-refutation route contract: it carries only the already audited
post-S2027 finite facts and a supplied bounded-depth Frege refutation of the
concrete `twoCyclePath3` CNF formula.  The contract does not construct the
refutation, prove completeness, or assert any proof-size/depth lower bound. -/
structure TwoCyclePath3PositiveAlignedSuppliedBDRefutationRoute : Prop where
  auditedFiniteFacts :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts
  refutation :
    BDRefutation [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]

/-- Bookkeeping constructor for the S2030 supplied-refutation route.  The only
new input is the supplied `pi`; the audited finite facts are the S2028 bundle. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute_of_refutation
    (pi : BDRefutation [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) :
    TwoCyclePath3PositiveAlignedSuppliedBDRefutationRoute := by
  exact ⟨
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts_proved,
    pi⟩

/-- Local soundness consumer for the S2030 supplied-refutation route.  This is
only the direct `bdFrege_sound` consequence of the supplied finite refutation; it
does not construct the refutation or make a SAT-solving or lower-bound claim. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_suppliedBDRefutationRoute
    (route : TwoCyclePath3PositiveAlignedSuppliedBDRefutationRoute) :
    ¬ ∃ a : CNFModel.Assignment 6,
      ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
        BoundedDepthFrege.eval a f = true := by
  exact BoundedDepthFrege.bdFrege_sound route.refutation

/-! S2032 probing: concrete supplied-refutation attempt. -/

/-- S2032 target-sequent normalization for the concrete singleton hypothesis list.
It unfolds only the local CNF-to-BD representation and structural negation; it is
not a completeness, SAT-solving, or arbitrary-CNF normalization theorem. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_normalization :
    [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula].map BoundedDepthFrege.neg =
      [BDFormula.or ((twoCyclePath3GeneratedBridgeWitness_cnfView.map cnfClauseToBD).attach.map
        (fun f => BoundedDepthFrege.neg f.1))] := by
  simp [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula, cnfToBD,
    BoundedDepthFrege.neg]

/-- Local abbreviation for a concrete six-variable bounded-depth literal used in
the finite S2032 proof tree. -/
def twoCyclePath3GeneratedBridgeWitness_bdLit (i : Fin 6) (sign : Bool) : BDFormula 6 :=
  BDFormula.lit { var := i, sign := sign }

/-- Local two-variable four-minterm negated-sequent pattern used by the concrete
S2032/S2033 witness.  This is only a finite bounded-depth sequent schema over
the displayed literals; it is not a completeness, SAT-solving, or arbitrary-CNF
compatibility theorem. -/
def twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent
    (x y : Fin 6) : List (BDFormula 6) :=
  [BDFormula.and
      [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
        twoCyclePath3GeneratedBridgeWitness_bdLit y false],
    BDFormula.and
      [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
        twoCyclePath3GeneratedBridgeWitness_bdLit y true],
    BDFormula.and
      [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
        twoCyclePath3GeneratedBridgeWitness_bdLit y true],
    BDFormula.and
      [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
        twoCyclePath3GeneratedBridgeWitness_bdLit y false]]

/-- Direct finite bounded-depth Frege proof of the local two-variable
four-minterm negated sequent.  The leaves close only by literal excluded middle
on `x` and `y`; no completeness or SAT-solving theorem is used. -/
theorem twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProof
    (x y : Fin 6) :
    BDProof (twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent x y) := by
  apply BDProof.andIntro
  intro f hf
  simp [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent] at hf
  rcases hf with rfl | rfl
  · apply BDProof.weaken
      (Γ := [BDFormula.and
          [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
            twoCyclePath3GeneratedBridgeWitness_bdLit y true],
        twoCyclePath3GeneratedBridgeWitness_bdLit x false,
        BDFormula.and
          [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
            twoCyclePath3GeneratedBridgeWitness_bdLit y true],
        BDFormula.and
          [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
            twoCyclePath3GeneratedBridgeWitness_bdLit y false]])
    · apply BDProof.andIntro
      intro f hf
      simp at hf
      rcases hf with rfl | rfl
      · exact BDProof.litEM _ x (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
      · apply BDProof.weaken
          (Γ := [BDFormula.and
              [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
                twoCyclePath3GeneratedBridgeWitness_bdLit y false],
            twoCyclePath3GeneratedBridgeWitness_bdLit y true,
            twoCyclePath3GeneratedBridgeWitness_bdLit x false,
            BDFormula.and
              [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
                twoCyclePath3GeneratedBridgeWitness_bdLit y true]])
        · apply BDProof.andIntro
          intro f hf
          simp at hf
          rcases hf with rfl | rfl
          · exact BDProof.litEM _ x (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          · exact BDProof.litEM _ y (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
        · intro g hg
          simp at hg ⊢
          tauto
    · intro g hg
      simp [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent] at hg ⊢
      tauto
  · apply BDProof.weaken
      (Γ := [BDFormula.and
          [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
            twoCyclePath3GeneratedBridgeWitness_bdLit y true],
        twoCyclePath3GeneratedBridgeWitness_bdLit y false,
        BDFormula.and
          [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
            twoCyclePath3GeneratedBridgeWitness_bdLit y true],
        BDFormula.and
          [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
            twoCyclePath3GeneratedBridgeWitness_bdLit y false]])
    · apply BDProof.andIntro
      intro f hf
      simp at hf
      rcases hf with rfl | rfl
      · apply BDProof.weaken
          (Γ := [BDFormula.and
              [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
                twoCyclePath3GeneratedBridgeWitness_bdLit y true],
            twoCyclePath3GeneratedBridgeWitness_bdLit x true,
            twoCyclePath3GeneratedBridgeWitness_bdLit y false,
            BDFormula.and
              [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
                twoCyclePath3GeneratedBridgeWitness_bdLit y false]])
        · apply BDProof.andIntro
          intro f hf
          simp at hf
          rcases hf with rfl | rfl
          · exact BDProof.litEM _ x (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          · exact BDProof.litEM _ y (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
        · intro g hg
          simp at hg ⊢
          tauto
      · exact BDProof.litEM _ y (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
    · intro g hg
      simp [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent] at hg ⊢
      tauto

/-- Measured trace counterpart of the local two-variable four-minterm finite
bounded-depth proof.  This mirrors the concrete `BDProof` above and carries only
the same literal excluded-middle leaves, weakening, and conjunction nodes. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProofTrace
    (x y : Fin 6) :
    BDProofTrace (twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent x y) := by
  apply BDProofTrace.andIntro
  intro f hf
  simp [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent] at hf
  by_cases hxf : f = twoCyclePath3GeneratedBridgeWitness_bdLit x false
  · subst f
    apply BDProofTrace.weaken
        (Γ := [BDFormula.and
            [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
              twoCyclePath3GeneratedBridgeWitness_bdLit y true],
          twoCyclePath3GeneratedBridgeWitness_bdLit x false,
          BDFormula.and
            [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
              twoCyclePath3GeneratedBridgeWitness_bdLit y true],
          BDFormula.and
            [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
              twoCyclePath3GeneratedBridgeWitness_bdLit y false]])
    · apply BDProofTrace.andIntro
      intro f hf
      simp at hf
      by_cases hxt : f = twoCyclePath3GeneratedBridgeWitness_bdLit x true
      · subst f
        exact BDProofTrace.litEM _ x (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
      · have hyt : f = twoCyclePath3GeneratedBridgeWitness_bdLit y true := by
          simpa [hxt] using hf
        subst f
        apply BDProofTrace.weaken
            (Γ := [BDFormula.and
                [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
                  twoCyclePath3GeneratedBridgeWitness_bdLit y false],
              twoCyclePath3GeneratedBridgeWitness_bdLit y true,
              twoCyclePath3GeneratedBridgeWitness_bdLit x false,
              BDFormula.and
                [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
                  twoCyclePath3GeneratedBridgeWitness_bdLit y true]])
        · apply BDProofTrace.andIntro
          intro f hf
          simp at hf
          by_cases hxt : f = twoCyclePath3GeneratedBridgeWitness_bdLit x true
          · subst f
            exact BDProofTrace.litEM _ x (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          · have hyf : f = twoCyclePath3GeneratedBridgeWitness_bdLit y false := by
              simpa [hxt] using hf
            subst f
            exact BDProofTrace.litEM _ y (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
        · intro g hg
          simp at hg ⊢
          tauto
    · intro g hg
      simp [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent] at hg ⊢
      tauto
  · have hyf : f = twoCyclePath3GeneratedBridgeWitness_bdLit y false := by
      simpa [hxf] using hf
    subst f
    apply BDProofTrace.weaken
        (Γ := [BDFormula.and
            [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
              twoCyclePath3GeneratedBridgeWitness_bdLit y true],
          twoCyclePath3GeneratedBridgeWitness_bdLit y false,
          BDFormula.and
            [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
              twoCyclePath3GeneratedBridgeWitness_bdLit y true],
          BDFormula.and
            [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
              twoCyclePath3GeneratedBridgeWitness_bdLit y false]])
    · apply BDProofTrace.andIntro
      intro f hf
      simp at hf
      by_cases hxt : f = twoCyclePath3GeneratedBridgeWitness_bdLit x true
      · subst f
        apply BDProofTrace.weaken
            (Γ := [BDFormula.and
                [twoCyclePath3GeneratedBridgeWitness_bdLit x false,
                  twoCyclePath3GeneratedBridgeWitness_bdLit y true],
              twoCyclePath3GeneratedBridgeWitness_bdLit x true,
              twoCyclePath3GeneratedBridgeWitness_bdLit y false,
              BDFormula.and
                [twoCyclePath3GeneratedBridgeWitness_bdLit x true,
                  twoCyclePath3GeneratedBridgeWitness_bdLit y false]])
        · apply BDProofTrace.andIntro
          intro f hf
          simp at hf
          by_cases hxf : f = twoCyclePath3GeneratedBridgeWitness_bdLit x false
          · subst f
            exact BDProofTrace.litEM _ x (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          · have hyt : f = twoCyclePath3GeneratedBridgeWitness_bdLit y true := by
              simpa [hxf] using hf
            subst f
            exact BDProofTrace.litEM _ y (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
              (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
        · intro g hg
          simp at hg ⊢
          tauto
      · have hyt : f = twoCyclePath3GeneratedBridgeWitness_bdLit y true := by
          simpa [hxt] using hf
        subst f
        exact BDProofTrace.litEM _ y (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
          (by simp [twoCyclePath3GeneratedBridgeWitness_bdLit])
    · intro g hg
      simp [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent] at hg ⊢
      tauto

/-- S2034 second local bounded-depth consumer of the four-minterm negated-sequent
helper, instantiated at concrete variables `2` and `3` from the displayed
six-variable witness.  This is only a finite sequent fact; it does not assert
that a second CNF clause block has the four-minterm shape. -/
theorem twoCyclePath3GeneratedBridgeWitness_vars23FourMintermNegatedSequent_bdProof :
    BDProof
      (twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent
        (2 : Fin 6) (3 : Fin 6)) := by
  exact twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProof
    (2 : Fin 6) (3 : Fin 6)

/-- Negation of the first displayed clause `(x₀ ∨ x₁)`. -/
def twoCyclePath3GeneratedBridgeWitness_negClause00 : BDFormula 6 :=
  BDFormula.and
    [twoCyclePath3GeneratedBridgeWitness_bdLit (0 : Fin 6) false,
      twoCyclePath3GeneratedBridgeWitness_bdLit (1 : Fin 6) false]

/-- Negation of the second displayed clause `(¬x₀ ∨ ¬x₁)`. -/
def twoCyclePath3GeneratedBridgeWitness_negClause11 : BDFormula 6 :=
  BDFormula.and
    [twoCyclePath3GeneratedBridgeWitness_bdLit (0 : Fin 6) true,
      twoCyclePath3GeneratedBridgeWitness_bdLit (1 : Fin 6) true]

/-- Negation of the third displayed clause `(x₀ ∨ ¬x₁)`. -/
def twoCyclePath3GeneratedBridgeWitness_negClause01 : BDFormula 6 :=
  BDFormula.and
    [twoCyclePath3GeneratedBridgeWitness_bdLit (0 : Fin 6) false,
      twoCyclePath3GeneratedBridgeWitness_bdLit (1 : Fin 6) true]

/-- Negation of the fourth displayed clause `(¬x₀ ∨ x₁)`. -/
def twoCyclePath3GeneratedBridgeWitness_negClause10 : BDFormula 6 :=
  BDFormula.and
    [twoCyclePath3GeneratedBridgeWitness_bdLit (0 : Fin 6) true,
      twoCyclePath3GeneratedBridgeWitness_bdLit (1 : Fin 6) false]

/-- A direct bounded-depth Frege proof of the finite four-minterm sequent carried
by the first four concrete clauses.  The leaves close only by literal excluded
middle on variables `0` and `1`; no completeness or SAT-solving theorem is used. -/
theorem twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProof :
    BDProof
      [twoCyclePath3GeneratedBridgeWitness_negClause00,
        twoCyclePath3GeneratedBridgeWitness_negClause11,
        twoCyclePath3GeneratedBridgeWitness_negClause01,
        twoCyclePath3GeneratedBridgeWitness_negClause10] := by
  simpa [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent,
    twoCyclePath3GeneratedBridgeWitness_negClause00,
    twoCyclePath3GeneratedBridgeWitness_negClause11,
    twoCyclePath3GeneratedBridgeWitness_negClause01,
    twoCyclePath3GeneratedBridgeWitness_negClause10] using
    (twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProof
      (0 : Fin 6) (1 : Fin 6))

/-- Measured trace for the first-four-clause finite sequent.  This is the exact
concrete four-minterm trace instantiated at variables `0` and `1`. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProofTrace :
    BDProofTrace
      [twoCyclePath3GeneratedBridgeWitness_negClause00,
        twoCyclePath3GeneratedBridgeWitness_negClause11,
        twoCyclePath3GeneratedBridgeWitness_negClause01,
        twoCyclePath3GeneratedBridgeWitness_negClause10] := by
  simpa [twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent,
    twoCyclePath3GeneratedBridgeWitness_negClause00,
    twoCyclePath3GeneratedBridgeWitness_negClause11,
    twoCyclePath3GeneratedBridgeWitness_negClause01,
    twoCyclePath3GeneratedBridgeWitness_negClause10] using
    (twoCyclePath3GeneratedBridgeWitness_fourMintermNegatedSequent_bdProofTrace
      (0 : Fin 6) (1 : Fin 6))

/-- Direct finite bounded-depth Frege proof of the exact target sequent for the
singleton concrete CNF formula.  The proof weakens the first-four-clause finite
proof into the full sixteen-clause negated sequent and then introduces the outer
disjunction from the structural negation of the CNF conjunction. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProof :
    BDProof ([twoCyclePath3GeneratedBridgeWitness_cnfBDFormula].map BoundedDepthFrege.neg) := by
  rw [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_normalization]
  apply BDProof.orIntro
  apply BDProof.weaken
      (Γ := [twoCyclePath3GeneratedBridgeWitness_negClause00,
        twoCyclePath3GeneratedBridgeWitness_negClause11,
        twoCyclePath3GeneratedBridgeWitness_negClause01,
        twoCyclePath3GeneratedBridgeWitness_negClause10])
  · exact twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProof
  · intro g hg
    simp [twoCyclePath3GeneratedBridgeWitness_negClause00,
      twoCyclePath3GeneratedBridgeWitness_negClause11,
      twoCyclePath3GeneratedBridgeWitness_negClause01,
      twoCyclePath3GeneratedBridgeWitness_negClause10,
      twoCyclePath3GeneratedBridgeWitness_bdLit,
      twoCyclePath3GeneratedBridgeWitness_cnfView, cnfClauseToBD, cnfLiteralToBD,
      BoundedDepthFrege.neg] at hg ⊢
    tauto

/-- Measured trace counterpart of the exact target sequent proof for the
singleton concrete CNF formula. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace :
    BDProofTrace ([twoCyclePath3GeneratedBridgeWitness_cnfBDFormula].map BoundedDepthFrege.neg) := by
  rw [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_normalization]
  apply BDProofTrace.orIntro
  apply BDProofTrace.weaken
      (Γ := [twoCyclePath3GeneratedBridgeWitness_negClause00,
        twoCyclePath3GeneratedBridgeWitness_negClause11,
        twoCyclePath3GeneratedBridgeWitness_negClause01,
        twoCyclePath3GeneratedBridgeWitness_negClause10])
  · exact twoCyclePath3GeneratedBridgeWitness_firstFourNegatedClauses_bdProofTrace
  · intro g hg
    simp [twoCyclePath3GeneratedBridgeWitness_negClause00,
      twoCyclePath3GeneratedBridgeWitness_negClause11,
      twoCyclePath3GeneratedBridgeWitness_negClause01,
      twoCyclePath3GeneratedBridgeWitness_negClause10,
      twoCyclePath3GeneratedBridgeWitness_bdLit,
      twoCyclePath3GeneratedBridgeWitness_cnfView, cnfClauseToBD, cnfLiteralToBD,
      BoundedDepthFrege.neg] at hg ⊢
    tauto

/-- At the Prop-valued proof surface, proof irrelevance identifies the erased
measured trace with the existing concrete target-sequent proof name. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace_erases_to_bdProof :
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace.erase =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProof := by
  exact Subsingleton.elim _ _

/-- Concrete measured bounded-depth Frege refutation trace of the displayed
singleton CNF formula. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace :
    BDRefutationTrace [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] where
  proof := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_negTargetSequent_bdProofTrace

/-- Erasure of the concrete measured trace to the existing Prop-valued
`BDRefutation` surface. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erasedBDRefutation :
    BDRefutation [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] :=
  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace.erase

/-- Concrete supplied bounded-depth Frege refutation of the displayed singleton
CNF formula, exposed as the erasure of the measured S2039 trace. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation :
    BDRefutation [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] where
  proof := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erasedBDRefutation.proof

/-- Erasing the measured trace recovers the existing supplied refutation name at
the Prop-valued refutation surface. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_erases_to_suppliedBDRefutation :
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace.erase =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation := by
  rfl

/-- Node-count resource accessor for the concrete measured refutation trace. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_size : Nat :=
  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace.size

/-- Line-count resource accessor for the concrete measured refutation trace. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_lineCount : Nat :=
  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace.lineCount

/-- Derivation-depth resource accessor for the concrete measured refutation
trace. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_derivationDepth : Nat :=
  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace.derivationDepth

/-- Conclusion-sequent max-formula-depth resource accessor for the concrete
measured refutation trace. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_maxFormulaDepth : Nat :=
  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace.maxFormulaDepth

/-- Resource-budgeted profile for the concrete measured bounded-depth Frege
refutation trace.  The budgets are exactly the existing S2039 accessors, with no
new numerical bounds introduced here. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile :
    BDRefutationTraceProfile [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] where
  trace := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace
  sizeBudget := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_size
  lineCountBudget := twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_lineCount
  derivationDepthBudget :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_derivationDepth
  maxFormulaDepthBudget :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_maxFormulaDepth
  size_le_budget := le_rfl
  lineCount_le_budget := le_rfl
  derivationDepth_le_budget := le_rfl
  maxFormulaDepth_le_budget := le_rfl

/-- Erasure of the concrete resource-budgeted profile to the existing
Prop-valued refutation surface. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile_erasedBDRefutation :
    BDRefutation [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula] :=
  twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile.erase

/-- Local unsatisfiability consumer obtained from the resource-budgeted measured
trace profile. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTraceProfile :
    ¬ ∃ a : CNFModel.Assignment 6,
      ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
        BoundedDepthFrege.eval a f = true := by
  exact bdFregeTraceProfile_sound
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile

/-- Local unsatisfiability consumer obtained directly from the measured trace
soundness theorem. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTrace :
    ¬ ∃ a : CNFModel.Assignment 6,
      ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
        BoundedDepthFrege.eval a f = true := by
  exact bdFregeTrace_sound
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace

/-- The S2030 supplied-refutation route instantiated by the S2032 concrete finite
bounded-depth refutation. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute :
    TwoCyclePath3PositiveAlignedSuppliedBDRefutationRoute := by
  exact twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute_of_refutation
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation

/-- Local unsatisfiability consumer exposed with the concrete supplied refutation
route.  This remains only the soundness consequence of the finite proof above. -/
theorem twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutation :
    ¬ ∃ a : CNFModel.Assignment 6,
      ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
        BoundedDepthFrege.eval a f = true := by
  exact twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_suppliedBDRefutationRoute
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute

/-! S2042: concrete profiled supplied-refutation route package. -/

/-- S2042 Type-valued concrete route package for the positive-aligned
`twoCyclePath3` route.  It bundles only the already-audited finite facts, the
positive aligned schedule certificate, the S2040 profiled measured refutation,
definitional resource-budget identities, local soundness through the profile,
and an equality pinning the remaining proof-complexity route to the existing
unresolved blocker.  It does not inhabit that unresolved blocker. -/
structure TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute : Type where
  auditedFiniteFacts :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts
  positiveAlignedScheduleCertificate :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget
  profile : BDRefutationTraceProfile [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]
  profile_eq :
    profile =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  erases_to_suppliedBDRefutation :
    profile.erase = twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutation
  sizeBudget_eq :
    profile.sizeBudget =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_size
  lineCountBudget_eq :
    profile.lineCountBudget =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_lineCount
  derivationDepthBudget_eq :
    profile.derivationDepthBudget =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_derivationDepth
  maxFormulaDepthBudget_eq :
    profile.maxFormulaDepthBudget =
      twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTrace_maxFormulaDepth
  localUnsat :
    ¬ ∃ a : CNFModel.Assignment 6,
      ∀ f ∈ [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula],
        BoundedDepthFrege.eval a f = true
  remainingUnresolvedProofComplexityRoute_eq :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027RemainingUnresolvedProofComplexityRoute =
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_unresolvedProofComplexityRouteObligation

/-- Concrete S2042 profiled supplied-refutation route.  The package is assembled
from the S2027/S2037/S2039/S2040 finite facts and reflexive pins only; the
unresolved proof-complexity route remains an equality to the named blocker, not
an inhabitant of it. -/
noncomputable def twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute :
    TwoCyclePath3PositiveAlignedProfiledBDRefutationRoute where
  auditedFiniteFacts :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_postS2027AuditedLocalFiniteFacts_proved
  positiveAlignedScheduleCertificate :=
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_firstLocalTheoremTarget_proved
  profile :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_suppliedBDRefutationTraceProfile
  profile_eq := rfl
  erases_to_suppliedBDRefutation := rfl
  sizeBudget_eq := rfl
  lineCountBudget_eq := rfl
  derivationDepthBudget_eq := rfl
  maxFormulaDepthBudget_eq := rfl
  localUnsat :=
    twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_unsat_of_concreteSuppliedBDRefutationTraceProfile
  remainingUnresolvedProofComplexityRoute_eq := rfl

/-- Erasing the S2042 profiled route through the existing supplied-refutation
constructor recovers the already-audited S2030 supplied route. -/
theorem twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute_erases_to_suppliedBDRefutationRoute :
    twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute_of_refutation
        twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_profiledBDRefutationRoute.profile.erase =
      twoCyclePath3GeneratedBridgeWitness_positiveAlignedSchedule_suppliedBDRefutationRoute := by
  exact Subsingleton.elim _ _

end GraphIndexedBridge
end PvNP
