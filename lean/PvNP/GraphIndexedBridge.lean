import PvNP.CertifiedAffine
import PvNP.BoundedDepthIteratedCollapse

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
  charge := fun _ => false

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

end GraphIndexedBridge
end PvNP
