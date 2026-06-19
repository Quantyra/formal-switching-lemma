import PvNP.BoundedDepthFrege

/-!
# Certified affine/Tseitin extraction boundary

This module adds a public, audited surface for arbitrary finite Tseitin-style
graphs.  It deliberately proves only reusable extraction and collision-handling
lemmas.  It does **not** assert unsatisfiability, expansion, proof-complexity
hardness, or any Frege/PHP lower bound.
-/

namespace PvNP
namespace CertifiedAffine

open CNFModel

/-- An undirected edge over `Fin n`, represented by its two endpoints. -/
structure Edge (n : Nat) where
  u : Fin n
  v : Fin n
deriving Repr, DecidableEq

/-- A finite Tseitin graph surface: an explicit edge list plus vertex charges. -/
structure TseitinGraph (n : Nat) where
  edges : List (Edge n)
  charge : Fin n → Bool

/-- Endpoint incidence. -/
def Edge.Incident {n : Nat} (e : Edge n) (x : Fin n) : Prop :=
  e.u = x ∨ e.v = x

/-- No self-loops.  This is a graph-shape condition, not a hardness property. -/
def NoLoops {n : Nat} (G : TseitinGraph n) : Prop :=
  ∀ e, e ∈ G.edges → e.u ≠ e.v

/-- A simple explicit edge list has no duplicate edge records. -/
def SimpleEdgeList {n : Nat} (G : TseitinGraph n) : Prop :=
  G.edges.Nodup

/-- Edge indices incident to a vertex.  The index is the edge-list position. -/
def incidentEdgeIndices {n : Nat} (G : TseitinGraph n) (x : Fin n) : List Nat :=
  (G.edges.enum.filter (fun p => decide (p.snd.u = x) || decide (p.snd.v = x))).map Prod.fst

/-- Low-degree bound as explicit extraction metadata. -/
def LowDegree {n : Nat} (G : TseitinGraph n) (d : Nat) : Prop :=
  ∀ x, (incidentEdgeIndices G x).length ≤ d

/-- Boolean xor fold with `false` as the empty parity. -/
def xorList : List Bool → Bool
  | [] => false
  | b :: bs => Bool.xor b (xorList bs)

/-- Values of the edge assignment on the incident edge indices. -/
def incidentValues {n : Nat} (G : TseitinGraph n) (α : Nat → Bool) (x : Fin n) : List Bool :=
  (incidentEdgeIndices G x).map α

/-- The Tseitin vertex equation evaluator for the explicit incidence extractor. -/
def vertexParity {n : Nat} (G : TseitinGraph n) (α : Nat → Bool) (x : Fin n) : Bool :=
  decide (xorList (incidentValues G α x) = G.charge x)

/-- A semantic extractor over a domain of vertices. -/
def SemanticExtractorCompleteOn {n : Nat} (G : TseitinGraph n)
    (domain : Fin n → Prop) (X : (Nat → Bool) → Fin n → Bool) : Prop :=
  ∀ α x, domain x → X α x = vertexParity G α x

/-- The canonical incident-edge extractor. -/
def incidentExtractor {n : Nat} (G : TseitinGraph n) (α : Nat → Bool) (x : Fin n) : Bool :=
  vertexParity G α x

/-- The canonical extractor is semantically complete on any chosen vertex domain. -/
theorem incidentExtractor_completeOn {n : Nat} (G : TseitinGraph n)
    (domain : Fin n → Prop) :
    SemanticExtractorCompleteOn G domain (incidentExtractor G) := by
  intro α x _hx
  rfl

/-- Collision handling for a single non-loop edge: if two distinct vertices are
incident to that edge, they must be exactly the two opposite endpoints. -/
theorem incident_collision_endpoints {n : Nat} {e : Edge n} {x y : Fin n}
    (_hloop : e.u ≠ e.v) (hx : e.Incident x) (hy : e.Incident y) (hxy : x ≠ y) :
    (x = e.u ∧ y = e.v) ∨ (x = e.v ∧ y = e.u) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exfalso
    exact hxy (hx.symm.trans hy)
  · exact Or.inl ⟨hx.symm, hy.symm⟩
  · exact Or.inr ⟨hx.symm, hy.symm⟩
  · exfalso
    exact hxy (hx.symm.trans hy)

/-- Public certificate packaging arbitrary simple/low-degree Tseitin extraction
metadata together with the proved semantic extractor connection. -/
structure CertifiedAffineExtraction (n d : Nat) where
  graph : TseitinGraph n
  noLoops : NoLoops graph
  simpleEdges : SimpleEdgeList graph
  lowDegree : LowDegree graph d

/-- Every certified affine extraction exposes a complete canonical semantic
extractor on every selected vertex domain. -/
theorem certifiedAffineExtraction_completeOn {n d : Nat}
    (C : CertifiedAffineExtraction n d) (domain : Fin n → Prop) :
    SemanticExtractorCompleteOn C.graph domain (incidentExtractor C.graph) :=
  incidentExtractor_completeOn C.graph domain

end CertifiedAffine
end PvNP
