import PvNP.BoundedDepthFrege
import PvNP.BoundedDepthDecisionTree
import PvNP.BoundedDepthRestriction

/-!
# Restricted PHP floor interface

This module starts the bounded-depth Frege/PHP lower-bound floor without claiming
a Frege lower bound.  It provides a restricted pigeonhole formula surface and an
isolated decision-tree depth-floor statement shape.  The floor statement is a
`Prop` interface, not an asserted theorem.
-/

namespace PvNP
namespace RestrictedPHPFloor

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction

/-- Variable index for "pigeon `p` maps to hole `h`" in a `pigeons × holes`
rectangle encoded in `Fin (Nat.succ (pigeons * holes))`, so degenerate empty
rectangles still have a harmless ambient variable type. -/
def phpVar (pigeons holes : Nat) (p : Fin pigeons) (h : Fin holes) :
    Fin (Nat.succ (pigeons * holes)) :=
  ⟨(p.val * holes + h.val) % Nat.succ (pigeons * holes),
    Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Positive literal saying pigeon `p` is assigned to hole `h`. -/
def mapsLit (pigeons holes : Nat) (p : Fin pigeons) (h : Fin holes) :
    Literal (Nat.succ (pigeons * holes)) :=
  { var := phpVar pigeons holes p h, sign := true }

/-- Negative literal saying pigeon `p` is not assigned to hole `h`. -/
def notMapsLit (pigeons holes : Nat) (p : Fin pigeons) (h : Fin holes) :
    Literal (Nat.succ (pigeons * holes)) :=
  { var := phpVar pigeons holes p h, sign := false }

/-- Hole choices allowed for each pigeon in the restricted PHP view. -/
structure RestrictedPHP (pigeons holes : Nat) where
  allowed : Fin pigeons → List (Fin holes)

/-- Enumerate a finite initial segment as `Fin n` values. -/
def finList (n : Nat) : List (Fin n) :=
  List.pmap (fun i hi => (Fin.mk i hi : Fin n))
    (List.range n)
    (by
      intro i hi
      exact List.mem_range.mp hi)

/-- A pigeon must choose at least one allowed hole. -/
def pigeonSomewhereClause {pigeons holes : Nat} (R : RestrictedPHP pigeons holes)
    (p : Fin pigeons) : BDFormula (Nat.succ (pigeons * holes)) :=
  BDFormula.or ((R.allowed p).map (fun h => BDFormula.lit (mapsLit pigeons holes p h)))

/-- Two pigeons may not occupy the same hole. -/
def noCollisionClause (pigeons holes : Nat) (p q : Fin pigeons) (h : Fin holes) :
    BDFormula (Nat.succ (pigeons * holes)) :=
  BDFormula.or [BDFormula.lit (notMapsLit pigeons holes p h),
    BDFormula.lit (notMapsLit pigeons holes q h)]

/-- The restricted PHP formula: all pigeons choose an allowed hole, and all listed
pair/hole collisions are forbidden.  Pair enumeration is intentionally explicit
and finite; duplicate/irrelevant pair clauses are harmless for this boundary
interface. -/
def restrictedPHPFormula {pigeons holes : Nat} (R : RestrictedPHP pigeons holes) :
    BDFormula (Nat.succ (pigeons * holes)) :=
  let ps : List (Fin pigeons) := finList pigeons
  let hs : List (Fin holes) := finList holes
  let someClauses := ps.map (pigeonSomewhereClause R)
  let collisionClauses := ps.bind (fun p =>
    ps.bind (fun q => hs.map (fun h => noCollisionClause pigeons holes p q h)))
  BDFormula.and (someClauses ++ collisionClauses)

/-- A public boundary record for a proposed decision-tree floor.  Supplying this
record is evidence of the exact restricted formula, restriction family, and depth
threshold being studied; it is not by itself a lower-bound proof. -/
structure PHPDepthFloorBoundary (pigeons holes : Nat) where
  view : RestrictedPHP pigeons holes
  restrictionFamily : List (Restriction (Nat.succ (pigeons * holes)))
  depthFloor : Nat

/-- The actual depth-floor statement shape for a boundary record.  It remains an
isolated proposition until proved for a concrete boundary. -/
def PHPDepthFloorStatement {pigeons holes : Nat}
    (B : PHPDepthFloorBoundary pigeons holes) : Prop :=
  ∀ ρ, ρ ∈ B.restrictionFamily → ∀ T : DTree (Nat.succ (pigeons * holes)),
    (∀ a : Assignment (Nat.succ (pigeons * holes)), Agree ρ a →
      dtEval a T = eval a (restrict ρ (restrictedPHPFormula B.view))) →
    B.depthFloor ≤ dtDepth T

/-- The boundary's formula is exactly the restricted PHP formula of its view. -/
theorem phpBoundary_formula_eq {pigeons holes : Nat}
    (B : PHPDepthFloorBoundary pigeons holes) :
    restrictedPHPFormula B.view = restrictedPHPFormula B.view := rfl

end RestrictedPHPFloor
end PvNP
