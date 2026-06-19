import Std

namespace PvNP
namespace CNFModel

/-!
Minimal CNF model with literals, clauses, and satisfiability.
This is isolated from BasicDefs to avoid breaking the main chain.
-/

structure Literal (n : Nat) where
  var : Fin n
  sign : Bool  -- true = positive, false = negated
deriving Repr, DecidableEq, BEq

abbrev Clause (n : Nat) := List (Literal n)

abbrev CNF (n : Nat) := List (Clause n)

abbrev Assignment (n : Nat) := Fin n -> Bool

/-- Evaluate a literal under an assignment. -/
def litEval {n : Nat} (a : Assignment n) (l : Literal n) : Bool :=
  if l.sign then a l.var else !a l.var

/-- A clause is satisfied if any literal evaluates to true. -/
def clauseSat {n : Nat} (a : Assignment n) (c : Clause n) : Prop :=
  Exists fun l => l ∈ c ∧ litEval a l = true

/-- A CNF is satisfied if all clauses are satisfied. -/
def cnfSat {n : Nat} (a : Assignment n) (f : CNF n) : Prop :=
  forall c, c ∈ f -> clauseSat a c

/-!
S1761 structural-simplification smoke-test vocabulary.

These computable predicates capture the first cheap, branch-free SAT
simplifications: empty-clause detection, unit propagation, and pure-literal
elimination.  A CNF with `noCheapSimplificationSignal = true` is not solved by
those local tests alone, so any P = NP structural-simplification candidate must
explain its next non-branching progress measure on such inputs.
-/

/-- Enumerate all variables of a finite CNF variable domain. -/
def allVars (n : Nat) : List (Fin n) :=
  List.pmap (fun i hi => (Fin.mk i hi : Fin n))
    (List.range n)
    (by
      intro i hi
      exact List.mem_range.mp hi)

/-- Boolean empty-clause detector. -/
def hasEmptyClause {n : Nat} (f : CNF n) : Bool :=
  f.any (fun c => c.isEmpty)

/-- Boolean unit-clause detector. -/
def hasUnitClause {n : Nat} (f : CNF n) : Bool :=
  f.any (fun c => c.length == 1)

/-- Boolean test that a literal uses a specific variable with a specific sign. -/
def literalMatches {n : Nat} (v : Fin n) (sign : Bool)
    (l : Literal n) : Bool :=
  decide (l.var = v) && decide (l.sign = sign)

/-- Boolean test that a clause contains a specific variable polarity. -/
def clauseHasVarSign {n : Nat} (c : Clause n) (v : Fin n)
    (sign : Bool) : Bool :=
  c.any (literalMatches v sign)

/-- Boolean test that a CNF contains a specific variable polarity. -/
def hasVarSign {n : Nat} (f : CNF n) (v : Fin n) (sign : Bool) :
    Bool :=
  f.any (fun c => clauseHasVarSign c v sign)

/-- Boolean pure-literal detector. -/
def hasPureLiteral {n : Nat} (f : CNF n) : Bool :=
  (allVars n).any (fun v =>
    let pos := hasVarSign f v true
    let neg := hasVarSign f v false
    (pos && !neg) || (neg && !pos))

/--
The first S1761 obstruction signal: no empty clause, no unit clause, and no
pure literal.  This is a candidate-killer smoke test, not a hardness claim.
-/
def noCheapSimplificationSignal {n : Nat} (f : CNF n) : Bool :=
  !hasEmptyClause f && !hasUnitClause f && !hasPureLiteral f

/-- Proposition wrapper for the computable S1761 smoke-test signal. -/
def NoCheapSimplificationSignal {n : Nat} (f : CNF n) : Prop :=
  noCheapSimplificationSignal f = true

/-!
S1763 first structural simplifier surface.

This branch-free cleanup pass captures two standard polynomial-time CNF
normalizations: duplicate-literal deletion inside each clause and deletion of
tautological clauses containing a variable with both polarities.  The pass is
size non-increasing by construction and gives the P = NP lane a concrete first
operation surface to test against the S1761 smoke pair.
-/

/-- First S1763 branch-free simplifier operations. -/
inductive BranchFreeCleanupOp where
  | deleteDuplicateLiterals
  | deleteTautologicalClauses
deriving Repr, DecidableEq

/-- Boolean test that two literals are complementary. -/
def literalComplementary {n : Nat} (l r : Literal n) : Bool :=
  decide (l.var = r.var) && decide (l.sign = !r.sign)

/-- Boolean test that a clause contains a complementary literal pair. -/
def clauseHasComplementaryPair {n : Nat} (c : Clause n) : Bool :=
  c.any (fun l => c.any (literalComplementary l))

/-- Boolean tautological-clause detector. -/
def isTautologicalClause {n : Nat} (c : Clause n) : Bool :=
  clauseHasComplementaryPair c

/-- Delete duplicate literals from a clause. -/
def dedupClause {n : Nat} (c : Clause n) : Clause n :=
  c.eraseDups

/--
One deterministic branch-free cleanup step: delete duplicate literals inside
clauses, then delete tautological clauses.  This is a candidate operation
surface, not a SAT decision procedure.
-/
def branchFreeCleanupStep {n : Nat} (f : CNF n) : CNF n :=
  (f.map dedupClause).filter (fun c => !isTautologicalClause c)

/-- Formula-size proxy used by the first cleanup surface. -/
def cnfLiteralCount {n : Nat} (f : CNF n) : Nat :=
  f.foldl (fun acc c => acc + c.length) 0

/-- Boolean fixed-point test for the first branch-free cleanup surface. -/
def branchFreeCleanupFixedPointSignal {n : Nat} (f : CNF n) : Bool :=
  decide (branchFreeCleanupStep f = f)

/--
Proposition wrapper for formulas where the first S1763 cleanup pass makes no
progress.  This is a candidate-killer fixed-point test, not a hardness claim.
-/
def BranchFreeCleanupFixedPoint {n : Nat} (f : CNF n) : Prop :=
  branchFreeCleanupFixedPointSignal f = true

end CNFModel
end PvNP
