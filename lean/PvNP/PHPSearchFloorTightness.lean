import PvNP.BDTaitCompleteness

/-!
# Tightness of the `3 x 2` falsified-clause search floor

An explicit correct query tree of depth exactly four for the fixed `3 x 2`
PHP falsified-clause search problem (strategy extracted by exhaustive game
search offline; correctness and depth kernel-checked here by `decide`).
Together with `threeTwoPHPFalsifiedClauseSearchDepthFloor_four` this
FORMALIZES tightness at the `3 x 2` instance: the optimal worst-case query
count there is exactly four.

## HONEST SCOPE STATEMENT (read this)

* Tightness is formalized at the fixed `3 x 2` instance ONLY.  The `2 * h`
  family floor's tightness for general `p > h` remains informal.  As
  everywhere in this lane: a bounded certificate-search statement, NOT a
  Frege/PHP lower bound, NOT an NP/circuit bound, NOT P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPSearchFloorTightness

open CNFModel
open RestrictedPHPFloor

/-- Explicit optimal `3 x 2` falsified-clause search tree (depth four).
Strategy: query `x00`; on the false branch query `x10` (pigeons 0 and 1 lead),
on the true branch query `x10` (collision at hole 0 or pigeon chase); every
branch resolves within four queries. -/
def optimalThreeTwoTree :
    QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause :=
  QueryTree.node threeTwoPHPVar00
    (QueryTree.node threeTwoPHPVar10
      (QueryTree.node threeTwoPHPVar01
        (QueryTree.leaf ThreeTwoPHPFalsifiedClause.pigeon0)
        (QueryTree.node threeTwoPHPVar11
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.pigeon1)
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.collision01h1)))
      (QueryTree.node threeTwoPHPVar21
        (QueryTree.node threeTwoPHPVar20
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.pigeon2)
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.collision12h0))
        (QueryTree.node threeTwoPHPVar01
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.pigeon0)
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.collision02h1))))
    (QueryTree.node threeTwoPHPVar10
      (QueryTree.node threeTwoPHPVar21
        (QueryTree.node threeTwoPHPVar20
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.pigeon2)
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.collision02h0))
        (QueryTree.node threeTwoPHPVar11
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.pigeon1)
          (QueryTree.leaf ThreeTwoPHPFalsifiedClause.collision12h1)))
      (QueryTree.leaf ThreeTwoPHPFalsifiedClause.collision01h0))

/-- The explicit tree is a correct falsified-clause search tree. -/
theorem optimalThreeTwoTree_searchCorrect :
    ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a optimalThreeTwoTree) := by
  intro a
  cases h00 : a threeTwoPHPVar00 <;>
    cases h01 : a threeTwoPHPVar01 <;>
    cases h10 : a threeTwoPHPVar10 <;>
    cases h11 : a threeTwoPHPVar11 <;>
    cases h20 : a threeTwoPHPVar20 <;>
    cases h21 : a threeTwoPHPVar21 <;>
    simp [optimalThreeTwoTree, queryEval, ThreeTwoPHPFalsifiedClause.Valid,
      h00, h01, h10, h11, h20, h21]

/-- The explicit tree has depth exactly four. -/
theorem optimalThreeTwoTree_depth : queryDepth optimalThreeTwoTree = 4 := by
  decide

/-- **Formalized tightness at `3 x 2`.**  The optimal worst-case query count
for the fixed `3 x 2` falsified-clause search problem is EXACTLY four: the
floor of four (`threeTwoPHPFalsifiedClauseSearchDepthFloor_four`) is attained
by the explicit correct tree above. -/
theorem threeTwoPHPFalsifiedClauseSearch_optimal_depth_eq_four :
    (∀ T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause,
      (∀ a : Assignment (Nat.succ (3 * 2)),
        ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) →
      4 ≤ queryDepth T) ∧
    (∃ T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause,
      (∀ a : Assignment (Nat.succ (3 * 2)),
        ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) ∧
      queryDepth T = 4) :=
  ⟨fun T hT => PHPSearchFloor.threeTwoPHPFalsifiedClauseSearchDepthFloor_four T hT,
    ⟨optimalThreeTwoTree, optimalThreeTwoTree_searchCorrect,
      optimalThreeTwoTree_depth⟩⟩

end PHPSearchFloorTightness
end PvNP
