/-
# Worst-case depth of the canonical decision tree

The canonical decision tree `canonicalDT D` of a DNF queries one variable per
level and residualizes, so its depth is at most the total literal-occurrence
count `dnfSize D` of the DNF.  This is the DETERMINISTIC worst-case baseline that
Håstad's switching lemma improves: under a random restriction, the depth drops to
`< t` except with small probability.

This file proves only the deterministic bound `dtDepth (canonicalDT D) ≤ dnfSize D`
— it is INFRASTRUCTURE, NOT the switching lemma, NOT a lower bound, NOT P≠NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import PvNP.BoundedDepthCanonicalDT

namespace PvNP
namespace BoundedDepthCanonicalDT

open PvNP.BoundedDepthDecisionTree

/-- **Worst-case depth bound.** The canonical decision tree of a DNF has depth at
most the DNF's total literal-occurrence count.  Proved by the same well-founded
recursion (on `dnfSize`) as `canonicalDT` itself; each query strictly shrinks
`dnfSize` (`dnfSize_assignVar_lt`), so the tree can be no deeper than `dnfSize`. -/
theorem dtDepth_canonicalDT_le {n : Nat} (D : DNF n) :
    dtDepth (canonicalDT D) ≤ dnfSize D := by
  match D with
  | [] => simp [canonicalDT]
  | [] :: D' => simp [canonicalDT]
  | (l :: t) :: D' =>
      rw [show canonicalDT ((l :: t) :: D')
            = DTree.node l.var
                (canonicalDT (assignVar l.var false ((l :: t) :: D')))
                (canonicalDT (assignVar l.var true ((l :: t) :: D'))) from by
            rw [canonicalDT]]
      rw [dtDepth_node]
      have h0 := dtDepth_canonicalDT_le (assignVar l.var false ((l :: t) :: D'))
      have h1 := dtDepth_canonicalDT_le (assignVar l.var true ((l :: t) :: D'))
      have hlt0 := dnfSize_assignVar_lt l.var false l t D' rfl
      have hlt1 := dnfSize_assignVar_lt l.var true l t D' rfl
      omega
  termination_by dnfSize D
  decreasing_by
    · exact dnfSize_assignVar_lt l.var false l t D' rfl
    · exact dnfSize_assignVar_lt l.var true l t D' rfl

end BoundedDepthCanonicalDT
end PvNP
