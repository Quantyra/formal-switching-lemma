/-
# Deep-path extraction from a decision tree

The switching-lemma encoding needs: when a (term-)canonical decision tree has
depth `≥ s`, there is a concrete root-to-leaf branch making `≥ s` decisions, from
which the `s` "star" variables are read off.  This file provides that at the pure
`DTree` level: `deepestPath` follows the deeper subtree at each node, and its
length equals the tree depth — so a depth-`≥ s` tree yields a decision list of
length `≥ s`.

This is INFRASTRUCTURE for the switching-lemma encoding, NOT the switching lemma,
NOT a lower bound, NOT P≠NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import PvNP.BoundedDepthDecisionTree

namespace PvNP
namespace BoundedDepthDecisionTree

/-- The deepest root-to-leaf branch: at each `node`, descend into the deeper
subtree, recording the queried variable and the direction taken. -/
def deepestPath {n : Nat} : DTree n → List (Fin n × Bool)
  | .leaf _ => []
  | .node v t0 t1 =>
      if dtDepth t0 ≤ dtDepth t1 then (v, true) :: deepestPath t1
      else (v, false) :: deepestPath t0

/-- **The deepest path realises the depth.** Its length equals `dtDepth t`. -/
theorem deepestPath_length {n : Nat} (t : DTree n) :
    (deepestPath t).length = dtDepth t := by
  induction t with
  | leaf b => simp [deepestPath, dtDepth]
  | node v t0 t1 ih0 ih1 =>
      rw [deepestPath, dtDepth]
      split
      · rename_i h
        rw [List.length_cons, ih1]; omega
      · rename_i h
        rw [List.length_cons, ih0]; omega

/-- **Depth ≥ s yields a length-≥ s decision branch.** From a tree of depth at
least `s`, the deepest path has at least `s` decisions — the branch the encoding
reads its `s` star-variables from. -/
theorem exists_deep_path {n : Nat} (t : DTree n) (s : Nat) (h : s ≤ dtDepth t) :
    s ≤ (deepestPath t).length := by
  rw [deepestPath_length]; exact h

end BoundedDepthDecisionTree
end PvNP
