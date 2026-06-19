import PvNP.BoundedDepthFrege

/-!
# Decision-tree representation for the bounded-depth Frege track

This file builds the **decision-tree object** that is the *target representation*
of a switching lemma, equipped with **real Boolean semantics**, and connects it
to the existing faithful bounded-depth formula model `PvNP.BoundedDepthFrege`.

## HONEST SCOPE STATEMENT (read this)
This is **switching-lemma INFRASTRUCTURE ONLY**.  A switching lemma states that,
under a random restriction, a bounded-depth (small) formula collapses to a
*shallow decision tree*; this file supplies the decision-tree side of that
statement and proves the (easy, self-contained) fact that a decision tree can be
written as a bounded-depth formula computing the **same Boolean function**.

It provides:
* a faithful decision-tree type `DTree n` that branches on a queried variable;
* real recursive Boolean semantics `dtEval` (an actual `Bool`);
* a `dtDepth` measure;
* a conversion `treeToFormula : DTree n → BDFormula n` and the load-bearing
  semantic equivalence `eval_treeToFormula : eval a (treeToFormula t) = dtEval a t`;
* a clean linear depth bound `depth_treeToFormula_le`.

This file does **NOT** prove the switching lemma, does **NOT** prove any lower
bound, and does **NOT** claim P ≠ NP.  It is the representation layer only.

`Assignment n = Fin n → Bool`, `Literal`, `litEval`, the formula type
`BDFormula n`, its `eval`/`depth`, and the `eval_or`/`eval_and`/`eval_lit`
lemmas are all reused from `PvNP.BoundedDepthFrege` / `PvNP.CNFModel`.
-/

namespace PvNP
namespace BoundedDepthDecisionTree

open CNFModel
open BoundedDepthFrege

/-! ## 1. Faithful decision-tree type -/

/--
A Boolean decision tree over variables `Fin n`.

* `leaf b` outputs the constant `b`.
* `node v t0 t1` queries variable `v`; on value `false` it descends into `t0`,
  on value `true` into `t1`.

This is a faithful model: see `dtEval` for the real Boolean semantics.
-/
inductive DTree (n : Nat) : Type where
  | leaf (b : Bool) : DTree n
  | node (v : Fin n) (t0 t1 : DTree n) : DTree n
  deriving Repr

/-! ## 2. Real recursive Boolean semantics -/

/--
Real recursive Boolean semantics of a decision tree.  A `leaf b` outputs `b`;
a `node v t0 t1` branches on the queried value `a v`, taking the `t1` subtree
when `a v = true` and the `t0` subtree when `a v = false`.  Structural recursion.
-/
def dtEval {n : Nat} (a : Assignment n) : DTree n → Bool
  | .leaf b => b
  | .node v t0 t1 => if a v then dtEval a t1 else dtEval a t0

@[simp] theorem dtEval_leaf {n : Nat} (a : Assignment n) (b : Bool) :
    dtEval a (DTree.leaf b) = b := rfl

@[simp] theorem dtEval_node {n : Nat} (a : Assignment n)
    (v : Fin n) (t0 t1 : DTree n) :
    dtEval a (DTree.node v t0 t1) = (if a v then dtEval a t1 else dtEval a t0) :=
  rfl

/-! ## 3. Decision-tree depth -/

/--
The depth of a decision tree: a leaf has depth `0`; a `node` is one deeper than
its deepest subtree.
-/
def dtDepth {n : Nat} : DTree n → Nat
  | .leaf _ => 0
  | .node _ t0 t1 => 1 + max (dtDepth t0) (dtDepth t1)

@[simp] theorem dtDepth_leaf {n : Nat} (b : Bool) :
    dtDepth (DTree.leaf b : DTree n) = 0 := rfl

@[simp] theorem dtDepth_node {n : Nat} (v : Fin n) (t0 t1 : DTree n) :
    dtDepth (DTree.node v t0 t1) = 1 + max (dtDepth t0) (dtDepth t1) := rfl

/-! ## 4. THE DELIVERABLE — equivalence with the formula model

A decision tree computes an OR (over root-to-leaf branches) of an AND (of the
literals along each branch).  We realise this directly by recursion: at a `node`
on variable `v` we guard the `false`-subtree's formula by the negative literal
`⟨v, false⟩` and the `true`-subtree's formula by the positive literal
`⟨v, true⟩`, and `or` the two guarded conjunctions.
-/

/--
Convert a decision tree to a bounded-depth formula computing the **same** Boolean
function.  A `leaf` becomes the matching constant; a `node v t0 t1` becomes

`or [ and [lit ⟨v,false⟩, treeToFormula t0],
      and [lit ⟨v,true⟩,  treeToFormula t1] ]`.
-/
def treeToFormula {n : Nat} : DTree n → BDFormula n
  | .leaf true  => BDFormula.tru
  | .leaf false => BDFormula.fls
  | .node v t0 t1 =>
      BDFormula.or
        [ BDFormula.and [BDFormula.lit ⟨v, false⟩, treeToFormula t0]
        , BDFormula.and [BDFormula.lit ⟨v, true⟩,  treeToFormula t1] ]

/--
**The load-bearing faithfulness theorem.** The formula produced by
`treeToFormula` computes exactly the decision tree's Boolean function: for every
assignment `a` and tree `t`, `eval a (treeToFormula t) = dtEval a t`.  This is the
genuine, unweakened `eval = dtEval` equivalence.
-/
theorem eval_treeToFormula {n : Nat} (a : Assignment n) (t : DTree n) :
    eval a (treeToFormula t) = dtEval a t := by
  induction t with
  | leaf b =>
      cases b with
      | true  => simp only [treeToFormula, eval_tru, dtEval_leaf]
      | false => simp only [treeToFormula, eval_fls, dtEval_leaf]
  | node v t0 t1 ih0 ih1 =>
      -- Unfold the OR-of-ANDs and the two literal guards.
      rw [treeToFormula]
      rw [eval_or]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [eval_and, eval_and]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rw [eval_lit, eval_lit, ih0, ih1]
      -- Goal: (litEval a ⟨v,false⟩ && dtEval a t0) || (litEval a ⟨v,true⟩ && dtEval a t1)
      --       = if a v then dtEval a t1 else dtEval a t0
      rw [dtEval_node]
      cases hv : a v with
      | true  => simp [litEval, hv]
      | false => simp [litEval, hv]

/-! ## 5. Depth bound

The construction adds, per tree level, an `or` gate over `and` gates over
literal/subformula children — i.e. two formula levels per tree level, plus one
for the leaf constants in the worst case.  This yields the clean linear bound
`depth (treeToFormula t) ≤ 2 * dtDepth t + 1`.

We first record how `depth` reduces on the concrete one- and two-element gate
lists that the construction produces, so the bound proof never has to unfold the
`attach`/`foldr` machinery by hand.
-/

/-- Depth of a literal is `0` (it is a leaf gate). -/
theorem depth_lit {n : Nat} (l : Literal n) :
    depth (BDFormula.lit l) = 0 := by simp only [depth]

/-- Depth of a two-element `and` whose first child is a literal: one more than the
depth of the second child. -/
theorem depth_and_lit_pair {n : Nat} (l : Literal n) (g : BDFormula n) :
    depth (BDFormula.and [BDFormula.lit l, g]) = 1 + depth g := by
  -- `depth (and xs) = 1 + (xs.attach.map (depth ∘ .1)).foldr Nat.max 0`.
  rw [show depth (BDFormula.and [BDFormula.lit l, g])
        = 1 + ([BDFormula.lit l, g].attach.map
                (fun f => depth f.1)).foldr Nat.max 0 from by rw [depth]]
  rw [List.attach_map_val [BDFormula.lit l, g] (fun f => depth f)]
  simp [depth_lit]

/-- Depth of the two-element `or` produced at a `node`. -/
theorem depth_or_pair {n : Nat} (g0 g1 : BDFormula n) :
    depth (BDFormula.or [g0, g1]) = 1 + max (depth g0) (depth g1) := by
  rw [show depth (BDFormula.or [g0, g1])
        = 1 + ([g0, g1].attach.map
                (fun f => depth f.1)).foldr Nat.max 0 from by rw [depth]]
  rw [List.attach_map_val [g0, g1] (fun f => depth f)]
  simp [Nat.max_comm]

/--
**Depth bound.** The converted formula has depth at most `2 * dtDepth t + 1`, so
it is bounded-depth in the tree depth (the property a switching lemma needs of
the target representation).
-/
theorem depth_treeToFormula_le {n : Nat} (t : DTree n) :
    depth (treeToFormula t) ≤ 2 * dtDepth t + 1 := by
  induction t with
  | leaf b =>
      cases b with
      | true  => simp [treeToFormula, depth]
      | false => simp [treeToFormula, depth]
  | node v t0 t1 ih0 ih1 =>
      -- depth (or [ and [lit, f0], and [lit, f1] ])
      --   = 1 + max (1 + depth f0) (1 + depth f1)
      have hor : depth (treeToFormula (DTree.node v t0 t1))
          = 1 + max (1 + depth (treeToFormula t0))
                    (1 + depth (treeToFormula t1)) := by
        rw [treeToFormula, depth_or_pair,
            depth_and_lit_pair, depth_and_lit_pair]
      rw [hor, dtDepth_node]
      omega
