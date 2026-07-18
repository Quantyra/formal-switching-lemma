import PvNP.PHPMatchingComposition

/-!
# GA-2 Stage A: matching decision trees, evaluation, and agreement (S2186)

Second formal rung of the Gate A rung-4 reopening arc (S2184 packet, GA-2),
Stage A of the pre-registered staged plan: the tree object the canonical
matching walk (Stage B) will build and the extension encode (GA-3) will
count.

* `MDTree p h` — matching decision trees: leaves carry Booleans; a query
  node names a **pigeon** and carries one subtree per hole. Queries are
  pigeon-only (the packet-disclosed deviation from classical vertex-query
  MDTs); the type is total over holes — the canonical walk of Stage B never
  enters used holes, which the Stage B depth-cap and soundness lemmas make
  precise.
* `mdtEval` — evaluation against a GA-1 `MatchingMap`: partial (returns
  `none` exactly when the tree queries a free pigeon), total on any map
  defined on every queried pigeon.
* `MAgree` — the matching-side mirror of the boolean `Agree`: every
  assignment of the first map survives into the second.
* Evaluation is `MAgree`-monotone (`mdtEval_mono_of_mAgree`) — the Stage A
  seed of the packet's evaluation-soundness pin (2.3) — and connects to the
  GA-1 composition algebra: a base matching always `MAgree`s into a
  first-wins composite, and an extension does under pigeon-level
  consistency.
* `mdtDepth` and the query-count view `mdtQueries` with
  `mdtDepth_le_mdtQueries`.

Deterministic matching-DT infrastructure only. This is not a PHP switching
lemma (no collapse-probability bound is stated or proved), not the
canonical walk (Stage B), not the deep-path bad set (Stage C), not the
S2080 bridge or depth-1 recovery (Stage D), not the extension encode
(GA-3), not Gate A closure, not a Frege/PHP or NP/circuit lower bound, and
not P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingCanonicalMDT

open PHPMatchingComposition

/-! ## The tree type -/

/-- Matching decision tree: a leaf carries the answer; a query node names a
pigeon and branches on the hole assigned to it. Pigeon-only queries are the
packet-disclosed deviation from classical vertex-query MDTs. The children
function is total over holes; the Stage B canonical walk never builds paths
into used holes. -/
inductive MDTree (p h : Nat) where
  | leaf (b : Bool)
  | query (i : Fin p) (children : Fin h → MDTree p h)

/-! ## Evaluation and depth -/

/-- Evaluate a matching decision tree against a matching map: querying a
pigeon the map assigns descends into that hole's subtree; querying a free
pigeon is stuck (`none`). Total on any map defined on every queried
pigeon. -/
def mdtEval {p h : Nat} (mu : MatchingMap p h) : MDTree p h → Option Bool
  | .leaf b => some b
  | .query i children =>
      match mu i with
      | some a => mdtEval mu (children a)
      | none => none

theorem mdtEval_leaf {p h : Nat} (mu : MatchingMap p h) (b : Bool) :
    mdtEval mu (.leaf b) = some b := rfl

theorem mdtEval_query_fixed {p h : Nat} (mu : MatchingMap p h) (i : Fin p)
    (children : Fin h → MDTree p h) (a : Fin h) (hi : mu i = some a) :
    mdtEval mu (.query i children) = mdtEval mu (children a) := by
  simp only [mdtEval, hi]

theorem mdtEval_query_free {p h : Nat} (mu : MatchingMap p h) (i : Fin p)
    (children : Fin h → MDTree p h) (hi : mu i = none) :
    mdtEval mu (.query i children) = none := by
  simp only [mdtEval, hi]

/-- Depth: the longest query chain. -/
def mdtDepth {p h : Nat} : MDTree p h → Nat
  | .leaf _ => 0
  | .query _ children => 1 + Finset.univ.sup (fun a => mdtDepth (children a))

theorem mdtDepth_leaf {p h : Nat} (b : Bool) :
    mdtDepth (.leaf b : MDTree p h) = 0 := rfl

theorem mdtDepth_query {p h : Nat} (i : Fin p)
    (children : Fin h → MDTree p h) :
    mdtDepth (.query i children) =
      1 + Finset.univ.sup (fun a => mdtDepth (children a)) := rfl

/-- Total query count: a crude size measure dominating the depth. -/
def mdtQueries {p h : Nat} : MDTree p h → Nat
  | .leaf _ => 0
  | .query _ children =>
      1 + Finset.univ.sup (fun a => mdtQueries (children a))

theorem mdtDepth_le_mdtQueries {p h : Nat} :
    ∀ T : MDTree p h, mdtDepth T ≤ mdtQueries T
  | .leaf _ => Nat.le_refl 0
  | .query i children => by
      unfold mdtDepth mdtQueries
      apply Nat.add_le_add_left
      apply Finset.sup_le
      intro a _
      exact Finset.le_sup_of_le (Finset.mem_univ a)
        (mdtDepth_le_mdtQueries (children a))

/-! ## Agreement (the boolean `Agree` mirror) -/

/-- The matching-side mirror of the boolean `Agree`: every assignment of
the first map survives into the second (the second map extends the
first). -/
def MAgree {p h : Nat} (mu nu : MatchingMap p h) : Prop :=
  ∀ i a, mu i = some a → nu i = some a

theorem mAgree_refl {p h : Nat} (mu : MatchingMap p h) : MAgree mu mu :=
  fun _ _ hi => hi

theorem mAgree_trans {p h : Nat} {mu nu xi : MatchingMap p h}
    (h01 : MAgree mu nu) (h12 : MAgree nu xi) : MAgree mu xi :=
  fun i a hi => h12 i a (h01 i a hi)

theorem mAgree_empty {p h : Nat} (mu : MatchingMap p h) :
    MAgree (emptyMatching p h) mu := by
  intro i a hi
  cases hi

/-- The base matching always agrees into a first-wins composite (its
assignments survive verbatim) — the matching-side `agree_compose_left`. -/
theorem mAgree_compose_left {p h : Nat} (mu0 mu1 : MatchingMap p h) :
    MAgree mu0 (compose mu0 mu1) :=
  fun i a hi => compose_fixed_left mu0 mu1 i a hi

/-- The extension agrees into the composite under pigeon-level consistency
— the matching-side `agree_compose_right`, via the GA-1 transfer lemma. -/
theorem mAgree_compose_right {p h : Nat} {mu0 mu1 : MatchingMap p h}
    (hcons : MatchingConsistentWith mu0 mu1) :
    MAgree mu1 (compose mu0 mu1) :=
  fun i a hi => matchingConsistentWith_compose_right hcons i a hi

/-- A disjoint extension agrees into the composite (special case of the
consistency route, matching the GA-3 intended usage). -/
theorem mAgree_compose_right_of_disjointExtension {p h : Nat}
    {mu0 mu1 : MatchingMap p h} (hd : DisjointExtension mu0 mu1) :
    MAgree mu1 (compose mu0 mu1) :=
  mAgree_compose_right (disjointExtension_matchingConsistentWith hd)

/-! ## Evaluation is agreement-monotone (Stage A seed of pin 2.3) -/

/-- A determined evaluation survives into any extension of the matching:
if the tree evaluates on `mu`, every `MAgree`-larger map evaluates to the
same answer. -/
theorem mdtEval_mono_of_mAgree {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) :
    ∀ (T : MDTree p h) (b : Bool), mdtEval mu T = some b → mdtEval nu T = some b
  | .leaf c, b, hb => hb
  | .query i children, b, hb => by
      cases hmu : mu i with
      | none =>
          rw [mdtEval_query_free mu i children hmu] at hb
          cases hb
      | some a =>
          rw [mdtEval_query_fixed mu i children a hmu] at hb
          rw [mdtEval_query_fixed nu i children a (hag i a hmu)]
          exact mdtEval_mono_of_mAgree hag (children a) b hb

/-- Consequently a composite evaluates everything its base determines. -/
theorem mdtEval_compose_of_base {p h : Nat} (mu0 mu1 : MatchingMap p h)
    (T : MDTree p h) (b : Bool) (hb : mdtEval mu0 T = some b) :
    mdtEval (compose mu0 mu1) T = some b :=
  mdtEval_mono_of_mAgree (mAgree_compose_left mu0 mu1) T b hb

/-! ## Stage A witnesses (rectangular-ready; square exercised) -/

/-- A depth-2 tree over the square 3×3 shape: query pigeon 0; on hole 0
query pigeon 1, else answer false. -/
def mdtWitnessSq : MDTree 3 3 :=
  .query ⟨0, by decide⟩ (fun a =>
    if a = (⟨0, by decide⟩ : Fin 3) then
      .query ⟨1, by decide⟩ (fun _ => .leaf true)
    else
      .leaf false)

theorem mdtWitnessSq_depth : mdtDepth mdtWitnessSq = 2 := by
  decide

/-- Evaluation against the GA-1 square witness composite: pigeon 0 ↦ hole
0, pigeon 1 ↦ hole 1, so the walk reaches the deep leaf. -/
theorem mdtWitnessSq_eval :
    mdtEval (compose sqFst sqSnd) mdtWitnessSq = some true := by
  decide

/-- The base alone is stuck (pigeon 1 free): evaluation is genuinely
partial, and the composite genuinely extends it. -/
theorem mdtWitnessSq_eval_base_stuck :
    mdtEval sqFst mdtWitnessSq = none := by
  decide

/-- Rectangular instance (3 pigeons, 2 holes): the same tree shape stated
rectangularly, evaluated on the GA-1 rectangular composite. -/
def mdtWitnessRect : MDTree 3 2 :=
  .query ⟨0, by decide⟩ (fun a =>
    if a = (⟨0, by decide⟩ : Fin 2) then
      .query ⟨2, by decide⟩ (fun _ => .leaf true)
    else
      .leaf false)

theorem mdtWitnessRect_eval :
    mdtEval (compose rectFst rectSnd) mdtWitnessRect = some true := by
  decide

end PHPMatchingCanonicalMDT
end PvNP
