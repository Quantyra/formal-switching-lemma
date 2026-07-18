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

/-! ## Stage B: PHP-shaped terms and pair status -/

/-- A matching term: positive pigeon-to-hole demands. -/
abbrev MTerm (p h : Nat) : Type :=
  List (Fin p × Fin h)

/-- A matching DNF: a list of matching terms, walked in list order. -/
abbrev MDNF (p h : Nat) : Type :=
  List (MTerm p h)

/-- Boolean duplicate detector (component of the legality gate). -/
def hasDupB {alpha : Type} [BEq alpha] : List alpha → Bool
  | [] => false
  | x :: xs => xs.contains x || hasDupB xs

/-- The self-collision gate (pin 2.5): a term is matching-legal when, after
removing duplicate entries, no pigeon repeats and no hole repeats — i.e.
the term's pair **set** is a partial matching. Duplicate copies of one pair
are tolerated (they mirror the boolean duplicate-literal case and are
semantically inert); genuinely colliding terms (one pigeon demanding two
holes, or two pigeons demanding one hole) are never entered by the walk,
and `illegal_term_unsat` below proves the convention semantically honest:
such terms are unsatisfiable by any hole-injective matching. -/
def termMatchingLegalB {p h : Nat} (t : MTerm p h) : Bool :=
  !hasDupB (t.dedup.map Prod.fst) && !hasDupB (t.dedup.map Prod.snd)

/-- The pair is satisfied: the pigeon sits in the demanded hole. -/
def pairSatB {p h : Nat} (mu : MatchingMap p h) (e : Fin p × Fin h) : Bool :=
  mu e.1 == some e.2

/-- The pair is falsified: the pigeon sits elsewhere, or the pigeon is free
while the demanded hole is already used — the latter is the **hole-side
falsification channel** (pin 2.4): hole-stealing is detected through GA-1's
`holeUsed`, with no hole queries. -/
def pairFalsB {p h : Nat} (mu : MatchingMap p h) (e : Fin p × Fin h) : Bool :=
  match mu e.1 with
  | some b => b != e.2
  | none => holeUsed mu e.2

/-- The pair is unresolved: pigeon free and demanded hole free. -/
def pairUnresolvedB {p h : Nat} (mu : MatchingMap p h)
    (e : Fin p × Fin h) : Bool :=
  (mu e.1 == none) && !holeUsed mu e.2

/-- Pair trichotomy: every pair is satisfied, falsified, or unresolved. -/
theorem pair_status_trichotomy {p h : Nat} (mu : MatchingMap p h)
    (e : Fin p × Fin h) :
    (pairSatB mu e || pairFalsB mu e || pairUnresolvedB mu e) = true := by
  unfold pairSatB pairFalsB pairUnresolvedB
  cases hmu : mu e.1 with
  | some b =>
      simp only [hmu]
      cases hbe : b == e.2 with
      | true =>
          have hsome : (some b == some e.2) = true := by
            simpa using hbe
          simp [hsome]
      | false =>
          have hne : (b != e.2) = true := by
            simp [bne, hbe]
          simp [hne]
  | none =>
      simp only [hmu]
      cases hu : holeUsed mu e.2 <;> simp [hu]

/-- Term falsified: some pair is falsified. -/
def termFalsifiedB {p h : Nat} (mu : MatchingMap p h) (t : MTerm p h) : Bool :=
  t.any (pairFalsB mu)

/-- Term satisfied: every pair is satisfied. -/
def termSatisfiedB {p h : Nat} (mu : MatchingMap p h) (t : MTerm p h) : Bool :=
  t.all (pairSatB mu)

/-- The first unresolved pair — the pigeon the canonical walk queries. -/
def firstUnresolvedPair {p h : Nat} (mu : MatchingMap p h) (t : MTerm p h) :
    Option (Fin p × Fin h) :=
  t.find? (pairUnresolvedB mu)

/-- The hole-side falsification statement (pin 2.4), term level: a term
containing a free-pigeon pair whose demanded hole is stolen is falsified —
no hole query occurs anywhere in the walk. -/
theorem termFalsified_of_stolen_hole {p h : Nat} (mu : MatchingMap p h)
    (t : MTerm p h) (e : Fin p × Fin h) (he : e ∈ t)
    (hfree : mu e.1 = none) (hstolen : holeUsed mu e.2 = true) :
    termFalsifiedB mu t = true := by
  unfold termFalsifiedB
  rw [List.any_eq_true]
  refine ⟨e, he, ?_⟩
  unfold pairFalsB
  rw [hfree]
  exact hstolen

/-- Duplicate under a map on a duplicate-free list yields two distinct
elements with equal images. -/
theorem exists_distinct_of_hasDupB_map {alpha beta : Type} [BEq beta]
    [LawfulBEq beta] (f : alpha → beta) :
    ∀ (l : List alpha), l.Nodup → hasDupB (l.map f) = true →
      ∃ x ∈ l, ∃ y ∈ l, x ≠ y ∧ f x = f y
  | [], _, hdup => by
      cases hdup
  | x :: xs, hnd, hdup => by
      unfold hasDupB at hdup
      rw [List.map_cons] at hdup
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
      rw [Bool.or_eq_true] at hdup
      cases hdup with
      | inl hcont =>
          have hmem : f x ∈ xs.map f := by
            simpa using hcont
          rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
          refine ⟨x, List.mem_cons_self x xs, y, List.mem_cons_of_mem x hy,
            ?_, hfy.symm⟩
          intro hxy
          rw [hxy] at hx
          exact hx hy
      | inr hrec =>
          rcases exists_distinct_of_hasDupB_map f xs hnd' hrec with
            ⟨a, ha, b, hb, hab, hfab⟩
          exact ⟨a, List.mem_cons_of_mem x ha, b, List.mem_cons_of_mem x hb,
            hab, hfab⟩

/-- Pin 2.5, semantic justification: a matching-illegal term is
unsatisfiable by **any** hole-injective matching — the walk's skip
convention never hides a satisfiable term. -/
theorem illegal_term_unsat {p h : Nat} {nu : MatchingMap p h}
    (hnu : IsMatching nu) (t : MTerm p h)
    (hbad : termMatchingLegalB t = false) :
    termSatisfiedB nu t = false := by
  unfold termMatchingLegalB at hbad
  rw [Bool.and_eq_false_iff] at hbad
  cases hsat : termSatisfiedB nu t with
  | false => rfl
  | true =>
      exfalso
      unfold termSatisfiedB at hsat
      rw [List.all_eq_true] at hsat
      have hsat' : ∀ e ∈ t, nu e.1 = some e.2 := by
        intro e he
        have hp := hsat e he
        unfold pairSatB at hp
        simpa using hp
      have hndd : t.dedup.Nodup := List.nodup_dedup t
      cases hbad with
      | inl hfst =>
          have hfst' : hasDupB (t.dedup.map Prod.fst) = true := by
            cases hf : hasDupB (t.dedup.map Prod.fst) with
            | true => rfl
            | false =>
                rw [hf] at hfst
                simp at hfst
          rcases exists_distinct_of_hasDupB_map Prod.fst t.dedup hndd hfst'
            with ⟨x, hx, y, hy, hxy, hfxy⟩
          have hxs : nu x.1 = some x.2 := hsat' x (List.mem_dedup.mp hx)
          have hys : nu y.1 = some y.2 := hsat' y (List.mem_dedup.mp hy)
          rw [hfxy] at hxs
          rw [hys] at hxs
          have hsnd : y.2 = x.2 := by
            simpa using hxs
          apply hxy
          exact Prod.ext hfxy hsnd.symm
      | inr hsnd =>
          have hsnd' : hasDupB (t.dedup.map Prod.snd) = true := by
            cases hf : hasDupB (t.dedup.map Prod.snd) with
            | true => rfl
            | false =>
                rw [hf] at hsnd
                simp at hsnd
          rcases exists_distinct_of_hasDupB_map Prod.snd t.dedup hndd hsnd'
            with ⟨x, hx, y, hy, hxy, hfxy⟩
          have hxs : nu x.1 = some x.2 := hsat' x (List.mem_dedup.mp hx)
          have hys : nu y.1 = some y.2 := hsat' y (List.mem_dedup.mp hy)
          rw [hfxy] at hxs
          have hfst : x.1 = y.1 := hnu x.1 y.1 y.2 hxs hys
          apply hxy
          exact Prod.ext hfst hfxy

/-- A term neither satisfied nor falsified has an unresolved pair, so the
walk never reaches its dead query arm. -/
theorem firstUnresolvedPair_isSome_of_undetermined {p h : Nat}
    (mu : MatchingMap p h) (t : MTerm p h)
    (hsat : termSatisfiedB mu t = false)
    (hfals : termFalsifiedB mu t = false) :
    (firstUnresolvedPair mu t).isSome = true := by
  unfold termSatisfiedB at hsat
  unfold termFalsifiedB at hfals
  rw [List.all_eq_false] at hsat
  rcases hsat with ⟨e, he, hesat⟩
  have hefals : pairFalsB mu e = false := by
    cases hef : pairFalsB mu e with
    | false => rfl
    | true =>
        have hany : t.any (pairFalsB mu) = true :=
          List.any_eq_true.mpr ⟨e, he, hef⟩
        rw [hfals] at hany
        cases hany
  have heunres : pairUnresolvedB mu e = true := by
    have htri := pair_status_trichotomy mu e
    have hns : pairSatB mu e = false := by
      cases hps : pairSatB mu e with
      | false => rfl
      | true => exact absurd hps (by simpa using hesat)
    rw [hns, hefals] at htri
    simpa using htri
  unfold firstUnresolvedPair
  rw [List.find?_isSome]
  exact ⟨e, he, heunres⟩

/-! ## Stage B: the canonical walk -/

/-- The one-pigeon extension the walk composes at a query. -/
def singleMatching {p h : Nat} (i : Fin p) (a : Fin h) : MatchingMap p h :=
  fun j => if j = i then some a else none

theorem singleMatching_self {p h : Nat} (i : Fin p) (a : Fin h) :
    singleMatching i a i = some a := by
  unfold singleMatching
  simp

/-- Querying an unresolved pair is a disjoint extension: the queried pigeon
is free and the answered hole is free, so the GA-1 composition laws apply
verbatim (`IsMatching` transfer, star drop, restriction homomorphism). -/
theorem disjointExtension_singleMatching {p h : Nat} (mu : MatchingMap p h)
    (i : Fin p) (a : Fin h) (hfree : mu i = none)
    (hhole : holeUsed mu a = false) :
    DisjointExtension mu (singleMatching i a) := by
  constructor
  · intro j b hj
    unfold singleMatching
    by_cases hji : j = i
    · rw [hji] at hj
      rw [hj] at hfree
      cases hfree
    · simp [hji]
  · intro j k b hj hk
    unfold singleMatching at hk
    by_cases hki : k = i
    · simp [hki] at hk
      rw [← hk] at hj
      have hused : holeUsed mu a = true :=
        (holeUsed_eq_true_iff mu a).mpr ⟨j, hj⟩
      rw [hhole] at hused
      cases hused
    · simp [hki] at hk

/-- The canonical matching walk. Terms are processed in list order:
matching-illegal terms are skipped unentered (pin 2.5); falsified terms are
skipped; a satisfied legal term stops with `true`; otherwise the first
unresolved pair's **pigeon** is queried, used-hole branches are dead
leaves, and each free-hole branch re-examines the same term under the
disjointly extended matching. Fuel bounds the query budget; the canonical
entry supplies the free-pigeon count. -/
def mwalk {p h : Nat} : Nat → MatchingMap p h → MDNF p h → MDTree p h
  | _, _, [] => .leaf false
  | fuel, mu, t :: rest =>
      if termMatchingLegalB t = false then mwalk fuel mu rest
      else if termFalsifiedB mu t = true then mwalk fuel mu rest
      else if termSatisfiedB mu t = true then .leaf true
      else
        match fuel with
        | 0 => .leaf false
        | fuel' + 1 =>
            match firstUnresolvedPair mu t with
            | none => .leaf false
            | some e =>
                .query e.1 (fun a =>
                  if holeUsed mu a = true then .leaf false
                  else mwalk fuel' (compose mu (singleMatching e.1 a))
                    (t :: rest))
  termination_by fuel _ D => (fuel, D.length)

/-- The canonical entry: fuel is the free-pigeon count of the base
matching. -/
def canonicalMDT {p h : Nat} (D : MDNF p h) (mu : MatchingMap p h) :
    MDTree p h :=
  mwalk (freePigeons mu).card mu D

/-! ## Stage B: pinned walk laws -/

/-- The empty DNF walks to the `false` leaf. -/
theorem mwalk_nil {p h : Nat} (fuel : Nat) (mu : MatchingMap p h) :
    mwalk fuel mu ([] : MDNF p h) = .leaf false := by
  simp [mwalk]

/-- Pin 2.5, walk level: a matching-illegal term is skipped unentered. -/
theorem mwalk_skip_illegal {p h : Nat} (fuel : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hbad : termMatchingLegalB t = false) :
    mwalk fuel mu (t :: rest) = mwalk fuel mu rest := by
  rw [mwalk.eq_def]
  simp [hbad]

/-- A falsified legal term is skipped. -/
theorem mwalk_skip_falsified {p h : Nat} (fuel : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = true) :
    mwalk fuel mu (t :: rest) = mwalk fuel mu rest := by
  rw [mwalk.eq_def]
  simp [hleg, hfals]

/-- A satisfied legal term stops the walk with `true`. -/
theorem mwalk_stop_satisfied {p h : Nat} (fuel : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = true) :
    mwalk fuel mu (t :: rest) = .leaf true := by
  rw [mwalk.eq_def]
  simp [hleg, hfals, hsat]

/-- With zero fuel an undetermined head term dead-ends. -/
theorem mwalk_zero_undetermined {p h : Nat} (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false) :
    mwalk 0 mu (t :: rest) = .leaf false := by
  rw [mwalk.eq_def]
  simp [hleg, hfals, hsat]

/-- The query step: on an undetermined legal head term with fuel, the walk
queries the first unresolved pair's pigeon; used-hole branches are dead
leaves; free-hole branches re-examine the same term under the disjointly
extended matching. -/
theorem mwalk_query_step {p h : Nat} (fuel' : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h) (e : Fin p × Fin h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (hfu : firstUnresolvedPair mu t = some e) :
    mwalk (fuel' + 1) mu (t :: rest) =
      .query e.1 (fun a =>
        if holeUsed mu a = true then .leaf false
        else mwalk fuel' (compose mu (singleMatching e.1 a)) (t :: rest)) := by
  rw [mwalk.eq_def]
  simp [hleg, hfals, hsat, hfu]

/-- The dead query arm (no unresolved pair) — provably unreachable for
undetermined terms by `firstUnresolvedPair_isSome_of_undetermined`. -/
theorem mwalk_query_none {p h : Nat} (fuel' : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (hfu : firstUnresolvedPair mu t = none) :
    mwalk (fuel' + 1) mu (t :: rest) = .leaf false := by
  rw [mwalk.eq_def]
  simp [hleg, hfals, hsat, hfu]

/-- Pin 2.6, fuel form: the walk's depth never exceeds its fuel. -/
theorem mdtDepth_mwalk_le_fuel {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (D : MDNF p h),
      mdtDepth (mwalk fuel mu D) ≤ fuel
  | fuel, mu, [] => by
      rw [mwalk_nil]
      exact Nat.zero_le fuel
  | fuel, mu, t :: rest => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [mwalk_skip_falsified fuel mu t rest hleg hfals]
          exact mdtDepth_mwalk_le_fuel fuel mu rest
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [mwalk_stop_satisfied fuel mu t rest hleg hfals' hsat]
            exact Nat.zero_le fuel
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [mwalk_zero_undetermined mu t rest hleg hfals' hsat']
                exact Nat.le_refl 0
            | succ fuel' =>
                cases hfu : firstUnresolvedPair mu t with
                | none =>
                    rw [mwalk_query_none fuel' mu t rest hleg hfals' hsat' hfu]
                    exact Nat.zero_le _
                | some e =>
                    rw [mwalk_query_step fuel' mu t rest e hleg hfals' hsat' hfu]
                    rw [mdtDepth_query, Nat.add_comm]
                    apply Nat.add_le_add_right
                    apply Finset.sup_le
                    intro a _
                    by_cases hha : holeUsed mu a = true
                    · rw [if_pos hha]
                      exact Nat.zero_le fuel'
                    · rw [if_neg hha]
                      exact mdtDepth_mwalk_le_fuel fuel'
                        (compose mu (singleMatching e.1 a)) (t :: rest)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [mwalk_skip_illegal fuel mu t rest hleg']
        exact mdtDepth_mwalk_le_fuel fuel mu rest
  termination_by fuel _ D => (fuel, D.length)

/-- Pin 2.6, canonical form: the canonical matching-DT's depth is at most
the base matching's free-pigeon count. -/
theorem mdtDepth_canonicalMDT_le_freePigeons {p h : Nat} (D : MDNF p h)
    (mu : MatchingMap p h) :
    mdtDepth (canonicalMDT D mu) ≤ (freePigeons mu).card :=
  mdtDepth_mwalk_le_fuel (freePigeons mu).card mu D

/-! ## Stage C: the honest space and the deep-path bad set -/

instance instFintypeMatchingMap (p h : Nat) : Fintype (MatchingMap p h) :=
  inferInstanceAs (Fintype (Fin p → Option (Fin h)))

instance instDecidableEqMatchingMap (p h : Nat) :
    DecidableEq (MatchingMap p h) :=
  inferInstanceAs (DecidableEq (Fin p → Option (Fin h)))

instance instDecidableIsMatching {p h : Nat} (mu : MatchingMap p h) :
    Decidable (IsMatching mu) :=
  inferInstanceAs (Decidable (∀ i j a, mu i = some a → mu j = some a → i = j))

/-- The honest partial-matching space `M_ℓ`: hole-injective maps with
exactly `ℓ` free pigeons. Rectangular signature. -/
def honestMatchingSpace (p h ell : Nat) : Finset (MatchingMap p h) :=
  Finset.univ.filter
    (fun mu => IsMatching mu ∧ (freePigeons mu).card = ell)

theorem mem_honestMatchingSpace {p h ell : Nat} (mu : MatchingMap p h) :
    mu ∈ honestMatchingSpace p h ell ↔
      IsMatching mu ∧ (freePigeons mu).card = ell := by
  unfold honestMatchingSpace
  simp

/-- The deep-path bad set: honest matchings with `ℓ` free pigeons whose
canonical matching-DT for `D` is deeper than `s`. -/
def badMatchings {p h : Nat} (D : MDNF p h) (s ell : Nat) :
    Finset (MatchingMap p h) :=
  (honestMatchingSpace p h ell).filter
    (fun mu => s < mdtDepth (canonicalMDT D mu))

theorem mem_badMatchings {p h : Nat} (D : MDNF p h) (s ell : Nat)
    (mu : MatchingMap p h) :
    mu ∈ badMatchings D s ell ↔
      (IsMatching mu ∧ (freePigeons mu).card = ell) ∧
        s < mdtDepth (canonicalMDT D mu) := by
  unfold badMatchings
  rw [Finset.mem_filter, mem_honestMatchingSpace]

/-! ## Stage C: definitional non-vacuity (pin 2.2)

The walk is WF-compiled, so kernel evaluation cannot unfold it; the member
is computed through the Stage B equation lemmas instead — exactly the
discipline the equation-lemma family exists for. -/

/-- The pin 2.2 concrete instance: one pigeon, one hole, the single-pair
term, the empty base matching (one free pigeon). -/
def nvD : MDNF 1 1 :=
  [[(⟨0, by decide⟩, ⟨0, by decide⟩)]]

theorem nv_freePigeons_card :
    (freePigeons (emptyMatching 1 1)).card = 1 := by
  decide

theorem nv_canonicalMDT_depth_pos :
    0 < mdtDepth (canonicalMDT nvD (emptyMatching 1 1)) := by
  have hstep := mwalk_query_step (p := 1) (h := 1) 0 (emptyMatching 1 1)
    [(⟨0, by decide⟩, ⟨0, by decide⟩)] [] (⟨0, by decide⟩, ⟨0, by decide⟩)
    (by decide) (by decide) (by decide) (by decide)
  have hcan : canonicalMDT nvD (emptyMatching 1 1) =
      mwalk (0 + 1) (emptyMatching 1 1)
        [[((⟨0, by decide⟩ : Fin 1), (⟨0, by decide⟩ : Fin 1))]] := by
    unfold canonicalMDT
    rw [nv_freePigeons_card]
    rfl
  rw [hcan, hstep, mdtDepth_query]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)

/-- Pin 2.2: the deep-path bad set is definitionally non-vacuous — a
concrete `D`, `ℓ` with a concrete member. -/
theorem badMatchings_nonvacuity :
    emptyMatching 1 1 ∈ badMatchings nvD 0 1 := by
  rw [mem_badMatchings]
  exact ⟨⟨isMatching_empty 1 1, nv_freePigeons_card⟩,
    nv_canonicalMDT_depth_pos⟩

theorem badMatchings_nonempty :
    (badMatchings nvD 0 1).Nonempty :=
  ⟨emptyMatching 1 1, badMatchings_nonvacuity⟩

/-! ## Stage C: falsification stability (the pin 2.3 seed)

The hole-side falsification channel is stable under matching-respecting
extensions: once a pair is falsified relative to `mu`, no hole-injective
extension of `mu` can satisfy it. This is the load-bearing ingredient of
the evaluation-soundness induction. -/

/-- A falsified pair is never satisfied by a hole-injective extension. -/
theorem pairFals_stable {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) (hnu : IsMatching nu)
    (e : Fin p × Fin h) (hfals : pairFalsB mu e = true) :
    pairSatB nu e = false := by
  unfold pairFalsB at hfals
  unfold pairSatB
  cases hmu : mu e.1 with
  | some b =>
      rw [hmu] at hfals
      have hnub : nu e.1 = some b := hag e.1 b hmu
      rw [hnub]
      have hbne : (b == e.2) = false := by
        cases hbe : b == e.2 with
        | false => rfl
        | true =>
            exfalso
            have hnot : (!(b == e.2)) = true := hfals
            rw [hbe] at hnot
            simp at hnot
      simp [hbne]
  | none =>
      rw [hmu] at hfals
      rcases (holeUsed_eq_true_iff mu e.2).mp hfals with ⟨j, hj⟩
      have hnuj : nu j = some e.2 := hag j e.2 hj
      cases hnue : nu e.1 with
      | none => simp
      | some c =>
          cases hce : c == e.2 with
          | false => simp [hnue, hce]
          | true =>
              exfalso
              have hc : c = e.2 := by simpa using hce
              rw [hc] at hnue
              have hij : e.1 = j := hnu e.1 j e.2 hnue hnuj
              rw [hij] at hmu
              rw [hj] at hmu
              cases hmu

/-- A falsified term is never satisfied by a hole-injective extension. -/
theorem termFals_stable {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) (hnu : IsMatching nu)
    (t : MTerm p h) (hfals : termFalsifiedB mu t = true) :
    termSatisfiedB nu t = false := by
  unfold termFalsifiedB at hfals
  unfold termSatisfiedB
  rw [List.any_eq_true] at hfals
  rcases hfals with ⟨e, he, hef⟩
  rw [List.all_eq_false]
  exact ⟨e, he, by rw [pairFals_stable hag hnu e hef]; simp⟩

end PHPMatchingCanonicalMDT
end PvNP
