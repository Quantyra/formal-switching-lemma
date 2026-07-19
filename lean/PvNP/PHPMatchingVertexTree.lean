import PvNP.PHPMatchingCanonicalMDT
import Mathlib.Tactic.FinCases

/-!
# GA-3 Stage 0: vertex-query canonical matching decision trees (S2187)

First formal stage of the GA-3 extension-encode rung (S2184 packet routing;
S2187 story; Option A adopted with recorded sign-off per the reviewed GA-3
reference-location memo). The located classical design (Beame §5 /
Urquhart–Fu Lemma 6.2 / PBI §3) consumes **vertex-query** matching decision
trees — non-leaf nodes query a pigeon *or a hole* (UF Def 4.1) — and its
canonical tree enters a term and queries every still-uncovered vertex of
the entered restricted term (UF Def 4.2/4.5) before re-scanning. This
module builds that consumed tree and its GA-2-analogue validation surface:

* `VMDTree p h` — vertex-query trees (`pquery`/`hquery` nodes); partial
  `vmdtEval` against GA-1 `MatchingMap`s (hole queries answered through
  `holeOccupant`); `MAgree`-monotone evaluation on hole-injective
  extensions; the depth measure.
* `vwalkAux`/`canonicalVMDT` — the canonical vertex walk: term scan
  (illegal terms skipped unentered — the GA-2 pin 2.5 gate, verbatim;
  falsified terms skipped; satisfied terms stop `true`), block entry
  freezing the entered restricted term's vertex list, in-block queries of
  the still-uncovered frozen vertices (mid-block falsification does NOT
  abort the block — the UF-faithful behavior the encode's block alignment
  needs), pigeon- and hole-side query nodes with dead used-answer arms,
  fuel = free-pigeon count (each vertex answer consumes one free pigeon
  and one free hole, so the GA-2.6 cap re-derives unchanged in bound).
  Full equation-lemma family (the walk is WF-compiled and does not
  kernel-reduce; the equation lemmas are the pinned evaluation
  discipline).
* Validation pins (S2187 stage 0, per the memo amendment M2): the
  skip-illegal law (pin 2.5 analogue), depth caps in fuel and canonical
  free-pigeon forms (pin 2.6 analogue — new Lean work, pinned not
  asserted), the vertex-tree deep-path bad set `vbadMatchings` with a
  kernel-checked concrete member (pin 2.2 analogue), and the dead entry
  arm's unreachability (`termVertices_ne_nil_of_undetermined`).
* The **kernel-pinned walk-vs-vertex divergence** (memo L5, companion to
  `walk_boolean_depth1_divergence`): on the memo's pinned instance
  (square 3×3, width 1, three terms demanding one hole, empty base
  matching) the GA-2 pigeon-only canonical walk has depth exactly 3 while
  the vertex-query canonical tree has depth exactly 2 — the two trees are
  genuinely different objects, and GA-3's encode counts the deep-path bad
  set of the **vertex** tree (the GA-2 closeout's walk-native
  parenthetical is superseded by the recorded Option A adoption).

Deterministic matching-DT infrastructure only. This is not a PHP switching
lemma (no collapse-probability bound of any kind is stated or proved), not
the extension encode itself (later S2187 stages), not an injectivity or
counting claim (GA-4/GA-5), not Gate A closure, not a Frege/PHP or
NP/circuit lower bound, and not P-versus-NP. GA-2's pigeon-only walk
artifacts stay banked and untouched; the GA-2 discharge of pin 2.4's
falsification-semantics half stands.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingVertexTree

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open RestrictedPHPFloor

/-! ## Vertices and hole occupancy -/

/-- A PHP vertex: a pigeon (`inl`) or a hole (`inr`) — the query alphabet
of the classical matching decision trees (UF Def 4.1). -/
abbrev Vertex (p h : Nat) : Type :=
  Sum (Fin p) (Fin h)

/-- The pigeon occupying a hole, if any: the first pigeon the map sends
there. On hole-injective maps this is the unique occupant. -/
def holeOccupant {p h : Nat} (mu : MatchingMap p h) (b : Fin h) :
    Option (Fin p) :=
  (finList p).find? (fun i => mu i == some b)

theorem mem_finList {p : Nat} (i : Fin p) : i ∈ finList p := by
  unfold finList
  exact List.mem_pmap.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

/-- An occupant returned by `holeOccupant` really occupies the hole. -/
theorem holeOccupant_spec {p h : Nat} {mu : MatchingMap p h} {b : Fin h}
    {q : Fin p} (hq : holeOccupant mu b = some q) : mu q = some b := by
  have hpred := List.find?_some hq
  simpa using hpred

/-- On a hole-injective map, the occupant of an occupied hole is found and
is the occupying pigeon — the evaluation-side uniqueness transfer. -/
theorem holeOccupant_eq_some_of_isMatching {p h : Nat}
    {nu : MatchingMap p h} (hnu : IsMatching nu) {q : Fin p} {b : Fin h}
    (hq : nu q = some b) : holeOccupant nu b = some q := by
  have hsome : (holeOccupant nu b).isSome = true := by
    unfold holeOccupant
    rw [List.find?_isSome]
    exact ⟨q, mem_finList q, by simpa using hq⟩
  rcases Option.isSome_iff_exists.mp hsome with ⟨a, ha⟩
  have haq : nu a = some b := holeOccupant_spec ha
  rw [ha]
  exact congrArg some (hnu a q b haq hq)

/-! ## The vertex-query tree type -/

/-- Vertex-query matching decision tree (UF Def 4.1 mirror): a leaf
carries the answer; a `pquery` node names a pigeon and branches on the
hole assigned to it; an `hquery` node names a hole and branches on the
pigeon occupying it. -/
inductive VMDTree (p h : Nat) where
  | leaf (b : Bool)
  | pquery (i : Fin p) (children : Fin h → VMDTree p h)
  | hquery (j : Fin h) (children : Fin p → VMDTree p h)

/-- Evaluate against a matching map: pigeon queries descend through the
map, hole queries through `holeOccupant`; querying a free pigeon or an
empty hole is stuck (`none`). -/
def vmdtEval {p h : Nat} (mu : MatchingMap p h) : VMDTree p h → Option Bool
  | .leaf b => some b
  | .pquery i children =>
      match mu i with
      | some a => vmdtEval mu (children a)
      | none => none
  | .hquery j children =>
      match holeOccupant mu j with
      | some q => vmdtEval mu (children q)
      | none => none

theorem vmdtEval_leaf {p h : Nat} (mu : MatchingMap p h) (b : Bool) :
    vmdtEval mu (.leaf b) = some b := rfl

theorem vmdtEval_pquery_matched {p h : Nat} (mu : MatchingMap p h)
    (i : Fin p) (children : Fin h → VMDTree p h) (a : Fin h)
    (hi : mu i = some a) :
    vmdtEval mu (.pquery i children) = vmdtEval mu (children a) := by
  simp only [vmdtEval, hi]

theorem vmdtEval_pquery_free {p h : Nat} (mu : MatchingMap p h)
    (i : Fin p) (children : Fin h → VMDTree p h) (hi : mu i = none) :
    vmdtEval mu (.pquery i children) = none := by
  simp only [vmdtEval, hi]

theorem vmdtEval_hquery_occupied {p h : Nat} (mu : MatchingMap p h)
    (j : Fin h) (children : Fin p → VMDTree p h) (q : Fin p)
    (hq : holeOccupant mu j = some q) :
    vmdtEval mu (.hquery j children) = vmdtEval mu (children q) := by
  simp only [vmdtEval, hq]

theorem vmdtEval_hquery_empty {p h : Nat} (mu : MatchingMap p h)
    (j : Fin h) (children : Fin p → VMDTree p h)
    (hq : holeOccupant mu j = none) :
    vmdtEval mu (.hquery j children) = none := by
  simp only [vmdtEval, hq]

/-- Determined evaluations survive into hole-injective `MAgree`
extensions — the vertex-tree mirror of GA-2's agreement-monotone
evaluation. Hole-injectivity of the larger map is genuinely needed on the
hole-query channel (occupant uniqueness); the pigeon channel is
functional as before. -/
theorem vmdtEval_mono_of_isMatching {p h : Nat}
    {mu nu : MatchingMap p h} (hag : MAgree mu nu) (hnu : IsMatching nu) :
    ∀ (T : VMDTree p h) (b : Bool),
      vmdtEval mu T = some b → vmdtEval nu T = some b
  | .leaf _, _, hev => hev
  | .pquery i children, b, hev => by
      cases hi : mu i with
      | none =>
          rw [vmdtEval_pquery_free mu i children hi] at hev
          cases hev
      | some a =>
          rw [vmdtEval_pquery_matched mu i children a hi] at hev
          rw [vmdtEval_pquery_matched nu i children a (hag i a hi)]
          exact vmdtEval_mono_of_isMatching hag hnu (children a) b hev
  | .hquery j children, b, hev => by
      cases hj : holeOccupant mu j with
      | none =>
          rw [vmdtEval_hquery_empty mu j children hj] at hev
          cases hev
      | some q =>
          rw [vmdtEval_hquery_occupied mu j children q hj] at hev
          have hq : mu q = some j := holeOccupant_spec hj
          have hq' : holeOccupant nu j = some q :=
            holeOccupant_eq_some_of_isMatching hnu (hag q j hq)
          rw [vmdtEval_hquery_occupied nu j children q hq']
          exact vmdtEval_mono_of_isMatching hag hnu (children q) b hev

/-- Depth: the longest query chain. -/
def vmdtDepth {p h : Nat} : VMDTree p h → Nat
  | .leaf _ => 0
  | .pquery _ children => 1 + Finset.univ.sup (fun a => vmdtDepth (children a))
  | .hquery _ children => 1 + Finset.univ.sup (fun q => vmdtDepth (children q))

theorem vmdtDepth_leaf {p h : Nat} (b : Bool) :
    vmdtDepth (.leaf b : VMDTree p h) = 0 := rfl

theorem vmdtDepth_pquery {p h : Nat} (i : Fin p)
    (children : Fin h → VMDTree p h) :
    vmdtDepth (.pquery i children) =
      1 + Finset.univ.sup (fun a => vmdtDepth (children a)) := rfl

theorem vmdtDepth_hquery {p h : Nat} (j : Fin h)
    (children : Fin p → VMDTree p h) :
    vmdtDepth (.hquery j children) =
      1 + Finset.univ.sup (fun q => vmdtDepth (children q)) := rfl

/-- A query node is deeper than any one child by at least the query. -/
theorem vmdtDepth_pquery_ge_child {p h : Nat} (i : Fin p)
    (children : Fin h → VMDTree p h) (a : Fin h) :
    1 + vmdtDepth (children a) ≤ vmdtDepth (.pquery i children) := by
  rw [vmdtDepth_pquery]
  exact Nat.add_le_add_left
    (Finset.le_sup (f := fun a => vmdtDepth (children a))
      (Finset.mem_univ a)) 1

theorem vmdtDepth_hquery_ge_child {p h : Nat} (j : Fin h)
    (children : Fin p → VMDTree p h) (q : Fin p) :
    1 + vmdtDepth (children q) ≤ vmdtDepth (.hquery j children) := by
  rw [vmdtDepth_hquery]
  exact Nat.add_le_add_left
    (Finset.le_sup (f := fun q => vmdtDepth (children q))
      (Finset.mem_univ q)) 1

/-- The pigeon-only mirror, for the divergence pin's walk side. -/
theorem mdtDepth_query_ge_child {p h : Nat} (i : Fin p)
    (children : Fin h → MDTree p h) (a : Fin h) :
    1 + mdtDepth (children a) ≤ mdtDepth (.query i children) := by
  rw [mdtDepth_query]
  exact Nat.add_le_add_left
    (Finset.le_sup (f := fun a => mdtDepth (children a))
      (Finset.mem_univ a)) 1

/-! ## The canonical vertex walk -/

/-- A vertex is covered by a matching map: a pigeon when matched, a hole
when occupied (UF's path-matching coverage). -/
def vertexCoveredB {p h : Nat} (mu : MatchingMap p h) : Vertex p h → Bool
  | .inl i => (mu i).isSome
  | .inr b => holeUsed mu b

/-- The entered restricted term's vertex list, frozen at block entry: for
each still-unresolved pair, its pigeon then its demanded hole (UF's
V(C↾ρ); satisfied pairs have dropped out, falsified pairs cannot occur at
entry). -/
def termVertices {p h : Nat} (mu : MatchingMap p h) (t : MTerm p h) :
    List (Vertex p h) :=
  (t.filter (pairUnresolvedB mu)).bind
    (fun e => [Sum.inl e.1, Sum.inr e.2])

/-- An undetermined legal term has a nonempty frozen vertex list — the
dead entry arm is unreachable on the canonical route. -/
theorem termVertices_ne_nil_of_undetermined {p h : Nat}
    (mu : MatchingMap p h) (t : MTerm p h)
    (hsat : termSatisfiedB mu t = false)
    (hfals : termFalsifiedB mu t = false) :
    termVertices mu t ≠ [] := by
  have hfu := firstUnresolvedPair_isSome_of_undetermined mu t hsat hfals
  rcases Option.isSome_iff_exists.mp hfu with ⟨e, he⟩
  have hmem : e ∈ t := List.mem_of_find?_eq_some he
  have hpred : pairUnresolvedB mu e = true := List.find?_some he
  have hin : Sum.inl e.1 ∈ termVertices mu t := by
    unfold termVertices
    refine List.mem_bind.mpr ⟨e, ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hmem, hpred⟩
    · exact List.mem_cons_self _ _
  exact List.ne_nil_of_mem hin

/-- The canonical vertex walk (UF Def 4.5 mirror). State: fuel, the
current path matching, the pending frozen-vertex list of the open block
(empty when scanning), and the DNF. Scanning (`pending = []`): illegal
terms are skipped unentered (the GA-2 pin 2.5 gate), falsified terms are
skipped, a satisfied legal term stops with `true`; an undetermined term is
entered — its restricted vertex list is frozen and its first vertex (a
free pigeon, by unresolvedness) is queried at once. In-block
(`pending = v :: vs`): covered vertices are passed over, uncovered ones
are queried — regardless of the entered term's current status, which is
the UF-faithful block behavior the encode's segment alignment needs. A
pigeon query branches on the answering hole (used holes are dead leaves),
a hole query on the answering pigeon (matched pigeons are dead leaves);
every live answer composes a `DisjointExtension` single-pair matching, so
all GA-1 composition laws apply along every path. At block exhaustion the
scan resumes on the full DNF (the entered term is by then determined). -/
def vwalkAux {p h : Nat} :
    Nat → MatchingMap p h → List (Vertex p h) → MDNF p h → VMDTree p h
  | _, _, [], [] => .leaf false
  | fuel, mu, [], t :: rest =>
      if termMatchingLegalB t = false then vwalkAux fuel mu [] rest
      else if termFalsifiedB mu t = true then vwalkAux fuel mu [] rest
      else if termSatisfiedB mu t = true then .leaf true
      else
        match fuel with
        | 0 => .leaf false
        | fuel' + 1 =>
            match termVertices mu t with
            | [] => .leaf false
            | .inl i :: vs =>
                .pquery i (fun a =>
                  if holeUsed mu a = true then .leaf false
                  else vwalkAux fuel' (compose mu (singleMatching i a)) vs
                    (t :: rest))
            | .inr b :: vs =>
                .hquery b (fun q =>
                  if (mu q).isSome = true then .leaf false
                  else vwalkAux fuel' (compose mu (singleMatching q b)) vs
                    (t :: rest))
  | fuel, mu, v :: vs, D =>
      if vertexCoveredB mu v = true then vwalkAux fuel mu vs D
      else
        match fuel with
        | 0 => .leaf false
        | fuel' + 1 =>
            match v with
            | .inl i =>
                .pquery i (fun a =>
                  if holeUsed mu a = true then .leaf false
                  else vwalkAux fuel' (compose mu (singleMatching i a)) vs D)
            | .inr b =>
                .hquery b (fun q =>
                  if (mu q).isSome = true then .leaf false
                  else vwalkAux fuel' (compose mu (singleMatching q b)) vs D)
  termination_by fuel _ pending D => (fuel, pending.length + D.length)

/-- The canonical entry: no open block, fuel = the free-pigeon count. -/
def canonicalVMDT {p h : Nat} (D : MDNF p h) (mu : MatchingMap p h) :
    VMDTree p h :=
  vwalkAux (freePigeons mu).card mu [] D

/-! ## The equation-lemma family (the walk is WF-compiled) -/

/-- The empty DNF walks to the `false` leaf. -/
theorem vwalk_nil {p h : Nat} (fuel : Nat) (mu : MatchingMap p h) :
    vwalkAux fuel mu [] ([] : MDNF p h) = .leaf false := by
  rw [vwalkAux.eq_def]

/-- Pin 2.5 analogue, vertex-walk level: a matching-illegal term is
skipped unentered — the GA-2 gate verbatim (`illegal_term_unsat` keeps it
semantically honest). -/
theorem vwalk_skip_illegal {p h : Nat} (fuel : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hbad : termMatchingLegalB t = false) :
    vwalkAux fuel mu [] (t :: rest) = vwalkAux fuel mu [] rest := by
  rw [vwalkAux.eq_def]
  simp [hbad]

/-- A falsified legal term is skipped. -/
theorem vwalk_skip_falsified {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = true) :
    vwalkAux fuel mu [] (t :: rest) = vwalkAux fuel mu [] rest := by
  rw [vwalkAux.eq_def]
  simp [hleg, hfals]

/-- A satisfied legal term stops the walk with `true`. -/
theorem vwalk_stop_satisfied {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = true) :
    vwalkAux fuel mu [] (t :: rest) = .leaf true := by
  rw [vwalkAux.eq_def]
  simp [hleg, hfals, hsat]

/-- With zero fuel an undetermined head term dead-ends. -/
theorem vwalk_entry_zero {p h : Nat} (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false) :
    vwalkAux 0 mu [] (t :: rest) = .leaf false := by
  rw [vwalkAux.eq_def]
  simp [hleg, hfals, hsat]

/-- The dead entry arm (empty frozen list) — provably unreachable by
`termVertices_ne_nil_of_undetermined`. -/
theorem vwalk_entry_none {p h : Nat} (fuel' : Nat) (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h)
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = []) :
    vwalkAux (fuel' + 1) mu [] (t :: rest) = .leaf false := by
  rw [vwalkAux.eq_def]
  simp [hleg, hfals, hsat, htv]

/-- Block entry, pigeon-headed frozen list: the entered term's first
frozen vertex (a free pigeon) is queried; the rest of the list becomes the
open block. -/
theorem vwalk_entry_pigeon {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (i : Fin p) (vs : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inl i :: vs) :
    vwalkAux (fuel' + 1) mu [] (t :: rest) =
      .pquery i (fun a =>
        if holeUsed mu a = true then .leaf false
        else vwalkAux fuel' (compose mu (singleMatching i a)) vs
          (t :: rest)) := by
  rw [vwalkAux.eq_def]
  simp [hleg, hfals, hsat, htv]

/-- Block entry, hole-headed frozen list (not produced by the canonical
pigeon-first freeze, but the walk is total over frozen lists). -/
theorem vwalk_entry_hole {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (b : Fin h) (vs : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inr b :: vs) :
    vwalkAux (fuel' + 1) mu [] (t :: rest) =
      .hquery b (fun q =>
        if (mu q).isSome = true then .leaf false
        else vwalkAux fuel' (compose mu (singleMatching q b)) vs
          (t :: rest)) := by
  rw [vwalkAux.eq_def]
  simp [hleg, hfals, hsat, htv]

/-- In-block, a covered pending vertex is passed over (UF Def 4.2's "first
vertex not yet covered"; coverage is monotone along the path, so the
linear pass realizes the re-scan). -/
theorem vblock_skip_covered {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (v : Vertex p h) (vs : List (Vertex p h))
    (D : MDNF p h) (hcov : vertexCoveredB mu v = true) :
    vwalkAux fuel mu (v :: vs) D = vwalkAux fuel mu vs D := by
  rw [vwalkAux.eq_def]
  simp [hcov]

/-- With zero fuel an uncovered pending vertex dead-ends. -/
theorem vblock_zero {p h : Nat} (mu : MatchingMap p h) (v : Vertex p h)
    (vs : List (Vertex p h)) (D : MDNF p h)
    (hcov : vertexCoveredB mu v = false) :
    vwalkAux 0 mu (v :: vs) D = .leaf false := by
  rw [vwalkAux.eq_def]
  simp [hcov]

/-- In-block pigeon query: branch on the answering hole; used holes are
dead leaves; live answers compose the single-pair `DisjointExtension`. -/
theorem vblock_query_pigeon {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (i : Fin p) (vs : List (Vertex p h))
    (D : MDNF p h) (hcov : vertexCoveredB mu (.inl i) = false) :
    vwalkAux (fuel' + 1) mu (.inl i :: vs) D =
      .pquery i (fun a =>
        if holeUsed mu a = true then .leaf false
        else vwalkAux fuel' (compose mu (singleMatching i a)) vs D) := by
  rw [vwalkAux.eq_def]
  simp [hcov]

/-- In-block hole query: branch on the answering pigeon; matched pigeons
are dead leaves. -/
theorem vblock_query_hole {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (b : Fin h) (vs : List (Vertex p h))
    (D : MDNF p h) (hcov : vertexCoveredB mu (.inr b) = false) :
    vwalkAux (fuel' + 1) mu (.inr b :: vs) D =
      .hquery b (fun q =>
        if (mu q).isSome = true then .leaf false
        else vwalkAux fuel' (compose mu (singleMatching q b)) vs D) := by
  rw [vwalkAux.eq_def]
  simp [hcov]

/-- Every live vertex-query answer is a `DisjointExtension` step: the
pigeon side directly, the hole side through the answering free pigeon —
GA-1's composition laws apply along every walk path (the GA-2 statement,
re-usable verbatim since both query orientations compose
`singleMatching`). -/
theorem vwalk_query_disjointExtension {p h : Nat} (mu : MatchingMap p h)
    (i : Fin p) (a : Fin h) (hfree : mu i = none)
    (hhole : holeUsed mu a = false) :
    DisjointExtension mu (singleMatching i a) :=
  disjointExtension_singleMatching mu i a hfree hhole

/-! ## Pin 2.6 analogue: depth caps -/

/-- Fuel form: the vertex walk's depth never exceeds its fuel. -/
theorem vmdtDepth_vwalkAux_le_fuel {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h), vmdtDepth (vwalkAux fuel mu pending D) ≤ fuel
  | fuel, mu, [], [] => by
      rw [vwalk_nil]
      exact Nat.zero_le fuel
  | fuel, mu, [], t :: rest => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vwalk_skip_falsified fuel mu t rest hleg hfals]
          exact vmdtDepth_vwalkAux_le_fuel fuel mu [] rest
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vwalk_stop_satisfied fuel mu t rest hleg hfals' hsat]
            exact Nat.zero_le fuel
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vwalk_entry_zero mu t rest hleg hfals' hsat']
                exact Nat.le_refl 0
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vwalk_entry_none fuel' mu t rest hleg hfals' hsat'
                      htv]
                    exact Nat.zero_le _
                | cons v vs =>
                    cases v with
                    | inl i =>
                        rw [vwalk_entry_pigeon fuel' mu t rest i vs hleg
                          hfals' hsat' htv]
                        rw [vmdtDepth_pquery, Nat.add_comm]
                        apply Nat.add_le_add_right
                        apply Finset.sup_le
                        intro a _
                        by_cases hha : holeUsed mu a = true
                        · rw [if_pos hha]
                          exact Nat.zero_le fuel'
                        · rw [if_neg hha]
                          exact vmdtDepth_vwalkAux_le_fuel fuel'
                            (compose mu (singleMatching i a)) vs (t :: rest)
                    | inr b =>
                        rw [vwalk_entry_hole fuel' mu t rest b vs hleg
                          hfals' hsat' htv]
                        rw [vmdtDepth_hquery, Nat.add_comm]
                        apply Nat.add_le_add_right
                        apply Finset.sup_le
                        intro q _
                        by_cases hpm : (mu q).isSome = true
                        · rw [if_pos hpm]
                          exact Nat.zero_le fuel'
                        · rw [if_neg hpm]
                          exact vmdtDepth_vwalkAux_le_fuel fuel'
                            (compose mu (singleMatching q b)) vs (t :: rest)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vwalk_skip_illegal fuel mu t rest hleg']
        exact vmdtDepth_vwalkAux_le_fuel fuel mu [] rest
  | fuel, mu, v :: vs, D => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vblock_skip_covered fuel mu v vs D hcov]
        exact vmdtDepth_vwalkAux_le_fuel fuel mu vs D
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vblock_zero mu v vs D hcov']
            exact Nat.le_refl 0
        | succ fuel' =>
            cases v with
            | inl i =>
                rw [vblock_query_pigeon fuel' mu i vs D hcov']
                rw [vmdtDepth_pquery, Nat.add_comm]
                apply Nat.add_le_add_right
                apply Finset.sup_le
                intro a _
                by_cases hha : holeUsed mu a = true
                · rw [if_pos hha]
                  exact Nat.zero_le fuel'
                · rw [if_neg hha]
                  exact vmdtDepth_vwalkAux_le_fuel fuel'
                    (compose mu (singleMatching i a)) vs D
            | inr b =>
                rw [vblock_query_hole fuel' mu b vs D hcov']
                rw [vmdtDepth_hquery, Nat.add_comm]
                apply Nat.add_le_add_right
                apply Finset.sup_le
                intro q _
                by_cases hpm : (mu q).isSome = true
                · rw [if_pos hpm]
                  exact Nat.zero_le fuel'
                · rw [if_neg hpm]
                  exact vmdtDepth_vwalkAux_le_fuel fuel'
                    (compose mu (singleMatching q b)) vs D
  termination_by fuel _ pending D => (fuel, pending.length + D.length)

/-- Canonical form: the canonical vertex tree's depth is at most the base
matching's free-pigeon count — each vertex-query answer consumes one free
pigeon (and one free hole), exactly as the packet's GA-2.6 accounting
anticipated for the vertex re-scope. -/
theorem vmdtDepth_canonicalVMDT_le_freePigeons {p h : Nat} (D : MDNF p h)
    (mu : MatchingMap p h) :
    vmdtDepth (canonicalVMDT D mu) ≤ (freePigeons mu).card :=
  vmdtDepth_vwalkAux_le_fuel (freePigeons mu).card mu [] D

/-! ## Pin 2.2 analogue: the vertex-tree deep-path bad set -/

/-- The vertex-tree deep-path bad set: honest matchings with `ℓ` free
pigeons whose canonical **vertex** tree for `D` is deeper than `s`. Same
`> s` convention as GA-2's `badMatchings` (the `≥ s` UF convention is the
pin 3.6 off-by-one identification, resolved at the encode stage, not
here). -/
def vbadMatchings {p h : Nat} (D : MDNF p h) (s ell : Nat) :
    Finset (MatchingMap p h) :=
  (honestMatchingSpace p h ell).filter
    (fun mu => s < vmdtDepth (canonicalVMDT D mu))

theorem mem_vbadMatchings {p h : Nat} (D : MDNF p h) (s ell : Nat)
    (mu : MatchingMap p h) :
    mu ∈ vbadMatchings D s ell ↔
      (IsMatching mu ∧ (freePigeons mu).card = ell) ∧
        s < vmdtDepth (canonicalVMDT D mu) := by
  unfold vbadMatchings
  rw [Finset.mem_filter, mem_honestMatchingSpace]

theorem nv_termVertices :
    termVertices (emptyMatching 1 1)
        [((⟨0, by decide⟩ : Fin 1), (⟨0, by decide⟩ : Fin 1))] =
      [Sum.inl ⟨0, by decide⟩, Sum.inr ⟨0, by decide⟩] := by
  decide

theorem nv_canonicalVMDT_depth_pos :
    0 < vmdtDepth (canonicalVMDT nvD (emptyMatching 1 1)) := by
  have hstep := vwalk_entry_pigeon (p := 1) (h := 1) 0 (emptyMatching 1 1)
    [(⟨0, by decide⟩, ⟨0, by decide⟩)] [] ⟨0, by decide⟩
    [Sum.inr ⟨0, by decide⟩] (by decide) (by decide) (by decide)
    nv_termVertices
  have hcan : canonicalVMDT nvD (emptyMatching 1 1) =
      vwalkAux (0 + 1) (emptyMatching 1 1) []
        [[((⟨0, by decide⟩ : Fin 1), (⟨0, by decide⟩ : Fin 1))]] := by
    unfold canonicalVMDT
    rw [nv_freePigeons_card]
    rfl
  rw [hcan, hstep, vmdtDepth_pquery]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)

/-- Pin 2.2 analogue: the vertex-tree deep-path bad set is definitionally
non-vacuous — the GA-2 concrete instance (one pigeon, one hole, the
single-pair term, the empty base matching) is a member here too. -/
theorem vbadMatchings_nonvacuity :
    emptyMatching 1 1 ∈ vbadMatchings nvD 0 1 := by
  rw [mem_vbadMatchings]
  exact ⟨⟨isMatching_empty 1 1, nv_freePigeons_card⟩,
    nv_canonicalVMDT_depth_pos⟩

theorem vbadMatchings_nonempty :
    (vbadMatchings nvD 0 1).Nonempty :=
  ⟨emptyMatching 1 1, vbadMatchings_nonvacuity⟩

/-! ## The kernel-pinned walk-vs-vertex divergence (memo L5)

The reviewed GA-3 memo's pinned instance: square `3 × 3`, width 1, three
terms each demanding hole 0, empty base matching (`ℓ = 3`). The GA-2
pigeon-only canonical walk falsifies its way through all three terms on
the deviating branch — depth exactly 3 — while the vertex-query canonical
tree covers hole 0 inside the first entered block, so every other
hole-0-demanding term is determined after block 1 — depth exactly 2. The
two canonical trees are different objects on the same DNF and base
matching; GA-3's encode counts the deep-path bad set of the **vertex**
tree. -/

/-- The pinned divergence DNF: three width-1 terms demanding hole 0. -/
def divD : MDNF 3 3 :=
  [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
    [((2 : Fin 3), (0 : Fin 3))]]

theorem div_freePigeons_card :
    (freePigeons (emptyMatching 3 3)).card = 3 := by
  decide

/-- Walk side of the divergence: the pigeon-only canonical walk on the
pinned instance has depth exactly 3 (the fuel cap is met by the branch
`p0 ↦ h1, p1 ↦ h2, p2 queried`). -/
theorem div_walk_depth :
    mdtDepth (canonicalMDT divD (emptyMatching 3 3)) = 3 := by
  unfold canonicalMDT divD
  rw [div_freePigeons_card]
  apply Nat.le_antisymm
  · exact mdtDepth_mwalk_le_fuel 3 (emptyMatching 3 3) _
  · -- descend the deviating branch p0 ↦ h1, p1 ↦ h2
    have hstep1 := mwalk_query_step (p := 3) (h := 3) 2
      (emptyMatching 3 3) [((0 : Fin 3), (0 : Fin 3))]
      [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]]
      ((0 : Fin 3), (0 : Fin 3)) (by decide) (by decide) (by decide)
      (by decide)
    -- level 3: at p0 ↦ h1, p1 ↦ h2 the third term is entered and queried
    have hA : 1 ≤ mdtDepth (mwalk 1
        (compose (compose (emptyMatching 3 3)
          (singleMatching (0 : Fin 3) (1 : Fin 3)))
          (singleMatching (1 : Fin 3) (2 : Fin 3)))
        ([((1 : Fin 3), (0 : Fin 3))] :: [[((2 : Fin 3), (0 : Fin 3))]])) := by
      rw [mwalk_skip_falsified 1 _ _ _ (by decide) (by decide)]
      rw [mwalk_query_step (p := 3) (h := 3) 0 _
        [((2 : Fin 3), (0 : Fin 3))] [] ((2 : Fin 3), (0 : Fin 3))
        (by decide) (by decide) (by decide) (by decide)]
      rw [mdtDepth_query]
      exact Nat.le_add_right 1 _
    -- level 2: at p0 ↦ h1 the second term is entered and queried
    have hB : 2 ≤ mdtDepth (mwalk 2
        (compose (emptyMatching 3 3)
          (singleMatching (0 : Fin 3) (1 : Fin 3)))
        (([((0 : Fin 3), (0 : Fin 3))]) ::
          ([((1 : Fin 3), (0 : Fin 3))] :: [[((2 : Fin 3), (0 : Fin 3))]]))) := by
      rw [mwalk_skip_falsified 2 _ _ _ (by decide) (by decide)]
      rw [mwalk_query_step (p := 3) (h := 3) 1 _
        [((1 : Fin 3), (0 : Fin 3))] [[((2 : Fin 3), (0 : Fin 3))]]
        ((1 : Fin 3), (0 : Fin 3)) (by decide) (by decide) (by decide)
        (by decide)]
      show 2 ≤ mdtDepth (MDTree.query (1 : Fin 3) (fun a =>
        if holeUsed (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (1 : Fin 3))) a = true
          then MDTree.leaf false
          else mwalk 1 (compose (compose (emptyMatching 3 3)
              (singleMatching (0 : Fin 3) (1 : Fin 3)))
              (singleMatching (1 : Fin 3) a))
            [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]]))
      have hA' : 1 ≤ mdtDepth
          (if holeUsed (compose (emptyMatching 3 3)
              (singleMatching (0 : Fin 3) (1 : Fin 3))) (2 : Fin 3) = true
            then MDTree.leaf false
            else mwalk 1
              (compose (compose (emptyMatching 3 3)
                (singleMatching (0 : Fin 3) (1 : Fin 3)))
                (singleMatching (1 : Fin 3) (2 : Fin 3)))
              ([((1 : Fin 3), (0 : Fin 3))] ::
                [[((2 : Fin 3), (0 : Fin 3))]])) := by
        rw [if_neg (by decide)]
        exact hA
      exact Nat.le_trans (Nat.add_le_add_left hA' 1)
        (mdtDepth_query_ge_child (1 : Fin 3)
          (fun a =>
            if holeUsed (compose (emptyMatching 3 3)
                (singleMatching (0 : Fin 3) (1 : Fin 3))) a = true
              then MDTree.leaf false
              else mwalk 1 (compose (compose (emptyMatching 3 3)
                  (singleMatching (0 : Fin 3) (1 : Fin 3)))
                  (singleMatching (1 : Fin 3) a))
                [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]])
          (2 : Fin 3))
    rw [hstep1]
    show 3 ≤ mdtDepth (MDTree.query (0 : Fin 3) (fun a =>
      if holeUsed (emptyMatching 3 3) a = true then MDTree.leaf false
      else mwalk 2 (compose (emptyMatching 3 3)
          (singleMatching (0 : Fin 3) a))
        [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
          [((2 : Fin 3), (0 : Fin 3))]]))
    have hB' : 2 ≤ mdtDepth
        (if holeUsed (emptyMatching 3 3) (1 : Fin 3) = true
          then MDTree.leaf false
          else mwalk 2
            (compose (emptyMatching 3 3)
              (singleMatching (0 : Fin 3) (1 : Fin 3)))
            (([((0 : Fin 3), (0 : Fin 3))]) ::
              ([((1 : Fin 3), (0 : Fin 3))] ::
                [[((2 : Fin 3), (0 : Fin 3))]]))) := by
      rw [if_neg (by decide)]
      exact hB
    exact Nat.le_trans (Nat.add_le_add_left hB' 1)
      (mdtDepth_query_ge_child (0 : Fin 3)
        (fun a =>
          if holeUsed (emptyMatching 3 3) a = true then MDTree.leaf false
          else mwalk 2 (compose (emptyMatching 3 3)
              (singleMatching (0 : Fin 3) a))
            [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
              [((2 : Fin 3), (0 : Fin 3))]])
        (1 : Fin 3))

theorem div_termVertices :
    termVertices (emptyMatching 3 3) [((0 : Fin 3), (0 : Fin 3))] =
      [Sum.inl (0 : Fin 3), Sum.inr (0 : Fin 3)] := by
  decide

/-- Leaf chain: the satisfying answer `p0 ↦ h0` closes block 1 (hole 0
covered by the answer pair) and stops satisfied at depth 0. -/
theorem div_child0 :
    vwalkAux 2 (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (0 : Fin 3)))
      [Sum.inr (0 : Fin 3)]
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] = .leaf true := by
  rw [vblock_skip_covered _ _ _ _ _ (by decide)]
  rw [vwalk_stop_satisfied _ _ _ _ (by decide) (by decide) (by decide)]

/-- Leaf chain: after `p0 ↦ h1`, the in-block hole query `h0 ↦ p1`
determines everything — term 1 falsified, term 2 satisfied. -/
theorem div_child1_q1 :
    vwalkAux 1 (compose (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (1 : Fin 3)))
        (singleMatching (1 : Fin 3) (0 : Fin 3)))
      []
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] = .leaf true := by
  rw [vwalk_skip_falsified _ _ _ _ (by decide) (by decide)]
  rw [vwalk_stop_satisfied _ _ _ _ (by decide) (by decide) (by decide)]

/-- Leaf chain: after `p0 ↦ h1`, the in-block hole answer `h0 ↦ p2`
determines everything — terms 1 and 2 falsified, term 3 satisfied. -/
theorem div_child1_q2 :
    vwalkAux 1 (compose (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (1 : Fin 3)))
        (singleMatching (2 : Fin 3) (0 : Fin 3)))
      []
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] = .leaf true := by
  rw [vwalk_skip_falsified _ _ _ _ (by decide) (by decide)]
  rw [vwalk_skip_falsified _ _ _ _ (by decide) (by decide)]
  rw [vwalk_stop_satisfied _ _ _ _ (by decide) (by decide) (by decide)]

/-- Subtree computation: after the falsifying answer `p0 ↦ h1`, block 1
still owes its hole vertex — the hole query `h0` resolves every branch at
the next level, so the subtree has depth exactly 1. -/
theorem div_child1_depth :
    vmdtDepth (vwalkAux 2 (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (1 : Fin 3)))
      [Sum.inr (0 : Fin 3)]
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]]) = 1 := by
  rw [vblock_query_hole 1 _ (0 : Fin 3) []
    [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] (by decide)]
  rw [vmdtDepth_hquery]
  have hsup : (Finset.univ : Finset (Fin 3)).sup (fun q =>
      vmdtDepth (if ((compose (emptyMatching 3 3)
          (singleMatching (0 : Fin 3) (1 : Fin 3))) q).isSome = true
        then VMDTree.leaf false
        else vwalkAux 1 (compose (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (1 : Fin 3)))
            (singleMatching q (0 : Fin 3))) []
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]])) = 0 := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro q _
      fin_cases q
      · exact Nat.le_refl 0
      · show vmdtDepth (vwalkAux 1 (compose (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (1 : Fin 3)))
            (singleMatching (1 : Fin 3) (0 : Fin 3))) []
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 0
        rw [div_child1_q1]
        exact Nat.le_refl 0
      · show vmdtDepth (vwalkAux 1 (compose (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (1 : Fin 3)))
            (singleMatching (2 : Fin 3) (0 : Fin 3))) []
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 0
        rw [div_child1_q2]
        exact Nat.le_refl 0
    · exact Nat.zero_le _
  rw [hsup]

/-- Symmetric leaf chains and subtree for the answer `p0 ↦ h2`. -/
theorem div_child2_q1 :
    vwalkAux 1 (compose (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (2 : Fin 3)))
        (singleMatching (1 : Fin 3) (0 : Fin 3)))
      []
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] = .leaf true := by
  rw [vwalk_skip_falsified _ _ _ _ (by decide) (by decide)]
  rw [vwalk_stop_satisfied _ _ _ _ (by decide) (by decide) (by decide)]

theorem div_child2_q2 :
    vwalkAux 1 (compose (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (2 : Fin 3)))
        (singleMatching (2 : Fin 3) (0 : Fin 3)))
      []
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] = .leaf true := by
  rw [vwalk_skip_falsified _ _ _ _ (by decide) (by decide)]
  rw [vwalk_skip_falsified _ _ _ _ (by decide) (by decide)]
  rw [vwalk_stop_satisfied _ _ _ _ (by decide) (by decide) (by decide)]

theorem div_child2_depth :
    vmdtDepth (vwalkAux 2 (compose (emptyMatching 3 3)
        (singleMatching (0 : Fin 3) (2 : Fin 3)))
      [Sum.inr (0 : Fin 3)]
      [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]]) = 1 := by
  rw [vblock_query_hole 1 _ (0 : Fin 3) []
    [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]] (by decide)]
  rw [vmdtDepth_hquery]
  have hsup : (Finset.univ : Finset (Fin 3)).sup (fun q =>
      vmdtDepth (if ((compose (emptyMatching 3 3)
          (singleMatching (0 : Fin 3) (2 : Fin 3))) q).isSome = true
        then VMDTree.leaf false
        else vwalkAux 1 (compose (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (2 : Fin 3)))
            (singleMatching q (0 : Fin 3))) []
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
        [((2 : Fin 3), (0 : Fin 3))]])) = 0 := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro q _
      fin_cases q
      · exact Nat.le_refl 0
      · show vmdtDepth (vwalkAux 1 (compose (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (2 : Fin 3)))
            (singleMatching (1 : Fin 3) (0 : Fin 3))) []
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 0
        rw [div_child2_q1]
        exact Nat.le_refl 0
      · show vmdtDepth (vwalkAux 1 (compose (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (2 : Fin 3)))
            (singleMatching (2 : Fin 3) (0 : Fin 3))) []
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 0
        rw [div_child2_q2]
        exact Nat.le_refl 0
    · exact Nat.zero_le _
  rw [hsup]

/-- Vertex side of the divergence: the canonical vertex tree on the
pinned instance has depth exactly 2 — after block 1's hole query, hole 0
is covered on every branch, so no other hole-0-demanding term is ever
entered (the anti-collision behavior the encode's σ-compatibility
needs). -/
theorem div_vertex_depth :
    vmdtDepth (canonicalVMDT divD (emptyMatching 3 3)) = 2 := by
  unfold canonicalVMDT divD
  rw [div_freePigeons_card]
  have hentry := vwalk_entry_pigeon (p := 3) (h := 3) 2
    (emptyMatching 3 3) [((0 : Fin 3), (0 : Fin 3))]
    [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]]
    (0 : Fin 3) [Sum.inr (0 : Fin 3)] (by decide) (by decide) (by decide)
    div_termVertices
  rw [hentry, vmdtDepth_pquery]
  have hsup : (Finset.univ : Finset (Fin 3)).sup (fun a =>
      vmdtDepth (if holeUsed (emptyMatching 3 3) a = true
        then VMDTree.leaf false
        else vwalkAux 2 (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) a)) [Sum.inr (0 : Fin 3)]
          ([((0 : Fin 3), (0 : Fin 3))] ::
            [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]]))) =
      1 := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro a _
      fin_cases a
      · show vmdtDepth (vwalkAux 2 (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (0 : Fin 3)))
          [Sum.inr (0 : Fin 3)]
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 1
        rw [div_child0]
        exact Nat.zero_le 1
      · show vmdtDepth (vwalkAux 2 (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (1 : Fin 3)))
          [Sum.inr (0 : Fin 3)]
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 1
        rw [div_child1_depth]
      · show vmdtDepth (vwalkAux 2 (compose (emptyMatching 3 3)
            (singleMatching (0 : Fin 3) (2 : Fin 3)))
          [Sum.inr (0 : Fin 3)]
          [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
            [((2 : Fin 3), (0 : Fin 3))]]) ≤ 1
        rw [div_child2_depth]
    · have hchild : (1 : Nat) =
          vmdtDepth (if holeUsed (emptyMatching 3 3) (1 : Fin 3) = true
            then VMDTree.leaf false
            else vwalkAux 2 (compose (emptyMatching 3 3)
                (singleMatching (0 : Fin 3) (1 : Fin 3)))
              [Sum.inr (0 : Fin 3)]
              [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
                [((2 : Fin 3), (0 : Fin 3))]]) := by
        rw [if_neg (by decide), div_child1_depth]
      exact Nat.le_trans (Nat.le_of_eq hchild)
        (Finset.le_sup (f := fun a =>
          vmdtDepth (if holeUsed (emptyMatching 3 3) a = true
            then VMDTree.leaf false
            else vwalkAux 2 (compose (emptyMatching 3 3)
                (singleMatching (0 : Fin 3) a)) [Sum.inr (0 : Fin 3)]
              [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (0 : Fin 3))],
                [((2 : Fin 3), (0 : Fin 3))]]))
          (Finset.mem_univ (1 : Fin 3)))
  rw [hsup]

/-- **The kernel-pinned walk-vs-vertex divergence** (memo L5; pin 3.0's
divergence witness; companion to `walk_boolean_depth1_divergence`): on the
pinned instance the GA-2 pigeon-only canonical walk and the GA-3
vertex-query canonical tree are different objects — depth 3 versus
depth 2. The vertex tree is the one whose deep-path bad set the extension
encode counts; the pigeon-only walk stays banked for its composition and
falsification artifacts, not the counting spine. -/
theorem walk_vertex_depth_divergence :
    vmdtDepth (canonicalVMDT divD (emptyMatching 3 3)) <
        mdtDepth (canonicalMDT divD (emptyMatching 3 3)) ∧
      mdtDepth (canonicalMDT divD (emptyMatching 3 3)) = 3 ∧
      vmdtDepth (canonicalVMDT divD (emptyMatching 3 3)) = 2 := by
  refine ⟨?_, div_walk_depth, div_vertex_depth⟩
  rw [div_walk_depth, div_vertex_depth]
  exact Nat.lt_succ_self 2

end PHPMatchingVertexTree
end PvNP
