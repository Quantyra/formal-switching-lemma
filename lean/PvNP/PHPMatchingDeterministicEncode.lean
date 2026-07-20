import PvNP.PHPMatchingAnswerTransport
import Mathlib.Data.Finset.Sort

/-!
# GA-3b deterministic trace feed and encode assembly (S2188)

This module closes the deterministic feed part of the matching extension
encode route on top of the S2187 vertex-walk trace infrastructure.  The
construction follows the walk state consumed by `vtrace`: at every live query
it chooses the first answer, in the canonical finite order, whose branch is
live and preserves enough remaining `vmdtDepth`.  Dead answers are never
selected.

The main synchronization theorem is deliberately bounded: for a square
hole-injective base matching `rho`, if `t` is at most the canonical vertex
tree depth, then the deterministic feed has length `t` and replaying the
canonical trace against that feed has exactly `t` query events.

Stages 3-6 assemble the concrete graded encode components along that feed:
G2 = beta-marks from `blockSigmas`, G3 = replay-namespace answer codes in
`[2*ell]` computed from G1 and sigma rather than the unknown base, the
free-pigeon drop on G1 = `encodeExt`, and the packaged `encodeMatch` tuple
whose G2/G3 side matches the predicates consumed by
`mcode_answers_family_card_le`.

This is trace/encode bookkeeping only.  It proves no injectivity, no bad-set
count, no switching lemma, no Frege/PHP or NP/circuit lower bound, and no
P-versus-NP statement.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingDeterministicEncode

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingAnswerTransport
open RestrictedPHPFloor

/-! ## Leftmost live depth-preserving answer selection -/

/-- A hole answer is live for a pigeon query and preserves `s` more steps. -/
def liveHoleDepthB {p h : Nat} (mu : MatchingMap p h) (i : Fin p)
    (fuel' : Nat) (pending : List (Vertex p h)) (D : MDNF p h)
    (s : Nat) (a : Fin h) : Bool :=
  if holeUsed mu a = false then
    decide
      (s ≤ vmdtDepth
        (vwalkAux fuel' (compose mu (singleMatching i a)) pending D))
  else
    false

/-- A pigeon answer is live for a hole query and preserves `s` more steps. -/
def livePigeonDepthB {p h : Nat} (mu : MatchingMap p h) (b : Fin h)
    (fuel' : Nat) (pending : List (Vertex p h)) (D : MDNF p h)
    (s : Nat) (q : Fin p) : Bool :=
  if (mu q).isSome = false then
    decide
      (s ≤ vmdtDepth
        (vwalkAux fuel' (compose mu (singleMatching q b)) pending D))
  else
    false

/-- First live depth-preserving hole answer in canonical `Fin` order. -/
def leftmostLiveDepthHole? {p h : Nat} (mu : MatchingMap p h) (i : Fin p)
    (fuel' : Nat) (pending : List (Vertex p h)) (D : MDNF p h)
    (s : Nat) : Option (Fin h) :=
  (finList h).find? (liveHoleDepthB mu i fuel' pending D s)

/-- First live depth-preserving pigeon answer in canonical `Fin` order. -/
def leftmostLiveDepthPigeon? {p h : Nat} (mu : MatchingMap p h) (b : Fin h)
    (fuel' : Nat) (pending : List (Vertex p h)) (D : MDNF p h)
    (s : Nat) : Option (Fin p) :=
  (finList p).find? (livePigeonDepthB mu b fuel' pending D s)

theorem leftmostLiveDepthHole?_eq_some {p h : Nat}
    (mu : MatchingMap p h) (i : Fin p) (fuel' : Nat)
    (pending : List (Vertex p h)) (D : MDNF p h) (s : Nat)
    (a : Fin h) :
    leftmostLiveDepthHole? mu i fuel' pending D s = some a ↔
      liveHoleDepthB mu i fuel' pending D s a = true ∧
        ∃ pre suf,
          finList h = pre ++ a :: suf ∧
            ∀ b ∈ pre, (!liveHoleDepthB mu i fuel' pending D s b) = true := by
  unfold leftmostLiveDepthHole?
  exact List.find?_eq_some

theorem leftmostLiveDepthPigeon?_eq_some {p h : Nat}
    (mu : MatchingMap p h) (b : Fin h) (fuel' : Nat)
    (pending : List (Vertex p h)) (D : MDNF p h) (s : Nat)
    (q : Fin p) :
    leftmostLiveDepthPigeon? mu b fuel' pending D s = some q ↔
      livePigeonDepthB mu b fuel' pending D s q = true ∧
        ∃ pre suf,
          finList p = pre ++ q :: suf ∧
            ∀ r ∈ pre, (!livePigeonDepthB mu b fuel' pending D s r) = true := by
  unfold leftmostLiveDepthPigeon?
  exact List.find?_eq_some

private theorem liveHoleDepthB_true {p h : Nat} {mu : MatchingMap p h}
    {i : Fin p} {fuel' : Nat} {pending : List (Vertex p h)}
    {D : MDNF p h} {s : Nat} {a : Fin h}
    (ha : liveHoleDepthB mu i fuel' pending D s a = true) :
    holeUsed mu a = false ∧
      s ≤ vmdtDepth
        (vwalkAux fuel' (compose mu (singleMatching i a)) pending D) := by
  unfold liveHoleDepthB at ha
  by_cases hha : holeUsed mu a = false
  · rw [if_pos hha] at ha
    exact ⟨hha, of_decide_eq_true ha⟩
  · rw [if_neg hha] at ha
    cases ha

private theorem livePigeonDepthB_true {p h : Nat} {mu : MatchingMap p h}
    {b : Fin h} {fuel' : Nat} {pending : List (Vertex p h)}
    {D : MDNF p h} {s : Nat} {q : Fin p}
    (hq : livePigeonDepthB mu b fuel' pending D s q = true) :
    (mu q).isSome = false ∧
      s ≤ vmdtDepth
        (vwalkAux fuel' (compose mu (singleMatching q b)) pending D) := by
  unfold livePigeonDepthB at hq
  by_cases hfree : (mu q).isSome = false
  · rw [if_pos hfree] at hq
    exact ⟨hfree, of_decide_eq_true hq⟩
  · rw [if_neg hfree] at hq
    cases hq

private theorem leftmostLiveDepthHole?_spec_of_exists {p h : Nat}
    {mu : MatchingMap p h} {i : Fin p} {fuel' : Nat}
    {pending : List (Vertex p h)} {D : MDNF p h} {s : Nat}
    (hex : ∃ a, liveHoleDepthB mu i fuel' pending D s a = true) :
    ∃ a, leftmostLiveDepthHole? mu i fuel' pending D s = some a ∧
      holeUsed mu a = false ∧
        s ≤ vmdtDepth
          (vwalkAux fuel' (compose mu (singleMatching i a)) pending D) := by
  have hsome : (leftmostLiveDepthHole? mu i fuel' pending D s).isSome = true := by
    unfold leftmostLiveDepthHole?
    rw [List.find?_isSome]
    rcases hex with ⟨a, ha⟩
    exact ⟨a, mem_finList a, ha⟩
  rcases Option.isSome_iff_exists.mp hsome with ⟨a, hsel⟩
  have hpred : liveHoleDepthB mu i fuel' pending D s a = true := by
    unfold leftmostLiveDepthHole? at hsel
    exact List.find?_some hsel
  exact ⟨a, hsel, (liveHoleDepthB_true hpred).1,
    (liveHoleDepthB_true hpred).2⟩

private theorem leftmostLiveDepthPigeon?_spec_of_exists {p h : Nat}
    {mu : MatchingMap p h} {b : Fin h} {fuel' : Nat}
    {pending : List (Vertex p h)} {D : MDNF p h} {s : Nat}
    (hex : ∃ q, livePigeonDepthB mu b fuel' pending D s q = true) :
    ∃ q, leftmostLiveDepthPigeon? mu b fuel' pending D s = some q ∧
      (mu q).isSome = false ∧
        s ≤ vmdtDepth
          (vwalkAux fuel' (compose mu (singleMatching q b)) pending D) := by
  have hsome :
      (leftmostLiveDepthPigeon? mu b fuel' pending D s).isSome = true := by
    unfold leftmostLiveDepthPigeon?
    rw [List.find?_isSome]
    rcases hex with ⟨q, hq⟩
    exact ⟨q, mem_finList q, hq⟩
  rcases Option.isSome_iff_exists.mp hsome with ⟨q, hsel⟩
  have hpred : livePigeonDepthB mu b fuel' pending D s q = true := by
    unfold leftmostLiveDepthPigeon? at hsel
    exact List.find?_some hsel
  exact ⟨q, hsel, (livePigeonDepthB_true hpred).1,
    (livePigeonDepthB_true hpred).2⟩

private theorem freePigeons_compose_single_card {p h : Nat}
    {mu : MatchingMap p h} {i : Fin p} {a : Fin h} {fuel' : Nat}
    (hinv : (freePigeons mu).card = fuel' + 1) (hfree : mu i = none) :
    (freePigeons (compose mu (singleMatching i a))).card = fuel' := by
  have hdrop := freePigeons_compose_card mu (singleMatching i a) {i}
    (by
      intro j
      unfold singleMatching
      by_cases hji : j = i
      · simp [hji]
      · simp [hji])
    (by
      intro j hj
      rw [Finset.mem_singleton] at hj
      rw [hj]
      exact (mem_freePigeons mu i).mpr hfree)
  rw [hdrop, Finset.card_singleton, hinv]
  omega

private theorem matching_free_of_isSome_false {p h : Nat}
    {mu : MatchingMap p h} {q : Fin p} (hq : (mu q).isSome = false) :
    mu q = none := by
  cases hmq : mu q with
  | none => rfl
  | some a =>
      rw [hmq] at hq
      cases hq

private theorem exists_live_hole_depth {p h : Nat} (hsq : p = h)
    {mu : MatchingMap p h} {i : Fin p} {fuel' : Nat}
    {pending : List (Vertex p h)} {D : MDNF p h} {s : Nat}
    (hmu : IsMatching mu) (hinv : (freePigeons mu).card = fuel' + 1)
    (hdepth :
      s + 1 ≤ vmdtDepth
        (.pquery i (fun a =>
          if holeUsed mu a = true then .leaf false
          else vwalkAux fuel' (compose mu (singleMatching i a)) pending D))) :
    ∃ a, liveHoleDepthB mu i fuel' pending D s a = true := by
  cases s with
  | zero =>
      have hcard := card_freeHoles_square hsq hmu hinv
      have hpos : 0 < (freeHoles mu).card := by
        rw [hcard]
        exact Nat.succ_pos fuel'
      rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
      have hfreeHole : holeUsed mu a = false := (Finset.mem_filter.mp ha).2
      refine ⟨a, ?_⟩
      unfold liveHoleDepthB
      rw [if_pos hfreeHole]
      exact decide_eq_true (Nat.zero_le _)
  | succ s =>
      let child : Fin h → VMDTree p h := fun a =>
        if holeUsed mu a = true then .leaf false
        else vwalkAux fuel' (compose mu (singleMatching i a)) pending D
      have hsup : s + 1 ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) := by
        rw [vmdtDepth_pquery] at hdepth
        exact Nat.le_of_succ_le_succ (by simpa [child, Nat.add_comm] using hdepth)
      have hlt : s < Finset.univ.sup (fun a => vmdtDepth (child a)) :=
        Nat.lt_of_succ_le hsup
      rcases (Finset.lt_sup_iff.mp hlt) with ⟨a, _, ha⟩
      have hchildIf : s + 1 ≤ vmdtDepth (child a) := Nat.succ_le_of_lt ha
      by_cases hdead : holeUsed mu a = true
      · have hdeadDepth :
            s + 1 ≤ vmdtDepth (.leaf false : VMDTree p h) := by
          simpa [child, hdead] using hchildIf
        have hzero : s + 1 ≤ 0 := by
          exact hdeadDepth
        exact False.elim (Nat.not_succ_le_zero s hzero)
      · have hfreeHole : holeUsed mu a = false := Bool.eq_false_iff.mpr hdead
        have hchild :
            s + 1 ≤ vmdtDepth
              (vwalkAux fuel' (compose mu (singleMatching i a)) pending D) := by
          simpa [child, hdead] using hchildIf
        refine ⟨a, ?_⟩
        unfold liveHoleDepthB
        rw [if_pos hfreeHole]
        exact decide_eq_true hchild

private theorem exists_live_pigeon_depth {p h : Nat}
    {mu : MatchingMap p h} {b : Fin h} {fuel' : Nat}
    {pending : List (Vertex p h)} {D : MDNF p h} {s : Nat}
    (hinv : (freePigeons mu).card = fuel' + 1)
    (hdepth :
      s + 1 ≤ vmdtDepth
        (.hquery b (fun q =>
          if (mu q).isSome = true then .leaf false
          else vwalkAux fuel' (compose mu (singleMatching q b)) pending D))) :
    ∃ q, livePigeonDepthB mu b fuel' pending D s q = true := by
  cases s with
  | zero =>
      have hpos : 0 < (freePigeons mu).card := by
        rw [hinv]
        exact Nat.succ_pos fuel'
      rcases Finset.card_pos.mp hpos with ⟨q, hq⟩
      have hfree : mu q = none := (mem_freePigeons mu q).mp hq
      have hfreeIs : (mu q).isSome = false := by
        rw [hfree]
        rfl
      refine ⟨q, ?_⟩
      unfold livePigeonDepthB
      rw [if_pos hfreeIs]
      exact decide_eq_true (Nat.zero_le _)
  | succ s =>
      let child : Fin p → VMDTree p h := fun q =>
        if (mu q).isSome = true then .leaf false
        else vwalkAux fuel' (compose mu (singleMatching q b)) pending D
      have hsup : s + 1 ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) := by
        rw [vmdtDepth_hquery] at hdepth
        exact Nat.le_of_succ_le_succ (by simpa [child, Nat.add_comm] using hdepth)
      have hlt : s < Finset.univ.sup (fun q => vmdtDepth (child q)) :=
        Nat.lt_of_succ_le hsup
      rcases (Finset.lt_sup_iff.mp hlt) with ⟨q, _, hq⟩
      have hchildIf : s + 1 ≤ vmdtDepth (child q) := Nat.succ_le_of_lt hq
      by_cases hdead : (mu q).isSome = true
      · have hdeadDepth :
            s + 1 ≤ vmdtDepth (.leaf false : VMDTree p h) := by
          simpa [child, hdead] using hchildIf
        have hzero : s + 1 ≤ 0 := by
          exact hdeadDepth
        exact False.elim (Nat.not_succ_le_zero s hzero)
      · have hfreeIs : (mu q).isSome = false := Bool.eq_false_iff.mpr hdead
        have hchild :
            s + 1 ≤ vmdtDepth
              (vwalkAux fuel' (compose mu (singleMatching q b)) pending D) := by
          simpa [child, hdead] using hchildIf
        refine ⟨q, ?_⟩
        unfold livePigeonDepthB
        rw [if_pos hfreeIs]
        exact decide_eq_true hchild

/-! ## Deterministic feed -/

/-- Deterministic leftmost live feed for an arbitrary canonical walk state. -/
def leftmostLiveFeedAux {p h : Nat} :
    Nat → MatchingMap p h → List (Vertex p h) → MDNF p h → Nat →
      List (Vertex p h)
  | _, _, _, _, 0 => []
  | _, _, [], [], _ + 1 => []
  | fuel, mu, [], t :: rest, s + 1 =>
      if termMatchingLegalB t = false then
        leftmostLiveFeedAux fuel mu [] rest (s + 1)
      else if termFalsifiedB mu t = true then
        leftmostLiveFeedAux fuel mu [] rest (s + 1)
      else if termSatisfiedB mu t = true then
        []
      else
        match fuel with
        | 0 => []
        | fuel' + 1 =>
            match termVertices mu t with
            | [] => []
            | .inl i :: vs =>
                match leftmostLiveDepthHole? mu i fuel' vs (t :: rest) s with
                | some a =>
                    Sum.inr a ::
                      leftmostLiveFeedAux fuel'
                        (compose mu (singleMatching i a)) vs (t :: rest) s
                | none => []
            | .inr b :: vs =>
                match leftmostLiveDepthPigeon? mu b fuel' vs (t :: rest) s with
                | some q =>
                    Sum.inl q ::
                      leftmostLiveFeedAux fuel'
                        (compose mu (singleMatching q b)) vs (t :: rest) s
                | none => []
  | fuel, mu, v :: vs, D, s + 1 =>
      if vertexCoveredB mu v = true then
        leftmostLiveFeedAux fuel mu vs D (s + 1)
      else
        match fuel with
        | 0 => []
        | fuel' + 1 =>
            match v with
            | .inl i =>
                match leftmostLiveDepthHole? mu i fuel' vs D s with
                | some a =>
                    Sum.inr a ::
                      leftmostLiveFeedAux fuel'
                        (compose mu (singleMatching i a)) vs D s
                | none => []
            | .inr b =>
                match leftmostLiveDepthPigeon? mu b fuel' vs D s with
                | some q =>
                    Sum.inl q ::
                      leftmostLiveFeedAux fuel'
                        (compose mu (singleMatching q b)) vs D s
                | none => []
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

/-- Canonical deterministic feed from the root walk state. -/
def leftmostLiveFeed {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (t : Nat) : List (Vertex p h) :=
  leftmostLiveFeedAux (freePigeons rho).card rho [] D t

/-! ## Exact trace synchronization -/

theorem eventsSteps_vevents_nil_feed {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h),
      eventsSteps (vevents fuel mu pending D []) = []
  | fuel, mu, [], [] => by
      rw [vevents_nil]
      rfl
  | fuel, mu, [], t :: rest => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest [] hleg hfals]
          exact eventsSteps_vevents_nil_feed fuel mu [] rest
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest [] hleg hfals' hsat]
            rfl
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest [] hleg hfals' hsat']
                rfl
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t rest [] hleg
                      hfals' hsat' htv]
                    rfl
                | cons v vs =>
                    cases v with
                    | inl i =>
                        rw [vevents_entry_feed_nil fuel' mu t rest i vs
                          hleg hfals' hsat' htv]
                        rfl
                    | inr b =>
                        exact False.elim
                          (absurd htv (termVertices_head_not_hole mu t b vs))
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest [] hleg']
        exact eventsSteps_vevents_nil_feed fuel mu [] rest
  | fuel, mu, v :: vs, D => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D [] hcov]
        exact eventsSteps_vevents_nil_feed fuel mu vs D
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D [] hcov']
            rfl
        | succ fuel' =>
            rw [vevents_block_feed_nil fuel' mu v vs D hcov']
            rfl
  termination_by fuel _ pending D => (fuel, pending.length + D.length)

theorem leftmostLiveFeedAux_sync {p h : Nat} (hsq : p = h) :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (t : Nat), IsMatching mu →
      (freePigeons mu).card = fuel →
      t ≤ vmdtDepth (vwalkAux fuel mu pending D) →
      (leftmostLiveFeedAux fuel mu pending D t).length = t ∧
        (eventsSteps
          (vevents fuel mu pending D
            (leftmostLiveFeedAux fuel mu pending D t))).length = t
  | fuel, mu, pending, D, 0, _hmu, _hinv, _hdepth => by
      have hfeed : leftmostLiveFeedAux fuel mu pending D 0 = [] := by
        rw [leftmostLiveFeedAux.eq_def]
        simp
      constructor
      · rw [hfeed]
        rfl
      · rw [hfeed]
        rw [eventsSteps_vevents_nil_feed fuel mu pending D]
        rfl
  | fuel, mu, [], [], s + 1, _hmu, _hinv, hdepth => by
      rw [vwalk_nil] at hdepth
      exact False.elim (Nat.not_succ_le_zero s hdepth)
  | fuel, mu, [], t :: rest, s + 1, hmu, hinv, hdepth => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vwalk_skip_falsified fuel mu t rest hleg hfals] at hdepth
          rw [leftmostLiveFeedAux.eq_def]
          simp [hleg, hfals]
          rw [vevents_skip_falsified fuel mu t rest
            (leftmostLiveFeedAux fuel mu [] rest (s + 1)) hleg hfals]
          exact leftmostLiveFeedAux_sync hsq fuel mu [] rest (s + 1) hmu
            hinv hdepth
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vwalk_stop_satisfied fuel mu t rest hleg hfals' hsat]
              at hdepth
            exact False.elim (Nat.not_succ_le_zero s hdepth)
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vwalk_entry_zero mu t rest hleg hfals' hsat'] at hdepth
                exact False.elim (Nat.not_succ_le_zero s hdepth)
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vwalk_entry_none fuel' mu t rest hleg hfals' hsat'
                      htv] at hdepth
                    exact False.elim (Nat.not_succ_le_zero s hdepth)
                | cons v vs =>
                    cases v with
                    | inl i =>
                        rw [vwalk_entry_pigeon fuel' mu t rest i vs hleg
                          hfals' hsat' htv] at hdepth
                        have hex := exists_live_hole_depth hsq hmu hinv hdepth
                        rcases leftmostLiveDepthHole?_spec_of_exists hex with
                          ⟨a, hsel, hha, hchild⟩
                        rw [leftmostLiveFeedAux.eq_def]
                        simp [hleg, hfals', hsat', htv, hsel]
                        rw [vevents_entry_pigeon_live fuel' mu t rest i vs a
                          (leftmostLiveFeedAux fuel'
                            (compose mu (singleMatching i a)) vs (t :: rest)
                            s)
                          hleg hfals' hsat' htv hha]
                        rw [eventsSteps_enter, eventsSteps_qstep]
                        have hfree : mu i = none :=
                          termVertices_head_pigeon_free mu t i vs htv
                        have hinv' :
                            (freePigeons
                              (compose mu (singleMatching i a))).card =
                              fuel' :=
                          freePigeons_compose_single_card hinv hfree
                        have hmu' : IsMatching
                            (compose mu (singleMatching i a)) :=
                          isMatching_compose_single hmu i a hfree hha
                        have hrec := leftmostLiveFeedAux_sync hsq fuel'
                          (compose mu (singleMatching i a)) vs (t :: rest) s
                          hmu' hinv' hchild
                        constructor
                        · simp [hrec.1]
                        · simp [hrec.2]
                    | inr b =>
                        exact False.elim
                          (absurd htv (termVertices_head_not_hole mu t b vs))
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vwalk_skip_illegal fuel mu t rest hleg'] at hdepth
        rw [leftmostLiveFeedAux.eq_def]
        simp [hleg']
        rw [vevents_skip_illegal fuel mu t rest
          (leftmostLiveFeedAux fuel mu [] rest (s + 1)) hleg']
        exact leftmostLiveFeedAux_sync hsq fuel mu [] rest (s + 1) hmu hinv
          hdepth
  | fuel, mu, v :: vs, D, s + 1, hmu, hinv, hdepth => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vblock_skip_covered fuel mu v vs D hcov] at hdepth
        rw [leftmostLiveFeedAux.eq_def]
        simp [hcov]
        rw [vevents_block_skip_covered fuel mu v vs D
          (leftmostLiveFeedAux fuel mu vs D (s + 1)) hcov]
        exact leftmostLiveFeedAux_sync hsq fuel mu vs D (s + 1) hmu hinv
          hdepth
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vblock_zero mu v vs D hcov'] at hdepth
            exact False.elim (Nat.not_succ_le_zero s hdepth)
        | succ fuel' =>
            cases v with
            | inl i =>
                rw [vblock_query_pigeon fuel' mu i vs D hcov'] at hdepth
                have hex := exists_live_hole_depth hsq hmu hinv hdepth
                rcases leftmostLiveDepthHole?_spec_of_exists hex with
                  ⟨a, hsel, hha, hchild⟩
                rw [leftmostLiveFeedAux.eq_def]
                simp [hcov', hsel]
                rw [vevents_block_pigeon_live fuel' mu i vs D a
                  (leftmostLiveFeedAux fuel'
                    (compose mu (singleMatching i a)) vs D s)
                  hcov' hha]
                rw [eventsSteps_qstep]
                have hfree : mu i = none := by
                  simp only [vertexCoveredB] at hcov'
                  cases hmi : mu i with
                  | none => rfl
                  | some a =>
                      rw [hmi] at hcov'
                      cases hcov'
                have hinv' :
                    (freePigeons (compose mu (singleMatching i a))).card =
                      fuel' :=
                  freePigeons_compose_single_card hinv hfree
                have hmu' : IsMatching (compose mu (singleMatching i a)) :=
                  isMatching_compose_single hmu i a hfree hha
                have hrec := leftmostLiveFeedAux_sync hsq fuel'
                  (compose mu (singleMatching i a)) vs D s hmu' hinv' hchild
                constructor
                · simp [hrec.1]
                · simp [hrec.2]
            | inr b =>
                rw [vblock_query_hole fuel' mu b vs D hcov'] at hdepth
                have hex := exists_live_pigeon_depth hinv hdepth
                rcases leftmostLiveDepthPigeon?_spec_of_exists hex with
                  ⟨q, hsel, hqfree, hchild⟩
                rw [leftmostLiveFeedAux.eq_def]
                simp [hcov', hsel]
                rw [vevents_block_hole_live fuel' mu b vs D q
                  (leftmostLiveFeedAux fuel'
                    (compose mu (singleMatching q b)) vs D s)
                  hcov' hqfree]
                rw [eventsSteps_qstep]
                have hbfree : holeUsed mu b = false := by
                  simpa only [vertexCoveredB] using hcov'
                have hqnone : mu q = none := matching_free_of_isSome_false hqfree
                have hinv' :
                    (freePigeons (compose mu (singleMatching q b))).card =
                      fuel' :=
                  freePigeons_compose_single_card hinv hqnone
                have hmu' : IsMatching (compose mu (singleMatching q b)) :=
                  isMatching_compose_single hmu q b hqnone hbfree
                have hrec := leftmostLiveFeedAux_sync hsq fuel'
                  (compose mu (singleMatching q b)) vs D s hmu' hinv' hchild
                constructor
                · simp [hrec.1]
                · simp [hrec.2]
  termination_by fuel _ pending D t _ _ _ => (fuel, pending.length + D.length)

theorem leftmostLiveFeed_length {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (leftmostLiveFeed rho D t).length = t := by
  unfold canonicalVMDT at ht
  unfold leftmostLiveFeed
  exact (leftmostLiveFeedAux_sync hsq (freePigeons rho).card rho [] D t
    hrho rfl ht).1

theorem leftmostLiveFeed_vtrace_eventsSteps_length {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (eventsSteps (vtrace rho D (leftmostLiveFeed rho D t))).length = t := by
  unfold canonicalVMDT at ht
  unfold leftmostLiveFeed vtrace
  exact (leftmostLiveFeedAux_sync hsq (freePigeons rho).card rho [] D t
    hrho rfl ht).2

/-- Packaged S2188 synchronization: the deterministic feed has length `t`,
and the canonical trace replay against it has exactly `t` query steps. -/
theorem leftmostLiveFeed_sync {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (leftmostLiveFeed rho D t).length = t ∧
      (eventsSteps (vtrace rho D (leftmostLiveFeed rho D t))).length = t :=
  ⟨leftmostLiveFeed_length hsq rho D hrho ht,
    leftmostLiveFeed_vtrace_eventsSteps_length hsq rho D hrho ht⟩

/-! ## S2188 acceptance-name wrappers -/

/-- Public acceptance alias: the deterministic leftmost live deep-path feed. -/
def leftmostLiveDeepFeed {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (t : Nat) : List (Vertex p h) :=
  leftmostLiveFeed rho D t

theorem leftmostLiveDeepFeed_length {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (leftmostLiveDeepFeed rho D t).length = t :=
  leftmostLiveFeed_length hsq rho D hrho ht

/-- Tree-trace synchronization under the acceptance-name feed. -/
theorem leftmostLiveDeepFeed_vtrace_eventsSteps_length {p h : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (eventsSteps (vtrace rho D (leftmostLiveDeepFeed rho D t))).length = t :=
  leftmostLiveFeed_vtrace_eventsSteps_length hsq rho D hrho ht

/-- Packaged tree-trace synchronization under the acceptance-name feed. -/
theorem leftmostLiveDeepFeed_treeTrace_sync {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (leftmostLiveDeepFeed rho D t).length = t ∧
      (eventsSteps (vtrace rho D (leftmostLiveDeepFeed rho D t))).length =
        t :=
  ⟨leftmostLiveDeepFeed_length hsq rho D hrho ht,
    leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht⟩

/-! ## Stage 3: concrete G2 β-code from block σ-marks -/

/-- First-index of a pair in a term (recursive; no competing `BEq`). -/
def termIdx {p h : Nat} : MTerm p h → Fin p × Fin h → Nat
  | [], _ => 0
  | x :: xs, e => if x = e then 0 else termIdx xs e + 1

private theorem termIdx_lt_of_mem {p h : Nat} :
    ∀ (t : MTerm p h) (e : Fin p × Fin h), e ∈ t → termIdx t e < t.length
  | x :: xs, e, he => by
      unfold termIdx
      by_cases hx : x = e
      · simp only [hx, ↓reduceIte]
        exact Nat.zero_lt_succ _
      · simp only [hx, ↓reduceIte]
        have he' : e ∈ xs := by
          cases he with
          | head => exact absurd rfl hx
          | tail _ h => exact h
        exact Nat.succ_lt_succ (termIdx_lt_of_mem xs e he')

private theorem termIdx_get {p h : Nat} :
    ∀ (t : MTerm p h) (e : Fin p × Fin h) (he : e ∈ t),
      t[termIdx t e]'(termIdx_lt_of_mem t e he) = e
  | x :: xs, e, he => by
      unfold termIdx
      by_cases hx : x = e
      · simp only [hx, ↓reduceIte, List.getElem_cons_zero]
      · simp only [hx, ↓reduceIte]
        have he' : e ∈ xs := by
          cases he with
          | head => exact absurd rfl hx
          | tail _ h => exact h
        simpa [List.getElem_cons_succ] using termIdx_get xs e he'

/-- Position of a pair inside a term as a mark in `Fin w`, if present and
in range. -/
def termMarkPos {p h w : Nat} (t : MTerm p h) (e : Fin p × Fin h) :
    Option (Fin w) :=
  if hmem : e ∈ t then
    if hw : termIdx t e < w then some ⟨termIdx t e, hw⟩ else none
  else
    none

/-- β-marks of a σ-list: positions of its pairs inside the entered term. -/
def sigmaMarks {p h w : Nat} (t : MTerm p h) (sig : List (Fin p × Fin h)) :
    Finset (Fin w) :=
  (sig.filterMap (termMarkPos (w := w) t)).toFinset

/-- Zip a block list with the encode's per-block σ rule into β-vectors. -/
def blockSigmasBeta {p h w : Nat} :
    List (VBlock p h) → List (Finset (Fin w))
  | [] => []
  | [B] => [sigmaMarks B.term (sigmaTrunc B)]
  | B :: Bs => sigmaMarks B.term (sigmaFull B) :: blockSigmasBeta Bs

/-- **G2**: the β-code of a trace — one position-set per σ-block. -/
def traceBeta {p h w : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (feed : List (Vertex p h)) : List (Finset (Fin w)) :=
  blockSigmasBeta (blocksOf (vtrace rho D feed))

/-- G2 along the deterministic deep feed. -/
def traceBetaDeep {p h w : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (t : Nat) : List (Finset (Fin w)) :=
  traceBeta rho D (leftmostLiveDeepFeed rho D t)

private theorem termMarkPos_of_mem {p h w : Nat} (t : MTerm p h)
    (e : Fin p × Fin h) (he : e ∈ t) (hw : t.length ≤ w) :
    ∃ i : Fin w, termMarkPos (w := w) t e = some i := by
  unfold termMarkPos
  simp only [he, ↓reduceDIte]
  have hlt := termIdx_lt_of_mem t e he
  have hltw : termIdx t e < w := Nat.lt_of_lt_of_le hlt hw
  simp [hltw]

private theorem termMarkPos_inj {p h w : Nat} (t : MTerm p h)
    (e f : Fin p × Fin h) (he : e ∈ t) (hf : f ∈ t) (hw : t.length ≤ w)
    {i : Fin w}
    (he' : termMarkPos (w := w) t e = some i)
    (hf' : termMarkPos (w := w) t f = some i) : e = f := by
  unfold termMarkPos at he' hf'
  simp only [he, hf, ↓reduceDIte] at he' hf'
  have hle : termIdx t e < w := by
    by_cases h : termIdx t e < w
    · exact h
    · simp [h] at he'
  have hlf : termIdx t f < w := by
    by_cases h : termIdx t f < w
    · exact h
    · simp [h] at hf'
  simp only [hle, hlf, ↓reduceDIte] at he' hf'
  have hie : (⟨termIdx t e, hle⟩ : Fin w) = i := by injection he'
  have hif : (⟨termIdx t f, hlf⟩ : Fin w) = i := by injection hf'
  have hidx : termIdx t e = termIdx t f := by
    have := congrArg Fin.val (hie.trans hif.symm)
    simpa using this
  have heget := termIdx_get t e he
  have hfget := termIdx_get t f hf
  have : t[termIdx t e]'(termIdx_lt_of_mem t e he) =
      t[termIdx t f]'(termIdx_lt_of_mem t f hf) := by
    simp only [hidx]
  exact heget.symm.trans (this.trans hfget)

private theorem sigmaMarks_card {p h w : Nat} (t : MTerm p h)
    (sig : List (Fin p × Fin h)) (hnd : sig.Nodup)
    (hm : ∀ e ∈ sig, e ∈ t) (hw : t.length ≤ w) :
    (sigmaMarks (w := w) t sig).card = sig.length := by
  unfold sigmaMarks
  induction sig with
  | nil => simp
  | cons e es ih =>
      have he : e ∈ t := hm e (List.mem_cons_self _ _)
      rcases termMarkPos_of_mem t e he hw with ⟨i, hi⟩
      have hnd' : es.Nodup := (List.nodup_cons.mp hnd).2
      have hnotin : e ∉ es := (List.nodup_cons.mp hnd).1
      have ih' := ih hnd' (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      have hfm :
          (e :: es).filterMap (termMarkPos (w := w) t) =
            i :: es.filterMap (termMarkPos (w := w) t) := by
        simp [List.filterMap_cons, hi]
      rw [hfm]
      have hinj :
          i ∉ (es.filterMap (termMarkPos (w := w) t)).toFinset := by
        intro hi'
        rw [List.mem_toFinset, List.mem_filterMap] at hi'
        rcases hi' with ⟨f, hf, hfi⟩
        have hfmem : f ∈ t := hm f (List.mem_cons_of_mem _ hf)
        have heq := termMarkPos_inj t e f he hfmem hw hi hfi
        exact hnotin (heq ▸ hf)
      have hcard := Finset.card_insert_of_not_mem (s :=
        (es.filterMap (termMarkPos (w := w) t)).toFinset) hinj
      rw [List.toFinset_cons, hcard, ih']
      rfl

private theorem sigmaFull_mem_term {p h : Nat} (B : VBlock p h)
    (e : Fin p × Fin h) (he : e ∈ sigmaFull B) : e ∈ B.term :=
  ((mem_sigmaFull B e).mp he).1

private theorem sigmaTrunc_mem_term {p h : Nat} (B : VBlock p h)
    (e : Fin p × Fin h) (he : e ∈ sigmaTrunc B) : e ∈ B.term :=
  sigmaFull_mem_term B e (sigmaTrunc_subset_sigmaFull B e he)

private theorem sigmaFull_ne_nil_of_unsat {p h : Nat} (B : VBlock p h)
    (hfals : termFalsifiedB B.entry B.term = false)
    (hsat : termSatisfiedB B.entry B.term = false) :
    sigmaFull B ≠ [] := by
  have hex : ∃ e ∈ B.term, pairSatB B.entry e = false := by
    by_contra hnone
    push_neg at hnone
    have hall : termSatisfiedB B.entry B.term = true := by
      unfold termSatisfiedB
      exact List.all_eq_true.mpr fun e he =>
        Bool.eq_true_of_not_eq_false (hnone e he)
    exact absurd (hsat.symm.trans hall) Bool.false_ne_true
  rcases hex with ⟨e, he, hns⟩
  have hnfals : pairFalsB B.entry e = false := by
    unfold termFalsifiedB at hfals
    by_contra hpf
    have : B.term.any (pairFalsB B.entry) = true :=
      List.any_eq_true.mpr ⟨e, he, Bool.eq_true_of_not_eq_false hpf⟩
    rw [this] at hfals
    cases hfals
  have hunres : pairUnresolvedB B.entry e = true := by
    have htrich := pair_status_trichotomy B.entry e
    simp only [hns, hnfals, Bool.or_false, Bool.false_or] at htrich
    exact htrich
  intro hnil
  have : e ∈ sigmaFull B := (mem_sigmaFull B e).mpr ⟨he, hunres⟩
  rw [hnil] at this
  cases this

/-- Event lists where every `enter` is immediately followed by a `qstep`. -/
def enterQstepWF {p h : Nat} : List (VEvent p h) → Prop
  | [] => True
  | .qstep _ :: rest => enterQstepWF rest
  | .enter _ _ :: .qstep _ :: rest => enterQstepWF rest
  | .enter _ _ :: _ => False

private theorem enterQstepWF_afterSteps {p h : Nat} :
    ∀ es : List (VEvent p h), enterQstepWF es → enterQstepWF (afterSteps es)
  | [], h => h
  | .qstep _ :: rest, h => by
      simp only [afterSteps]
      exact enterQstepWF_afterSteps rest h
  | .enter _ _ :: .qstep _ :: rest, h => by
      simp only [afterSteps]
      exact h
  | .enter _ _ :: [], h => by cases h
  | .enter _ _ :: .enter _ _ :: _, h => by cases h
  termination_by es => es.length

private theorem blocksOf_steps_ne_nil_of_WF {p h : Nat} :
    ∀ (es : List (VEvent p h)),
      ∀ (B : VBlock p h), enterQstepWF es → B ∈ blocksOf es → B.steps ≠ [] := by
  intro es
  induction' hlen : es.length using Nat.strong_induction_on with n ih generalizing es
  intro B hwf hB
  match es with
  | [] =>
      rw [blocksOf_nil] at hB; cases hB
  | .qstep st :: rest =>
      rw [blocksOf_qstep] at hB
      have hlen' : rest.length < n := by
        rw [← hlen]; exact Nat.lt_succ_self _
      exact ih rest.length hlen' rest rfl B hwf hB
  | .enter t ent :: rest =>
      match rest, hwf with
      | .qstep st :: rest', hwf' =>
          rw [blocksOf_enter] at hB
          cases hB with
          | head => intro hnil; simp [stepsPrefix] at hnil
          | tail _ hB' =>
              have hwf2 :
                  enterQstepWF (afterSteps (.qstep st :: rest')) :=
                enterQstepWF_afterSteps _ hwf'
              simp only [afterSteps] at hB' hwf2
              have hlen' : (afterSteps rest').length < n := by
                have hle := afterSteps_length_le (p := p) (h := h) rest'
                have hn : n = rest'.length + 2 := by
                  cases hlen; rfl
                omega
              exact ih _ hlen' (afterSteps rest') rfl B hwf2 hB'
      | [], hwf' => cases hwf'
      | .enter _ _ :: _, hwf' => cases hwf'

private theorem vevents_enterQstepWF {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)),
      enterQstepWF (vevents fuel mu pending D feed)
  | _, _, [], [], _ => by rw [vevents_nil]; trivial
  | fuel, mu, [], t :: rest, feed => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals]
          exact vevents_enterQstepWF fuel mu [] rest feed
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals' hsat]
            trivial
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat']
                trivial
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t rest feed hleg
                      hfals' hsat' htv]
                    trivial
                | cons v vs =>
                    cases v with
                    | inl i =>
                        cases feed with
                        | nil =>
                            rw [vevents_entry_feed_nil fuel' mu t rest i vs
                              hleg hfals' hsat' htv]
                            trivial
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents_entry_feed_illkind fuel' mu t
                                  rest i vs q fs hleg hfals' hsat' htv]
                                trivial
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv hha]
                                  trivial
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv hha']
                                  exact vevents_enterQstepWF fuel'
                                    (compose mu (singleMatching i a)) vs
                                    (t :: rest) fs
                    | inr b =>
                        exact False.elim
                          (absurd htv (termVertices_head_not_hole mu t b vs))
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg']
        exact vevents_enterQstepWF fuel mu [] rest feed
  | fuel, mu, v :: vs, D, feed => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov]
        exact vevents_enterQstepWF fuel mu vs D feed
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov']; trivial
        | succ fuel' =>
            cases v with
            | inl i =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov']; trivial
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents_block_pigeon_illkind fuel' mu i vs D q fs
                          hcov']; trivial
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents_block_pigeon_dead fuel' mu i vs D a fs
                            hcov' hha]; trivial
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a fs
                            hcov' hha']
                          exact vevents_enterQstepWF fuel'
                            (compose mu (singleMatching i a)) vs D fs
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov']; trivial
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents_block_hole_illkind fuel' mu b vs D a fs
                          hcov']; trivial
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents_block_hole_dead fuel' mu b vs D q fs
                            hcov' hq]; trivial
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq']
                          exact vevents_enterQstepWF fuel'
                            (compose mu (singleMatching q b)) vs D fs
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

private theorem blocksOf_vevents_steps_ne_nil {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (B : VBlock p h)
    (hB : B ∈ blocksOf (vevents fuel mu pending D feed)) : B.steps ≠ [] :=
  blocksOf_steps_ne_nil_of_WF _ B (vevents_enterQstepWF fuel mu pending D feed)
    hB

private theorem blockSigmasBeta_codeSize {p h w : Nat} :
    ∀ (Bs : List (VBlock p h)),
      (∀ B ∈ Bs, B.term.length ≤ w) →
      codeSize (blockSigmasBeta (w := w) Bs) =
        ((blockSigmas Bs).join).length
  | [], _ => by simp [blockSigmasBeta, blockSigmas, codeSize]
  | [B], hw => by
      have hsz := sigmaMarks_card B.term (sigmaTrunc B)
        ((sigmaFull_nodup B).filter _)
        (fun e he => sigmaTrunc_mem_term B e he)
        (hw B (List.mem_singleton.mpr rfl))
      simpa [blockSigmasBeta, blockSigmas, codeSize] using hsz
  | B :: B' :: Bs, hw => by
      have h1 := sigmaMarks_card B.term (sigmaFull B) (sigmaFull_nodup B)
        (fun e he => sigmaFull_mem_term B e he)
        (hw B (List.mem_cons_self _ _))
      have h2 := blockSigmasBeta_codeSize (B' :: Bs)
        (fun b hb => hw b (List.mem_cons_of_mem _ hb))
      simpa [blockSigmasBeta, blockSigmas, codeSize, List.length_append,
        h1] using h2

private theorem blockSigmasBeta_wellFormed {p h w : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h)) :
    ∀ (Bs : List (VBlock p h)),
      (∀ B ∈ Bs, B ∈ blocksOf (vevents fuel mu [] D feed)) →
      (∀ B ∈ Bs, B.term.length ≤ w) →
      (∀ b ∈ blockSigmasBeta (w := w) Bs, Finset.Nonempty b)
  | [], _, _ => by intro b hb; cases hb
  | [B], hmem, hw => by
      intro b hb
      simp only [blockSigmasBeta, List.mem_singleton] at hb
      subst hb
      have hB := hmem B (List.mem_singleton.mpr rfl)
      have hst := blocksOf_vevents_steps_ne_nil fuel mu [] D feed B hB
      have hlow := steps_length_le_two_sigmaTrunc B
        (blocksOf_steps_vertex_mem_frozen fuel mu [] D feed B hB)
        (blocksOf_steps_labels_pairwise fuel mu [] D feed B hB)
      have hpos : 0 < (sigmaTrunc B).length := by
        have : 0 < B.steps.length := List.length_pos_of_ne_nil hst
        omega
      have hcard := sigmaMarks_card B.term (sigmaTrunc B)
        ((sigmaFull_nodup B).filter _)
        (fun e he => sigmaTrunc_mem_term B e he)
        (hw B (List.mem_singleton.mpr rfl))
      exact Finset.card_pos.mp (by rw [hcard]; exact hpos)
  | B :: B' :: Bs, hmem, hw => by
      intro b hb
      simp only [blockSigmasBeta, List.mem_cons] at hb
      cases hb with
      | inl hbe =>
          subst hbe
          have hB := hmem B (List.mem_cons_self _ _)
          have hspec := blocksOf_entry_spec fuel mu [] D feed B hB
          have hne := sigmaFull_ne_nil_of_unsat B hspec.2.2.1 hspec.2.2.2
          have hcard := sigmaMarks_card B.term (sigmaFull B)
            (sigmaFull_nodup B)
            (fun e he => sigmaFull_mem_term B e he)
            (hw B (List.mem_cons_self _ _))
          exact Finset.card_pos.mp (by
            rw [hcard]; exact List.length_pos_of_ne_nil hne)
      | inr hb' =>
          exact blockSigmasBeta_wellFormed fuel mu D feed (B' :: Bs)
            (fun b' hb2 => hmem b' (List.mem_cons_of_mem _ hb2))
            (fun b' hb2 => hw b' (List.mem_cons_of_mem _ hb2)) b hb'

private theorem blocksOf_term_mem_D {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hmu : IsMatching mu) (B : VBlock p h)
    (hB : B ∈ blocksOf (vevents fuel mu [] D feed)) : B.term ∈ D := by
  rcases blocksOf_entered_first fuel mu [] D feed hmu B hB with
    ⟨pre, suf, hD, _⟩
  rw [hD]
  exact List.mem_append_right _ (List.mem_cons_self _ _)

/-- **Stage 3**: G2 is well-formed and has star-count equal to the encode's
σ-join length `j`, under a uniform term-width bound. -/
theorem traceBeta_wellFormed_codeSize {p h w : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho) (hw : ∀ t ∈ D, t.length ≤ w) :
    (∀ b ∈ traceBeta (w := w) rho D feed, Finset.Nonempty b) ∧
      codeSize (traceBeta (w := w) rho D feed) =
        ((blockSigmas (blocksOf (vtrace rho D feed))).join).length := by
  unfold traceBeta vtrace
  constructor
  · intro b hb
    refine blockSigmasBeta_wellFormed (freePigeons rho).card rho D feed
      (blocksOf (vevents (freePigeons rho).card rho [] D feed))
      (fun B hB => hB) ?_ b hb
    intro B hB
    exact hw B.term
      (blocksOf_term_mem_D (freePigeons rho).card rho D feed hrho B hB)
  · refine blockSigmasBeta_codeSize
      (blocksOf (vevents (freePigeons rho).card rho [] D feed)) ?_
    intro B hB
    exact hw B.term
      (blocksOf_term_mem_D (freePigeons rho).card rho D feed hrho B hB)

/-- Stage 3 under the deterministic deep feed. -/
theorem traceBetaDeep_wellFormed_codeSize {p h w : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (_ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    (∀ b ∈ traceBetaDeep (w := w) rho D t, Finset.Nonempty b) ∧
      codeSize (traceBetaDeep (w := w) rho D t) =
        ((blockSigmas (blocksOf
          (vtrace rho D (leftmostLiveDeepFeed rho D t)))).join).length := by
  unfold traceBetaDeep
  exact traceBeta_wellFormed_codeSize rho D (leftmostLiveDeepFeed rho D t)
    hrho hw

/-! ## Stage 4: concrete G3 answer codes in `[2ℓ]` -/

/-- Canonical free-vertex enumeration: free pigeons then free holes. -/
def freeVertexList {p h : Nat} (mu : MatchingMap p h) :
    List (Vertex p h) :=
  ((freePigeons mu).sort (· ≤ ·)).map Sum.inl ++
    ((freeHoles mu).sort (· ≤ ·)).map Sum.inr

theorem freeVertexList_length {p h : Nat} (mu : MatchingMap p h) :
    (freeVertexList mu).length =
      (freePigeons mu).card + (freeHoles mu).card := by
  unfold freeVertexList
  rw [List.length_append, List.length_map, List.length_map,
    Finset.length_sort, Finset.length_sort]

theorem freeVertexList_length_square {p h : Nat} (hsq : p = h)
    {mu : MatchingMap p h} (hmu : IsMatching mu) {ell : Nat}
    (hell : (freePigeons mu).card = ell) :
    (freeVertexList mu).length = 2 * ell := by
  rw [freeVertexList_length, hell, card_freeHoles_square hsq hmu hell]
  omega

theorem mem_freeVertexList {p h : Nat} (mu : MatchingMap p h)
    (v : Vertex p h) :
    v ∈ freeVertexList mu ↔ v ∈ freeVertices mu := by
  unfold freeVertexList freeVertices
  cases v with
  | inl i =>
      simp only [List.mem_append, List.mem_map, Finset.mem_union,
        Finset.mem_image]
      constructor
      · rintro (⟨j, hj, hji⟩ | ⟨_, _, hb⟩)
        · left
          exact ⟨j, (Finset.mem_sort (· ≤ ·)).mp hj, hji⟩
        · cases hb
      · rintro (⟨j, hj, hji⟩ | ⟨_, _, hb⟩)
        · left
          exact ⟨j, (Finset.mem_sort (· ≤ ·)).mpr hj, hji⟩
        · cases hb
  | inr b =>
      simp only [List.mem_append, List.mem_map, Finset.mem_union,
        Finset.mem_image]
      constructor
      · rintro (⟨_, _, hj⟩ | ⟨c, hc, hcb⟩)
        · cases hj
        · right
          exact ⟨c, (Finset.mem_sort (· ≤ ·)).mp hc, hcb⟩
      · rintro (⟨_, _, hj⟩ | ⟨c, hc, hcb⟩)
        · cases hj
        · right
          exact ⟨c, (Finset.mem_sort (· ≤ ·)).mpr hc, hcb⟩

/-- Reconstruct the pre-extension base from `G1` and the decoded sigma list.
This is the answer namespace's UF-style replay state: unlike the original G3
definition, it does not take the unknown base `rho` as an input. -/
def replayBase {p h : Nat} (G1 : MatchingMap p h)
    (sigma : List (Fin p × Fin h)) : MatchingMap p h :=
  fun i => if pairsToMatching sigma i = none then G1 i else none

/-- Canonical answer namespace computed from replay data only. -/
def replayVertexList {p h : Nat} (G1 : MatchingMap p h)
    (sigma : List (Fin p × Fin h)) : List (Vertex p h) :=
  freeVertexList (replayBase G1 sigma)

/-- On an encode image, replay reconstructs the original base pointwise. -/
theorem replayBase_encodeExt {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h)) :
    replayBase (encodeExt rho D feed)
        (blockSigmas (blocksOf (vtrace rho D feed))).join = rho := by
  funext i
  exact (PHPMatchingEncodeDisposal.encodeExt_recover_base rho D feed i).symm

/-- Consequently the corrected answer namespace agrees with the old
free-base enumeration on every encode image. -/
theorem replayVertexList_encodeExt {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h)) :
    replayVertexList (encodeExt rho D feed)
        (blockSigmas (blocksOf (vtrace rho D feed))).join =
      freeVertexList rho := by
  simp only [replayVertexList, replayBase_encodeExt]

/-- First-index of a vertex in a list (recursive; no competing `BEq`). -/
def vertexIdx {p h : Nat} : List (Vertex p h) → Vertex p h → Nat
  | [], _ => 0
  | x :: xs, v => if x = v then 0 else vertexIdx xs v + 1

private theorem vertexIdx_lt_of_mem {p h : Nat} :
    ∀ (l : List (Vertex p h)) (v : Vertex p h), v ∈ l →
      vertexIdx l v < l.length
  | x :: xs, v, hv => by
      unfold vertexIdx
      by_cases hx : x = v
      · simp only [hx, ↓reduceIte]
        exact Nat.zero_lt_succ _
      · simp only [hx, ↓reduceIte]
        have hv' : v ∈ xs := by
          cases hv with
          | head => exact absurd rfl hx
          | tail _ h => exact h
        exact Nat.succ_lt_succ (vertexIdx_lt_of_mem xs v hv')

/-- Looking up a present vertex at its first index returns that vertex. -/
theorem vertexIdx_get {p h : Nat} :
    ∀ (l : List (Vertex p h)) (v : Vertex p h) (hv : v ∈ l),
      l[vertexIdx l v]'(vertexIdx_lt_of_mem l v hv) = v
  | x :: xs, v, hv => by
      unfold vertexIdx
      by_cases hx : x = v
      · simp only [hx, ↓reduceIte, List.getElem_cons_zero]
      · simp only [hx, ↓reduceIte]
        have hv' : v ∈ xs := by
          cases hv with
          | head => exact absurd rfl hx
          | tail _ h => exact h
        simpa [List.getElem_cons_succ] using vertexIdx_get xs v hv'

/-- Encode one free vertex as its index in the square free-vertex list. -/
def freeVertexCode {p h ell : Nat} (mu : MatchingMap p h)
    (hsq : p = h) (hmu : IsMatching mu)
    (hell : (freePigeons mu).card = ell) (v : Vertex p h)
    (hv : v ∈ freeVertices mu) : Fin (2 * ell) :=
  ⟨vertexIdx (freeVertexList mu) v, by
    have hlen := freeVertexList_length_square hsq hmu hell
    have hmem : v ∈ freeVertexList mu := (mem_freeVertexList mu v).mpr hv
    have hlt := vertexIdx_lt_of_mem (freeVertexList mu) v hmem
    omega⟩

/-- Encode in the corrected namespace, which is computed from `G1` and a
decoded sigma list rather than from the unknown base. -/
def replayVertexCode {p h ell : Nat} (G1 : MatchingMap p h)
    (sigma : List (Fin p × Fin h))
    (hlen : (replayVertexList G1 sigma).length = 2 * ell)
    (v : Vertex p h) (hv : v ∈ replayVertexList G1 sigma) : Fin (2 * ell) :=
  ⟨vertexIdx (replayVertexList G1 sigma) v, by
    have hlt := vertexIdx_lt_of_mem (replayVertexList G1 sigma) v hv
    omega⟩

/-- Decode one corrected-namespace symbol. -/
def replayVertexDecode {p h ell : Nat} (G1 : MatchingMap p h)
    (sigma : List (Fin p × Fin h))
    (hlen : (replayVertexList G1 sigma).length = 2 * ell)
    (c : Fin (2 * ell)) : Vertex p h :=
  (replayVertexList G1 sigma).get ⟨c.val, by omega⟩

/-- One-symbol roundtrip for the corrected answer namespace. -/
theorem replayVertexDecode_replayVertexCode {p h ell : Nat}
    (G1 : MatchingMap p h) (sigma : List (Fin p × Fin h))
    (hlen : (replayVertexList G1 sigma).length = 2 * ell)
    (v : Vertex p h) (hv : v ∈ replayVertexList G1 sigma) :
    replayVertexDecode G1 sigma hlen
        (replayVertexCode G1 sigma hlen v hv) = v := by
  unfold replayVertexDecode replayVertexCode
  exact vertexIdx_get (replayVertexList G1 sigma) v hv

/-- **G3**: answer stream packaged as `Fin t → Fin (2ℓ)`. -/
def traceAnswerCode {p h ell t : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (hsq : p = h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (feed : List (Vertex p h))
    (hlen : (answerStream (vtrace rho D feed)).length = t) :
    Fin t → Fin (2 * ell) :=
  let sigma := (blockSigmas (blocksOf (vtrace rho D feed))).join
  let G1 := encodeExt rho D feed
  have hns : replayVertexList G1 sigma = freeVertexList rho :=
    replayVertexList_encodeExt rho D feed
  have hlist : (replayVertexList G1 sigma).length = 2 * ell := by
    rw [hns]
    exact freeVertexList_length_square hsq hrho hell
  fun i =>
    replayVertexCode G1 sigma hlist
      ((answerStream (vtrace rho D feed)).get ⟨i.val, by
        rw [hlen]; exact i.isLt⟩)
      (by
        rw [hns]
        apply (mem_freeVertexList rho _).mpr
        have hvmem :
            (answerStream (vtrace rho D feed)).get
              ⟨i.val, by rw [hlen]; exact i.isLt⟩ ∈
              answerStream (vtrace rho D feed) :=
          List.get_mem _ _ _
        have hvmem' :
            (answerStream (vtrace rho D feed)).get
              ⟨i.val, by rw [hlen]; exact i.isLt⟩ ∈
              answerStream
                (vevents (freePigeons rho).card rho [] D feed) := by
          simpa [vtrace] using hvmem
        exact answerStream_mem_freeVertices (freePigeons rho).card rho [] D
          feed _ hvmem')

/-- G3 along the deterministic deep feed under tree-trace sync. -/
def traceAnswerCodeDeep {p h ell t : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    Fin t → Fin (2 * ell) :=
  traceAnswerCode rho D hsq hrho hell (leftmostLiveDeepFeed rho D t)
    (by
      rw [answerStream_length]
      exact leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht)

/-! ## Stage 5: free-pigeon drop on the extension G1 -/

private theorem pairwise_PairDisjoint_nodup {p h : Nat} :
    ∀ {l : List (Fin p × Fin h)}, List.Pairwise PairDisjoint l → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hpd => by
      rw [List.nodup_cons]
      exact ⟨fun hx => ((List.pairwise_cons.mp hpd).1 x hx).1 rfl,
        pairwise_PairDisjoint_nodup (List.pairwise_cons.mp hpd).2⟩

private theorem pairsToMatching_none_iff {p h : Nat} :
    ∀ (l : List (Fin p × Fin h)) (i : Fin p),
      pairsToMatching l i = none ↔ i ∉ (l.map Prod.fst).toFinset
  | [], i => by
      constructor
      · intro; simp
      · intro; rfl
  | e :: es, i => by
      rw [show pairsToMatching (e :: es) =
        compose (singleMatching e.1 e.2) (pairsToMatching es) from rfl]
      by_cases hie : i = e.1
      · constructor
        · intro hi
          have hsome : singleMatching e.1 e.2 i = some e.2 := by
            unfold singleMatching; rw [if_pos hie]
          rw [compose_fixed_left _ _ i e.2 hsome] at hi
          cases hi
        · intro hi
          have : i ∈ (List.map Prod.fst (e :: es)).toFinset := by
            simp [List.map_cons, List.toFinset_cons, hie]
          exact absurd this hi
      · have hnone : singleMatching e.1 e.2 i = none := by
          unfold singleMatching; rw [if_neg hie]
        constructor
        · intro hi
          rw [compose_free_left _ _ i hnone] at hi
          have hrest := (pairsToMatching_none_iff es i).mp hi
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert,
            not_or]
          exact ⟨hie, hrest⟩
        · intro hi
          rw [compose_free_left _ _ i hnone]
          apply (pairsToMatching_none_iff es i).mpr
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert,
            not_or] at hi
          exact hi.2

private theorem sigma_pigeons_card {p h : Nat}
    (l : List (Fin p × Fin h)) (hpd : List.Pairwise PairDisjoint l) :
    ((l.map Prod.fst).toFinset).card = l.length := by
  have hnd := pairwise_PairDisjoint_nodup hpd
  have hmap : (l.map Prod.fst).Nodup := by
    refine List.Nodup.map_on ?_ hnd
    intro x hx y hy hxy
    by_contra hne
    exact (hpd.forall pairDisjoint_symm hx hy hne).1 hxy
  rw [List.toFinset_card_of_nodup hmap, List.length_map]

/-- **Stage 5**: the extension drops exactly `j` free pigeons when the
σ-join has length `j` and the base has `ell` free pigeons. -/
theorem encodeExt_freePigeons_card {p h ell j : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hell : (freePigeons rho).card = ell)
    (hj : ((blockSigmas (blocksOf (vtrace rho D feed))).join).length = j) :
    (freePigeons (encodeExt rho D feed)).card = ell - j := by
  let sig := (blockSigmas (blocksOf (vtrace rho D feed))).join
  have hsig : sig =
      (blockSigmas (blocksOf
        (vevents (freePigeons rho).card rho [] D feed))).join := rfl
  have hpd : List.Pairwise PairDisjoint sig := by
    rw [hsig]
    exact blockSigmas_join_pairwise (freePigeons rho).card rho [] D feed
  have hj' : sig.length = j := hj
  let T : Finset (Fin p) := (sig.map Prod.fst).toFinset
  have hTcard : T.card = j := by
    change ((sig.map Prod.fst).toFinset).card = j
    rw [sigma_pigeons_card sig hpd, hj']
  have hT : ∀ i : Fin p, pairsToMatching sig i = none ↔ i ∉ T :=
    fun i => pairsToMatching_none_iff sig i
  have hTfree : T ⊆ freePigeons rho := by
    intro i hi
    rw [List.mem_toFinset, List.mem_map] at hi
    rcases hi with ⟨e, he, hei⟩
    have hfr :=
      blockSigmas_join_fresh (freePigeons rho).card rho [] D feed e
        (by rw [← hsig]; exact he)
    rw [mem_freePigeons, ← hei]
    exact hfr.1
  unfold encodeExt
  have hdrop := freePigeons_compose_card rho (pairsToMatching sig) T hT hTfree
  simpa [sig] using (by rw [hdrop, hell, hTcard] : (freePigeons
    (compose rho (pairsToMatching sig))).card = ell - j)

/-! ## Stage 6: packaged deterministic encodeMatch -/

/-- Graded encode packet: G1 extension, G2 β-code, G3 answer codes, star
count `j`. -/
structure MatchEncode (p h w t ell : Nat) where
  G1 : MatchingMap p h
  G2 : List (Finset (Fin w))
  G3 : Fin t → Fin (2 * ell)
  j : Nat

/-- **Stage 6**: total deterministic encode from a square hole-injective
base with `ell` free pigeons and depth at least `t`, under term-width `w`.
Uses the leftmost live deep feed; inputs may come from a depth hypothesis
(e.g. bad-matching membership) or any other proof of the depth bound. -/
def encodeMatch {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (_hw : ∀ term ∈ D, term.length ≤ w) : MatchEncode p h w t ell where
  G1 := encodeExt rho D (leftmostLiveDeepFeed rho D t)
  G2 := traceBetaDeep (w := w) rho D t
  G3 := traceAnswerCodeDeep hsq rho D hrho hell ht
  j := codeSize (traceBetaDeep (w := w) rho D t)

/-- The packaged encode lands in the graded code family shape consumed by
`mcode_answers_family_card_le`: well-formed nonempty β-blocks and
`codeSize G2 = j`. -/
theorem encodeMatch_mem_gradedCode {p h w t ell : Nat}
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (hsq : p = h) (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let code := encodeMatch hsq rho D hrho hell ht hw
    (∀ b ∈ code.G2, Finset.Nonempty b) ∧ codeSize code.G2 = code.j := by
  intro code
  have hβ := traceBetaDeep_wellFormed_codeSize rho D hrho ht hw
  exact ⟨hβ.1, rfl⟩

/-- Free-pigeon drop packaged through `encodeMatch`. -/
theorem encodeMatch_freePigeons_card {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let code := encodeMatch hsq rho D hrho hell ht hw
    (freePigeons code.G1).card = ell - code.j := by
  intro code
  have hβ := traceBetaDeep_wellFormed_codeSize rho D hrho ht hw
  simpa [encodeMatch] using
    encodeExt_freePigeons_card rho D (leftmostLiveDeepFeed rho D t) hell
      hβ.2.symm

/-- Bad-matching convenience: depth hyp from `vbadMatchings` at level
`t - 1` (packet `> t-1` yields `t ≤ depth` when `0 < t`). -/
theorem encodeMatch_of_vbad {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (_htpos : 0 < t)
    (hbad : rho ∈ vbadMatchings D (t - 1) ell)
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let hmem := (mem_vbadMatchings D (t - 1) ell rho).mp hbad
    let ht : t ≤ vmdtDepth (canonicalVMDT D rho) :=
      Nat.le_of_pred_lt hmem.2
    let code := encodeMatch hsq rho D hmem.1.1 hmem.1.2 ht hw
    (∀ b ∈ code.G2, Finset.Nonempty b) ∧ codeSize code.G2 = code.j := by
  intro hmem ht code
  exact encodeMatch_mem_gradedCode rho D hmem.1.1 hmem.1.2 hsq ht hw

end PHPMatchingDeterministicEncode
end PvNP
