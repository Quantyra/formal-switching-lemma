import PvNP.PHPMatchingAnswerTransport

/-!
# GA-3b deterministic trace feed (S2188)

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

end PHPMatchingDeterministicEncode
end PvNP
