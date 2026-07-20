import PvNP.PHPMatchingEncodeDisposal

/-!
# GA-3 Stage 4: the path-answer transport (S2187)

Final formal stage of the GA-3 extension-encode rung (S2187 story): pin
3.0 in its amended form, and the remaining pin 3.6 riders as theorems.

* **One entry per walked pair, near endpoint replay-inferred**
  (`stepAnswer`, `vevents_feed_recoverable`): each query step determines
  its consumed answer — a pigeon query's answer is the far hole, a hole
  query's the far pigeon — and the trace's consumed feed prefix is
  exactly the steps' answer stream. The near endpoint is never coded:
  query labels are walk-state data (`blocksOf_steps_vertex_mem_frozen`),
  so the answer stream is the entire per-pair cost, one name per walked
  pair (`answerStream_length`).
* **The alphabet is the free-vertex namespace** (`stepAnswer_fresh`,
  `answerStream_mem_freeVertices`): every answer names a vertex free in
  the trace's base matching — pulled back from the walk's dead-arm
  conditions through the already-proved pair freshness.
* **The namespace cardinality** (`freeVertices_card`,
  `freeVertices_card_square`): in general the free-vertex namespace has
  exactly (free pigeons + free holes) names — the L2 rider stated as a
  theorem, with UF's `2ℓ+1` the rectangular `(n+1)/n` instance — and on
  square hole-injective instances with `ℓ` free pigeons it has exactly
  `2ℓ` names (`card_freeHoles_square`: matched pigeons biject with used
  holes, so free pigeons and free holes balance). This is the `[2ℓ]`
  alphabet consumed abstractly by Stage 2's graded bound, and the
  free-VERTEX answer cost is the disclosed L3 constant-factor exceedance
  of the packet menu's free-hole count.

The kernel-pinned consumed-tree divergence witness required by pin 3.0
(`walk_vertex_depth_divergence`, companion to
`walk_boolean_depth1_divergence`) was delivered at Stage 0 and stands.

Deterministic bookkeeping and finite counting only. No injectivity claim
(GA-4), no bad-set cardinality bound (GA-5), no probability statement,
not a switching lemma, not Gate A closure, not Frege/PHP, NP/circuit, or
P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingAnswerTransport

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode

/-! ## The answer of a step (the far endpoint) -/

/-- The answer a query step consumed: a pigeon query was answered by its
pair's hole, a hole query by its pair's pigeon. -/
def stepAnswer {p h : Nat} (st : VStep p h) : Vertex p h :=
  match st.vertex with
  | .inl _ => Sum.inr st.pair.2
  | .inr _ => Sum.inl st.pair.1

/-- The answer stream of a trace: one name per walked pair. -/
def answerStream {p h : Nat} (es : List (VEvent p h)) :
    List (Vertex p h) :=
  (eventsSteps es).map stepAnswer

theorem answerStream_length {p h : Nat} (es : List (VEvent p h)) :
    (answerStream es).length = (eventsSteps es).length :=
  List.length_map _ _

/-! ## Pin 3.0: the feed prefix is exactly the answer stream -/

/-- **Near endpoints are replay-inferred**: the feed prefix a trace
consumes is exactly its steps' answer stream — the walk's own state
supplies every query label, so the answers are the entire external
input. -/
theorem vevents_feed_recoverable {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)),
      ∃ rest : List (Vertex p h),
        feed = answerStream (vevents fuel mu pending D feed) ++ rest
  | _, _, [], [], feed => by
      rw [vevents_nil]
      exact ⟨feed, rfl⟩
  | fuel, mu, [], t :: rest, feed => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals]
          exact vevents_feed_recoverable fuel mu [] rest feed
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals'
              hsat]
            exact ⟨feed, rfl⟩
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat']
                exact ⟨feed, rfl⟩
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t rest feed hleg
                      hfals' hsat' htv]
                    exact ⟨feed, rfl⟩
                | cons v vs =>
                    cases v with
                    | inl i =>
                        cases feed with
                        | nil =>
                            rw [vevents_entry_feed_nil fuel' mu t rest i
                              vs hleg hfals' hsat' htv]
                            exact ⟨[], rfl⟩
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents_entry_feed_illkind fuel' mu t
                                  rest i vs q fs hleg hfals' hsat' htv]
                                exact ⟨Sum.inl q :: fs, rfl⟩
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha]
                                  exact ⟨Sum.inr a :: fs, rfl⟩
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha']
                                  rcases vevents_feed_recoverable fuel'
                                    (compose mu (singleMatching i a)) vs
                                    (t :: rest) fs with ⟨tail, htail⟩
                                  refine ⟨tail, ?_⟩
                                  unfold answerStream
                                  rw [eventsSteps_enter, eventsSteps_qstep,
                                    List.map_cons]
                                  exact congrArg (List.cons _) htail
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg']
        exact vevents_feed_recoverable fuel mu [] rest feed
  | fuel, mu, v :: vs, D, feed => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov]
        exact vevents_feed_recoverable fuel mu vs D feed
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov']
            exact ⟨feed, rfl⟩
        | succ fuel' =>
            cases v with
            | inl i =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov']
                    exact ⟨[], rfl⟩
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents_block_pigeon_illkind fuel' mu i vs D q
                          fs hcov']
                        exact ⟨Sum.inl q :: fs, rfl⟩
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents_block_pigeon_dead fuel' mu i vs D a
                            fs hcov' hha]
                          exact ⟨Sum.inr a :: fs, rfl⟩
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a
                            fs hcov' hha']
                          rcases vevents_feed_recoverable fuel'
                            (compose mu (singleMatching i a)) vs D fs with
                            ⟨tail, htail⟩
                          refine ⟨tail, ?_⟩
                          unfold answerStream
                          rw [eventsSteps_qstep, List.map_cons]
                          exact congrArg (List.cons _) htail
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov']
                    exact ⟨[], rfl⟩
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents_block_hole_illkind fuel' mu b vs D a
                          fs hcov']
                        exact ⟨Sum.inr a :: fs, rfl⟩
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents_block_hole_dead fuel' mu b vs D q fs
                            hcov' hq]
                          exact ⟨Sum.inl q :: fs, rfl⟩
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq']
                          rcases vevents_feed_recoverable fuel'
                            (compose mu (singleMatching q b)) vs D fs with
                            ⟨tail, htail⟩
                          refine ⟨tail, ?_⟩
                          unfold answerStream
                          rw [eventsSteps_qstep, List.map_cons]
                          exact congrArg (List.cons _) htail
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

/-! ## The answer alphabet: free vertices of the base -/

/-- Every answer names a vertex free in the trace's base matching —
directly from the walked pair's freshness. -/
theorem stepAnswer_fresh {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (st : VStep p h)
    (hst : st ∈ eventsSteps (vevents fuel mu pending D feed)) :
    vertexCoveredB mu (stepAnswer st) = false := by
  have hpair : st.pair ∈ eventsPairs (vevents fuel mu pending D feed) := by
    rw [eventsPairs_eq_map]
    exact List.mem_map.mpr ⟨st, hst, rfl⟩
  have hfr := vevents_pairs_fresh fuel mu pending D feed st.pair hpair
  unfold stepAnswer
  cases st.vertex with
  | inl i =>
      simp only [vertexCoveredB]
      exact hfr.2
  | inr b =>
      simp only [vertexCoveredB]
      rw [hfr.1]
      rfl

/-- The free holes of a matching map. -/
def freeHoles {p h : Nat} (mu : MatchingMap p h) : Finset (Fin h) :=
  Finset.univ.filter (fun b => holeUsed mu b = false)

/-- The free-vertex namespace: free pigeons and free holes. -/
def freeVertices {p h : Nat} (mu : MatchingMap p h) :
    Finset (Vertex p h) :=
  (freePigeons mu).image Sum.inl ∪ (freeHoles mu).image Sum.inr

theorem mem_freeVertices {p h : Nat} (mu : MatchingMap p h)
    (v : Vertex p h) :
    v ∈ freeVertices mu ↔ vertexCoveredB mu v = false := by
  unfold freeVertices
  cases v with
  | inl i =>
      simp only [Finset.mem_union, Finset.mem_image, vertexCoveredB]
      constructor
      · rintro (⟨j, hj, hji⟩ | ⟨b, _, hb⟩)
        · have : j = i := by injection hji
          rw [← this]
          rw [(mem_freePigeons mu j).mp hj]
          rfl
        · cases hb
      · intro hfree
        left
        refine ⟨i, ?_, rfl⟩
        rw [mem_freePigeons]
        cases hmi : mu i with
        | none => rfl
        | some c =>
            rw [hmi] at hfree
            simp at hfree
  | inr b =>
      simp only [Finset.mem_union, Finset.mem_image, vertexCoveredB]
      constructor
      · rintro (⟨j, _, hj⟩ | ⟨c, hc, hcb⟩)
        · cases hj
        · have : c = b := by injection hcb
          rw [← this]
          have := (Finset.mem_filter.mp hc).2
          exact this
      · intro hfree
        right
        refine ⟨b, ?_, rfl⟩
        unfold freeHoles
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hfree⟩

/-- **The answer stream lives in the free-vertex namespace.** -/
theorem answerStream_mem_freeVertices {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (v : Vertex p h)
    (hv : v ∈ answerStream (vevents fuel mu pending D feed)) :
    v ∈ freeVertices mu := by
  unfold answerStream at hv
  rcases List.mem_map.mp hv with ⟨st, hst, hstv⟩
  rw [mem_freeVertices, ← hstv]
  exact stepAnswer_fresh fuel mu pending D feed st hst

/-! ## The namespace cardinality (the L2 rider as a theorem) -/

/-- The general free-vertex count: free pigeons plus free holes — UF's
`2ℓ+1` is the rectangular `(n+1)/n` instance of this sum. -/
theorem freeVertices_card {p h : Nat} (mu : MatchingMap p h) :
    (freeVertices mu).card =
      (freePigeons mu).card + (freeHoles mu).card := by
  unfold freeVertices
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  · rw [Finset.disjoint_left]
    rintro v hv1 hv2
    rcases Finset.mem_image.mp hv1 with ⟨i, _, hi⟩
    rcases Finset.mem_image.mp hv2 with ⟨b, _, hb⟩
    rw [← hi] at hb
    cases hb

/-- On hole-injective maps, matched pigeons biject with used holes —
both count the matched-pair graph, by its two projections. -/
theorem card_usedHoles_eq_matched {p h : Nat} {mu : MatchingMap p h}
    (hmu : IsMatching mu) :
    (Finset.univ.filter (fun b : Fin h => holeUsed mu b = true)).card =
      (Finset.univ.filter
        (fun i : Fin p => (mu i).isSome = true)).card := by
  have himg2 : (Finset.univ.filter
      (fun e : Fin p × Fin h => mu e.1 = some e.2)).image Prod.snd =
      Finset.univ.filter (fun b : Fin h => holeUsed mu b = true) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨e, he, hcb⟩
      rw [← hcb]
      exact (holeUsed_eq_true_iff mu e.2).mpr ⟨e.1, he⟩
    · intro hb
      rcases (holeUsed_eq_true_iff mu b).mp hb with ⟨j, hj⟩
      exact ⟨(j, b), hj, rfl⟩
  have himg1 : (Finset.univ.filter
      (fun e : Fin p × Fin h => mu e.1 = some e.2)).image Prod.fst =
      Finset.univ.filter
        (fun i : Fin p => (mu i).isSome = true) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨e, he, hei⟩
      rw [← hei, he]
      rfl
    · intro hi
      rcases Option.isSome_iff_exists.mp hi with ⟨b, hb⟩
      exact ⟨(i, b), hb, rfl⟩
  have hinj2 : Set.InjOn Prod.snd
      (↑(Finset.univ.filter
        (fun e : Fin p × Fin h => mu e.1 = some e.2)) :
        Set (Fin p × Fin h)) := by
    intro e he f hf hef
    have he' : mu e.1 = some e.2 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
    have hf' : mu f.1 = some f.2 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hsnd : e.2 = f.2 := hef
    have hfst : e.1 = f.1 := by
      apply hmu e.1 f.1 e.2 he'
      rw [hf', hsnd]
    exact Prod.ext hfst hsnd
  have hinj1 : Set.InjOn Prod.fst
      (↑(Finset.univ.filter
        (fun e : Fin p × Fin h => mu e.1 = some e.2)) :
        Set (Fin p × Fin h)) := by
    intro e he f hf hef
    have he' : mu e.1 = some e.2 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
    have hf' : mu f.1 = some f.2 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hchain : some e.2 = some f.2 := by
      rw [← he', ← hf']
      exact congrArg mu hef
    have hsnd : e.2 = f.2 := by
      injection hchain
    exact Prod.ext hef hsnd
  rw [← himg2, ← himg1, Finset.card_image_of_injOn hinj2,
    Finset.card_image_of_injOn hinj1]

/-- **Square balance**: with `ℓ` free pigeons on a square hole-injective
instance, there are exactly `ℓ` free holes. -/
theorem card_freeHoles_square {p h : Nat} (hsq : p = h)
    {mu : MatchingMap p h} (hmu : IsMatching mu) {ell : Nat}
    (hell : (freePigeons mu).card = ell) :
    (freeHoles mu).card = ell := by
  have hpart1 : (Finset.univ.filter
        (fun i : Fin p => (mu i).isSome = true)).card +
      (freePigeons mu).card = p := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin p)))
      (p := fun i => (mu i).isSome = true)
    rw [Finset.card_univ, Fintype.card_fin] at this
    have hfp : Finset.univ.filter
        (fun i : Fin p => ¬((mu i).isSome = true)) = freePigeons mu := by
      unfold freePigeons
      apply Finset.filter_congr
      intro i _
      cases _hmi : mu i with
      | none => simp
      | some c => simp
    rw [hfp] at this
    exact this
  have hpart2 : (Finset.univ.filter
        (fun b : Fin h => holeUsed mu b = true)).card +
      (freeHoles mu).card = h := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin h)))
      (p := fun b => holeUsed mu b = true)
    rw [Finset.card_univ, Fintype.card_fin] at this
    have hfh : Finset.univ.filter
        (fun b : Fin h => ¬(holeUsed mu b = true)) = freeHoles mu := by
      unfold freeHoles
      apply Finset.filter_congr
      intro b _
      cases _hub : holeUsed mu b with
      | false => simp
      | true => simp
    rw [hfh] at this
    exact this
  have hbij := card_usedHoles_eq_matched (p := p) (h := h) hmu
  omega

/-- **Pin 3.0's alphabet on the square instance**: the answer namespace
has exactly `2ℓ` names — the `[2ℓ]` alphabet Stage 2's graded bound
consumes, and the free-VERTEX cost disclosed by rider L3. -/
theorem freeVertices_card_square {p h : Nat} (hsq : p = h)
    {mu : MatchingMap p h} (hmu : IsMatching mu) {ell : Nat}
    (hell : (freePigeons mu).card = ell) :
    (freeVertices mu).card = 2 * ell := by
  rw [freeVertices_card, hell, card_freeHoles_square hsq hmu hell]
  omega

end PHPMatchingAnswerTransport
end PvNP
