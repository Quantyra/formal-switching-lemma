import PvNP.PHPMatchingEncodeInjectivity

/-!
# S2190 / S2196: packet replay counterexample and coherent exclusion

`PacketReplayTermsUnique` — S2189's named GA-4 residual — is **false** on
`encodeMatch` images in general.  This module exhibits a concrete 3×3
instance whose deterministic encode packet admits **two distinct**
pure-replay fixed points:

* `cexD = [[(0,0)], [(1,1)]]`, base `cexRho = (0 ↦ 2)`, `t = 1`, `ell = 2`,
  `w = 3`; packet `G1 = (0 ↦ 2, 1 ↦ 1)`, `G2 = [{0}]`, `G3 = [2]`.
* The true entered-term list `[[(1,1)]]` replays to itself and decodes the
  base back to `cexRho`.
* The spurious candidate `[[(0,0)]]` **also** replays to itself: applying
  the packet's β-mark `{0}` to the wrong term selects the pair `(0,0)`,
  strips pigeon 0 from `G1` even though `G1 0 = some 2 ≠ some 0` (the
  fixed-point predicate never checks overlay/`G1` consistency), and the
  resulting wrong base `(1 ↦ 1)` traces straight into `[(0,0)]`.

Consequently `EncodeMatchReplayUniqueResidual` is **formally refuted** as
stated and the S2189 fixed-point uniqueness route to full
`Function.InjOn encodeMatch` is closed.  The conditional reduction shells
of S2189 remain valid but their uniqueness premise cannot be discharged.

**S2196 coherent exclusion.**  The spur fails
`PacketReplayTermsCoherent` because its sigma overlay assigns `0 ↦ 0`
while `G1 0 = some 2` (directional `OverlayAgreesG1` fails).  The true
entered-term list is coherent.  Bounded manual search on this packet
among length-`G2` singletons drawn from `cexD` finds no second coherent
fixed point; general coherent uniqueness remains open (no stop-loss
coherent counterexample found).

This module makes **no positive injectivity claim**.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingReplayCounterexample

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingAnswerTransport
open PHPMatchingEncodeInjectivity
open RestrictedPHPFloor

/-! ## Concrete instance -/

/-- Counterexample DNF: two legal width-1 terms. -/
def cexD : MDNF 3 3 :=
  [[((0 : Fin 3), (0 : Fin 3))], [((1 : Fin 3), (1 : Fin 3))]]

/-- Counterexample base matching: pigeon 0 on hole 2, pigeons 1,2 free. -/
def cexRho : MatchingMap 3 3 :=
  fun i => if i = (0 : Fin 3) then some (2 : Fin 3) else none

/-- The spurious decoded base: pigeon 1 on hole 1, pigeons 0,2 free. -/
def cexMu : MatchingMap 3 3 :=
  fun i => if i = (1 : Fin 3) then some (1 : Fin 3) else none

private def term00 : MTerm 3 3 := [((0 : Fin 3), (0 : Fin 3))]
private def term11 : MTerm 3 3 := [((1 : Fin 3), (1 : Fin 3))]

private theorem cexD_eq : cexD = [term00, term11] := rfl

theorem cexRho_isMatching : IsMatching cexRho := by
  intro i j a hi hj
  have hi0 : i = 0 := by
    by_contra hne
    have : cexRho i = none := by simp [cexRho, hne]
    simp [this] at hi
  have hj0 : j = 0 := by
    by_contra hne
    have : cexRho j = none := by simp [cexRho, hne]
    simp [this] at hj
  exact hi0.trans hj0.symm

theorem cexMu_isMatching : IsMatching cexMu := by
  intro i j a hi hj
  have hi1 : i = 1 := by
    by_contra hne
    have : cexMu i = none := by simp [cexMu, hne]
    simp [this] at hi
  have hj1 : j = 1 := by
    by_contra hne
    have : cexMu j = none := by simp [cexMu, hne]
    simp [this] at hj
  exact hi1.trans hj1.symm

private theorem freePigeons_cexRho :
    freePigeons cexRho = ({(1 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) := by
  ext i
  simp only [freePigeons, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases i <;> simp [cexRho]

private theorem freeHoles_cexRho :
    freeHoles cexRho = ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) := by
  ext b
  simp only [freeHoles, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases b <;> simp [holeUsed, finList, cexRho]

private theorem freePigeons_cexMu :
    freePigeons cexMu = ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) := by
  ext i
  simp only [freePigeons, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases i <;> simp [cexMu]

private theorem freeHoles_cexMu :
    freeHoles cexMu = ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) := by
  ext b
  simp only [freeHoles, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases b <;> simp [holeUsed, finList, cexMu]

theorem cex_ell : (freePigeons cexRho).card = 2 := by
  rw [freePigeons_cexRho]; decide

private theorem freePigeons_cexMu_card : (freePigeons cexMu).card = 2 := by
  rw [freePigeons_cexMu]; decide

private theorem sort_insert_two {a b : Fin 3} (hle : a ≤ b) (hne : a ≠ b) :
    ({a, b} : Finset (Fin 3)).sort (· ≤ ·) = [a, b] := by
  have hset : ({a, b} : Finset (Fin 3)) = insert a {b} := by
    ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm]
  rw [hset, Finset.sort_insert, Finset.sort_singleton]
  · intro c hc
    simp only [Finset.mem_singleton] at hc
    exact hc ▸ hle
  · simp [hne]

private theorem sort_12 :
    ({(1 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)).sort (· ≤ ·) =
      [(1 : Fin 3), (2 : Fin 3)] :=
  sort_insert_two (by decide : (1 : Fin 3) ≤ 2) (by decide)

private theorem sort_01 :
    ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)).sort (· ≤ ·) =
      [(0 : Fin 3), (1 : Fin 3)] :=
  sort_insert_two (by decide : (0 : Fin 3) ≤ 1) (by decide)

private theorem sort_02 :
    ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)).sort (· ≤ ·) =
      [(0 : Fin 3), (2 : Fin 3)] :=
  sort_insert_two (by decide : (0 : Fin 3) ≤ 2) (by decide)

/-- Canonical free-vertex enumeration of the true base. -/
theorem freeVertexList_cexRho :
    freeVertexList cexRho =
      [Sum.inl (1 : Fin 3), Sum.inl (2 : Fin 3),
        Sum.inr (0 : Fin 3), Sum.inr (1 : Fin 3)] := by
  unfold freeVertexList
  rw [freePigeons_cexRho, freeHoles_cexRho, sort_12, sort_01]
  rfl

/-- Canonical free-vertex enumeration of the spurious base. -/
theorem freeVertexList_cexMu :
    freeVertexList cexMu =
      [Sum.inl (0 : Fin 3), Sum.inl (2 : Fin 3),
        Sum.inr (0 : Fin 3), Sum.inr (2 : Fin 3)] := by
  simp only [freeVertexList, freePigeons_cexMu, freeHoles_cexMu, sort_02]
  rfl

theorem cex_hw : ∀ term ∈ cexD, term.length ≤ 3 := by
  intro term ht
  have hmem : term = term00 ∨ term = term11 := by
    simpa [cexD_eq] using ht
  rcases hmem with rfl | rfl <;> decide

/-! ## Boolean facts -/

private theorem term00_legal : termMatchingLegalB term00 = true := by decide
private theorem term11_legal : termMatchingLegalB term11 = true := by decide

private theorem term00_fals_rho : termFalsifiedB cexRho term00 = true := by
  unfold termFalsifiedB term00 pairFalsB
  simp [cexRho, holeUsed, finList]

private theorem term11_not_fals_rho : termFalsifiedB cexRho term11 = false := by
  unfold termFalsifiedB term11 pairFalsB
  simp [cexRho, holeUsed, finList]

private theorem term11_not_sat_rho : termSatisfiedB cexRho term11 = false := by
  unfold termSatisfiedB term11 pairSatB
  simp [cexRho]

private theorem term00_not_fals_mu : termFalsifiedB cexMu term00 = false := by
  unfold termFalsifiedB term00 pairFalsB
  simp [cexMu, holeUsed, finList]

private theorem term00_not_sat_mu : termSatisfiedB cexMu term00 = false := by
  unfold termSatisfiedB term00 pairSatB
  simp [cexMu]

private theorem termVertices_rho_term11 :
    termVertices cexRho term11 =
      [Sum.inl (1 : Fin 3), Sum.inr (1 : Fin 3)] := by
  unfold termVertices term11 pairUnresolvedB
  simp [cexRho, holeUsed, finList]

private theorem termVertices_mu_term00 :
    termVertices cexMu term00 =
      [Sum.inl (0 : Fin 3), Sum.inr (0 : Fin 3)] := by
  unfold termVertices term00 pairUnresolvedB
  simp [cexMu, holeUsed, finList]

private theorem holeUsed_rho_0 : holeUsed cexRho (0 : Fin 3) = false := by
  simp [holeUsed, finList, cexRho]

private theorem holeUsed_mu_0 : holeUsed cexMu (0 : Fin 3) = false := by
  simp [holeUsed, finList, cexMu]

private theorem finList_3 : finList 3 = [(0 : Fin 3), 1, 2] := by
  unfold finList
  simp [List.range_succ, List.range_zero]

/-! ## Depth bound via structural walk -/

private theorem vwalk_after_skip_term00 :
    vwalkAux 2 cexRho [] cexD = vwalkAux 2 cexRho [] [term11] := by
  rw [cexD_eq]
  exact vwalk_skip_falsified 2 cexRho term00 [term11]
    term00_legal term00_fals_rho

private theorem vwalk_entry_term11 :
    vwalkAux 2 cexRho [] [term11] =
      .pquery (1 : Fin 3) (fun a =>
        if holeUsed cexRho a = true then .leaf false
        else vwalkAux 1 (compose cexRho (singleMatching (1 : Fin 3) a))
          [Sum.inr (1 : Fin 3)] [term11]) := by
  simpa [termVertices_rho_term11] using
    (vwalk_entry_pigeon (fuel' := 1) cexRho term11 [] (1 : Fin 3)
      [Sum.inr (1 : Fin 3)] term11_legal term11_not_fals_rho
      term11_not_sat_rho termVertices_rho_term11)

theorem cex_ht : 1 ≤ vmdtDepth (canonicalVMDT cexD cexRho) := by
  unfold canonicalVMDT
  rw [cex_ell, vwalk_after_skip_term00, vwalk_entry_term11, vmdtDepth_pquery]
  exact Nat.le_add_right 1 _

/-! ## Packet -/

/-- The counterexample packet. -/
noncomputable def cexCode : MatchEncode 3 3 3 1 2 :=
  encodeMatch rfl cexRho cexD cexRho_isMatching cex_ell cex_ht cex_hw

/-- Deterministic deep feed of the counterexample. -/
def cex_deepFeed : List (Vertex 3 3) := [Sum.inr (0 : Fin 3)]

/-! ## Feed pin: leftmostLiveDeepFeed = [inr 0] -/

private theorem liveHole_rho_s0 (a : Fin 3) (ha : holeUsed cexRho a = false) :
    liveHoleDepthB cexRho (1 : Fin 3) 1
      [Sum.inr (1 : Fin 3)] [term11] 0 a = true := by
  unfold liveHoleDepthB
  rw [if_pos ha]
  exact decide_eq_true (Nat.zero_le _)

private theorem leftmostLiveDepthHole_rho :
    leftmostLiveDepthHole? cexRho (1 : Fin 3) 1
      [Sum.inr (1 : Fin 3)] [term11] 0 = some (0 : Fin 3) := by
  unfold leftmostLiveDepthHole?
  rw [finList_3]
  have h0 := liveHole_rho_s0 0 holeUsed_rho_0
  simp [List.find?_cons, h0]

private theorem leftmostLiveFeed_cex :
    leftmostLiveFeed cexRho cexD 1 = cex_deepFeed := by
  unfold leftmostLiveFeed cex_deepFeed
  rw [cex_ell, cexD_eq]
  -- Unfold the WF auxiliary at the concrete arguments.
  simp [leftmostLiveFeedAux, term00_legal, term00_fals_rho, term11_legal,
    term11_not_fals_rho, term11_not_sat_rho, termVertices_rho_term11,
    leftmostLiveDepthHole_rho]

theorem cex_deepFeed_eq :
    leftmostLiveDeepFeed cexRho cexD 1 = cex_deepFeed := by
  unfold leftmostLiveDeepFeed
  exact leftmostLiveFeed_cex

/-! ## Trace pins on the deep feed -/

private theorem vevents_skip_term00_rho (fuel : Nat) (feed : List (Vertex 3 3)) :
    vevents fuel cexRho [] cexD feed =
      vevents fuel cexRho [] [term11] feed := by
  rw [cexD_eq]
  exact vevents_skip_falsified fuel cexRho term00 [term11] feed
    term00_legal term00_fals_rho

private theorem vtrace_rho_feed :
    vtrace cexRho cexD cex_deepFeed =
      [.enter term11 cexRho,
        .qstep ⟨Sum.inl (1 : Fin 3), ((1 : Fin 3), (0 : Fin 3))⟩] := by
  unfold vtrace cex_deepFeed
  rw [cex_ell, vevents_skip_term00_rho]
  have htv := termVertices_rho_term11
  rw [vevents_entry_pigeon_live (fuel' := 1) cexRho term11 [] (1 : Fin 3)
    [Sum.inr (1 : Fin 3)] (0 : Fin 3) [] term11_legal term11_not_fals_rho
    term11_not_sat_rho htv holeUsed_rho_0]
  have hcov :
      vertexCoveredB (compose cexRho (singleMatching (1 : Fin 3) (0 : Fin 3)))
        (Sum.inr (1 : Fin 3)) = false := by
    simp [vertexCoveredB, holeUsed, finList, compose, singleMatching, cexRho]
  -- remaining fuel-1 call is stuck on uncovered pending with empty feed
  simp [hcov, vevents_block_feed_nil (fuel' := 0)
    (compose cexRho (singleMatching (1 : Fin 3) (0 : Fin 3)))
    (Sum.inr (1 : Fin 3)) [] [term11] hcov]

private theorem blocksOf_rho_feed :
    blocksOf (vtrace cexRho cexD cex_deepFeed) =
      [⟨term11, cexRho, [⟨Sum.inl (1 : Fin 3), ((1 : Fin 3), (0 : Fin 3))⟩]⟩] := by
  rw [vtrace_rho_feed]
  simp [blocksOf, stepsPrefix, afterSteps]

private theorem blockSigmas_rho_feed :
    blockSigmas (blocksOf (vtrace cexRho cexD cex_deepFeed)) = [term11] := by
  rw [blocksOf_rho_feed]
  simp only [blockSigmas]
  unfold sigmaTrunc sigmaFull blockQueried pairQueriedB pairUnresolvedB
  simp [cexRho, holeUsed, finList, term11]
  -- pairQueried: query labels include inl 1
  decide

private theorem vtrace_mu_feed :
    vtrace cexMu cexD cex_deepFeed =
      [.enter term00 cexMu,
        .qstep ⟨Sum.inl (0 : Fin 3), ((0 : Fin 3), (0 : Fin 3))⟩] := by
  unfold vtrace cex_deepFeed
  rw [freePigeons_cexMu_card, cexD_eq]
  have htv := termVertices_mu_term00
  rw [vevents_entry_pigeon_live (fuel' := 1) cexMu term00 [term11] (0 : Fin 3)
    [Sum.inr (0 : Fin 3)] (0 : Fin 3) [] term00_legal term00_not_fals_mu
    term00_not_sat_mu htv holeUsed_mu_0]
  have hcov :
      vertexCoveredB (compose cexMu (singleMatching (0 : Fin 3) (0 : Fin 3)))
        (Sum.inr (0 : Fin 3)) = true := by
    simp [vertexCoveredB, holeUsed, finList, compose, singleMatching, cexMu]
  rw [vevents_block_skip_covered _ _ _ _ _ _ hcov]
  have hsat :
      termSatisfiedB
        (compose cexMu (singleMatching (0 : Fin 3) (0 : Fin 3))) term00 =
        true := by
    unfold termSatisfiedB term00 pairSatB
    simp [compose, singleMatching, cexMu]
  have hfals' :
      termFalsifiedB
        (compose cexMu (singleMatching (0 : Fin 3) (0 : Fin 3))) term00 =
        false := by
    unfold termFalsifiedB term00 pairFalsB
    simp [compose, singleMatching, cexMu, holeUsed, finList]
  rw [vevents_stop_satisfied _ _ _ _ _ term00_legal hfals' hsat]

private theorem blocksOf_mu_feed :
    blocksOf (vtrace cexMu cexD cex_deepFeed) =
      [⟨term00, cexMu, [⟨Sum.inl (0 : Fin 3), ((0 : Fin 3), (0 : Fin 3))⟩]⟩] := by
  rw [vtrace_mu_feed]
  simp [blocksOf, stepsPrefix, afterSteps]

private theorem terms_rho_feed :
    (blocksOf (vtrace cexRho cexD cex_deepFeed)).map (fun B => B.term) =
      [term11] := by
  rw [blocksOf_rho_feed]; rfl

private theorem terms_mu_feed :
    (blocksOf (vtrace cexMu cexD cex_deepFeed)).map (fun B => B.term) =
      [term00] := by
  rw [blocksOf_mu_feed]; rfl

/-! ## Packet component pins -/

private theorem singleMatching_11 :
    pairsToMatching (term11 : List (Fin 3 × Fin 3)) =
      fun i => if i = (1 : Fin 3) then some (1 : Fin 3) else none := by
  funext i
  simp only [term11, pairsToMatching, compose, singleMatching, emptyMatching]
  split <;> simp_all

private theorem cexCode_G1_point (i : Fin 3) :
    cexCode.G1 i =
      (if i = (0 : Fin 3) then some (2 : Fin 3)
        else if i = (1 : Fin 3) then some (1 : Fin 3) else none) := by
  simp only [cexCode, encodeMatch]
  rw [cex_deepFeed_eq]
  unfold encodeExt
  rw [blockSigmas_rho_feed, List.join_cons, List.join_nil, List.append_nil,
    singleMatching_11]
  simp only [compose, cexRho]
  split_ifs <;> simp_all

theorem cexCode_G1 :
    cexCode.G1 =
      fun i =>
        if i = (0 : Fin 3) then some (2 : Fin 3)
        else if i = (1 : Fin 3) then some (1 : Fin 3) else none := by
  funext i; exact cexCode_G1_point i

private theorem sigmaMarks_term11 :
    sigmaMarks (w := 3) term11 term11 = ({(0 : Fin 3)} : Finset (Fin 3)) := by
  unfold sigmaMarks termMarkPos termIdx term11
  simp [List.filterMap, List.toFinset]

theorem cexCode_G2 :
    cexCode.G2 = [({(0 : Fin 3)} : Finset (Fin 3))] := by
  simp only [cexCode, encodeMatch, traceBetaDeep, traceBeta]
  rw [cex_deepFeed_eq, blocksOf_rho_feed]
  simp only [blockSigmasBeta]
  -- single block uses sigmaTrunc marks
  -- sigmaTrunc of the block = term11 (from blockSigmas_rho_feed)
  have hσ :
      sigmaTrunc ⟨term11, cexRho,
        [⟨Sum.inl (1 : Fin 3), ((1 : Fin 3), (0 : Fin 3))⟩]⟩ = term11 := by
    unfold sigmaTrunc sigmaFull blockQueried pairQueriedB pairUnresolvedB
    simp [cexRho, holeUsed, finList, term11]
    decide
  -- blockSigmasBeta [B] = [sigmaMarks B.term (sigmaTrunc B)]
  change [sigmaMarks (w := 3) term11
      (sigmaTrunc ⟨term11, cexRho,
        [⟨Sum.inl (1 : Fin 3), ((1 : Fin 3), (0 : Fin 3))⟩]⟩)] = _
  rw [hσ, sigmaMarks_term11]

private theorem answerStream_rho_feed :
    answerStream (vtrace cexRho cexD cex_deepFeed) = cex_deepFeed := by
  rw [vtrace_rho_feed]
  unfold answerStream eventsSteps stepAnswer cex_deepFeed
  rfl

private theorem vertexIdx_inr0_rho :
    vertexIdx (freeVertexList cexRho) (Sum.inr (0 : Fin 3)) = 2 := by
  rw [freeVertexList_cexRho]
  simp [vertexIdx]

private theorem vertexIdx_inr0_mu :
    vertexIdx (freeVertexList cexMu) (Sum.inr (0 : Fin 3)) = 2 := by
  rw [freeVertexList_cexMu]
  simp [vertexIdx]

private theorem freeVertexList_rho_len :
    (freeVertexList cexRho).length = 4 := by
  have h := freeVertexList_length_square (rfl : (3 : Nat) = 3)
    cexRho_isMatching cex_ell
  simpa using h

private theorem freeVertexList_mu_len :
    (freeVertexList cexMu).length = 4 := by
  have h := freeVertexList_length_square (rfl : (3 : Nat) = 3)
    cexMu_isMatching freePigeons_cexMu_card
  simpa using h

private theorem termMarkPos_singleton (e : Fin 3 × Fin 3) :
    termMarkPos (w := 3) [e] e = some (0 : Fin 3) := by
  unfold termMarkPos termIdx
  simp

private theorem decodeSigmaBlock_singleton (e : Fin 3 × Fin 3) :
    decodeSigmaBlock [e] ({(0 : Fin 3)} : Finset (Fin 3)) = {e} := by
  ext f
  constructor
  · intro hf
    simp only [decodeSigmaBlock, Finset.mem_filter, List.mem_toFinset,
      List.mem_singleton] at hf
    rcases hf with ⟨rfl, _i, _hpos, _hi⟩
    exact Finset.mem_singleton_self _
  · intro hf
    have hfe : f = e := Finset.mem_singleton.mp hf
    rw [hfe]
    simp only [decodeSigmaBlock, Finset.mem_filter, List.mem_toFinset,
      List.mem_singleton, Finset.mem_singleton, termMarkPos_singleton]
    exact ⟨trivial, ⟨0, rfl, rfl⟩⟩

/-- G3 collapses to the constant index `2` (position of `inr 0` in the
true free-vertex list). -/
theorem cexCode_G3 :
    cexCode.G3 = fun _ : Fin 1 => (⟨2, by decide⟩ : Fin 4) := by
  funext s
  apply Fin.eq_of_val_eq
  -- Unfold and pin the deep feed everywhere inside G3.
  simp only [cexCode, encodeMatch, traceAnswerCodeDeep, traceAnswerCode,
    replayVertexCode, cex_deepFeed_eq]
  have hstream := answerStream_rho_feed
  have hstream_deep :
      answerStream (vtrace cexRho cexD (leftmostLiveDeepFeed cexRho cexD 1)) =
        answerStream (vtrace cexRho cexD cex_deepFeed) := by
    rw [cex_deepFeed_eq]
  -- get is proof-irrelevant in the bounds certificate
  have hget_any :
      ∀ (L : List (Vertex 3 3))
        (_hL : L = answerStream (vtrace cexRho cexD cex_deepFeed))
        (hlt : s.val < L.length),
        L.get ⟨s.val, hlt⟩ = Sum.inr (0 : Fin 3) := by
    intro L hL _hlt
    fin_cases s
    have hgen : ∀ (M : List (Vertex 3 3))
        (_hM : M = [Sum.inr (0 : Fin 3)])
        (h0 : (0 : Nat) < M.length), M.get ⟨0, h0⟩ = Sum.inr 0 := by
      intro M hM _h0
      subst hM
      rfl
    subst hL
    exact hgen _ hstream (by rw [hstream]; exact Nat.zero_lt_one)
  have hns :
      replayVertexList (encodeExt cexRho cexD cex_deepFeed)
          (blockSigmas (blocksOf (vtrace cexRho cexD cex_deepFeed))).join =
        freeVertexList cexRho :=
    replayVertexList_encodeExt cexRho cexD cex_deepFeed
  -- Goal is `vertexIdx NS (answerStream deep).get ⟨s,_⟩ = 2`.
  simp_rw [hget_any _ hstream_deep, hns]
  exact vertexIdx_inr0_rho

/-! ## Choice-free singleton overlay -/

private theorem choose_singleton {p h : Nat} (x : Fin p) (y : Fin h)
    (hex : ∃ a, ((x, a) : Fin p × Fin h) ∈
      ({(x, y)} : Finset (Fin p × Fin h))) :
    Classical.choose hex = y := by
  have hs := Classical.choose_spec hex
  rw [Finset.mem_singleton] at hs
  exact congrArg Prod.snd hs

private theorem overlay_singleton {p h : Nat} (x : Fin p) (y : Fin h) :
    pairFinsetToMatching ({(x, y)} : Finset (Fin p × Fin h)) =
      fun i => if i = x then some y else none := by
  funext i
  rw [PHPMatchingEncodeInjectivity.pairFinsetToMatching_eq_dite]
  by_cases hix : i = x
  · subst hix
    rw [dif_pos ⟨y, Finset.mem_singleton_self _⟩, if_pos rfl]
    exact congrArg some (choose_singleton i y _)
  · rw [dif_neg, if_neg hix]
    rintro ⟨a, ha⟩
    rw [Finset.mem_singleton] at ha
    exact hix (congrArg Prod.fst ha)

/-! ## Decode sigma sets via pinned G2 -/

private theorem spur_sigmaSet :
    decodeSigmaSet [term00] cexCode.G2 =
      ({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3)) := by
  rw [cexCode_G2]
  unfold decodeSigmaSet term00
  simp only [decodeSigmaBlocks, sigmaFinsetUnion]
  rw [decodeSigmaBlock_singleton]
  simp [sigmaFinsetUnion]

private theorem true_sigmaSet :
    decodeSigmaSet [term11] cexCode.G2 =
      ({((1 : Fin 3), (1 : Fin 3))} : Finset (Fin 3 × Fin 3)) := by
  rw [cexCode_G2]
  unfold decodeSigmaSet term11
  simp only [decodeSigmaBlocks, sigmaFinsetUnion]
  rw [decodeSigmaBlock_singleton]
  simp [sigmaFinsetUnion]

private theorem spur_overlay :
    decodeSigmaOverlay [term00] cexCode.G2 =
      fun i => if i = (0 : Fin 3) then some (0 : Fin 3) else none := by
  unfold decodeSigmaOverlay
  rw [spur_sigmaSet, overlay_singleton]

private theorem true_overlay :
    decodeSigmaOverlay [term11] cexCode.G2 =
      fun i => if i = (1 : Fin 3) then some (1 : Fin 3) else none := by
  unfold decodeSigmaOverlay
  rw [true_sigmaSet, overlay_singleton]

private theorem decodeBasePoint_eval (G1 sigma : MatchingMap 3 3) (i : Fin 3) :
    decodeBasePoint G1 sigma i =
      if sigma i = none then G1 i else none := rfl

private theorem spur_base :
    decodeMatchFromTerms [term00] cexCode = cexMu := by
  funext i
  unfold decodeMatchFromTerms
  rw [spur_overlay, cexCode_G1, decodeBasePoint_eval]
  fin_cases i <;> simp [cexMu]

private theorem true_base :
    decodeMatchFromTerms [term11] cexCode = cexRho := by
  funext i
  unfold decodeMatchFromTerms
  rw [true_overlay, cexCode_G1, decodeBasePoint_eval]
  fin_cases i <;> simp [cexRho]

/-! ## Length pins via freeVertexList_length_square -/

private theorem spur_hlen_mu :
    (freeVertexList cexMu).length = 2 * 2 :=
  freeVertexList_length_square (rfl : (3 : Nat) = 3) cexMu_isMatching
    freePigeons_cexMu_card

private theorem true_hlen_rho :
    (freeVertexList cexRho).length = 2 * 2 :=
  freeVertexList_length_square (rfl : (3 : Nat) = 3) cexRho_isMatching cex_ell

private theorem spur_hlen :
    (freeVertexList (decodeMatchFromTerms [term00] cexCode)).length = 2 * 2 := by
  rw [spur_base, spur_hlen_mu]

private theorem true_hlen :
    (freeVertexList (decodeMatchFromTerms [term11] cexCode)).length = 2 * 2 := by
  rw [true_base, true_hlen_rho]

/-! ## Replay evaluation through an explicit base -/

/-- Evaluate `replayTermsFromTerms` once the decoded base has been
identified with an explicit map. -/
private theorem replayTermsFromTerms_eval {p h w t ell : Nat} (D : MDNF p h)
    (terms : List (MTerm p h)) (code : MatchEncode p h w t ell)
    (mu : MatchingMap p h) (hmu : decodeMatchFromTerms terms code = mu)
    (hlen : (freeVertexList (decodeMatchFromTerms terms code)).length =
      2 * ell)
    (hlen' : (freeVertexList mu).length = 2 * ell) :
    replayTermsFromTerms D terms code hlen =
      (blocksOf (vtrace mu D (List.ofFn fun s : Fin t =>
        (freeVertexList mu).get ⟨(code.G3 s).val, by
          rw [hlen']; exact (code.G3 s).isLt⟩))).map
        (fun B => B.term) := by
  subst hmu
  rfl

private theorem ofFn_fin_one {α : Type} (f : Fin 1 → α) :
    List.ofFn f = [f 0] := by
  rw [List.ofFn_succ]
  simp [List.ofFn_zero]

private theorem cexCode_G3_val (s : Fin 1) : (cexCode.G3 s).val = 2 := by
  rw [cexCode_G3]

private theorem decoded_feed_mu :
    (List.ofFn fun s : Fin 1 =>
      (freeVertexList cexMu).get ⟨(cexCode.G3 s).val, by
        rw [spur_hlen_mu]; exact (cexCode.G3 s).isLt⟩) =
      cex_deepFeed := by
  rw [ofFn_fin_one]
  have hval : (cexCode.G3 0).val = 2 := cexCode_G3_val 0
  have hlt : 2 < (freeVertexList cexMu).length := by
    rw [freeVertexList_mu_len]; decide
  have hget :
      (freeVertexList cexMu).get ⟨2, hlt⟩ = Sum.inr (0 : Fin 3) := by
    simp [freeVertexList_cexMu]
  have hhead :
      (freeVertexList cexMu).get ⟨(cexCode.G3 0).val, by
        rw [spur_hlen_mu]; exact (cexCode.G3 0).isLt⟩ =
        Sum.inr (0 : Fin 3) := by
    refine Eq.trans ?_ hget
    congr 1
    exact Fin.ext hval
  simpa [cex_deepFeed, hhead]

private theorem decoded_feed_rho :
    (List.ofFn fun s : Fin 1 =>
      (freeVertexList cexRho).get ⟨(cexCode.G3 s).val, by
        rw [true_hlen_rho]; exact (cexCode.G3 s).isLt⟩) =
      cex_deepFeed := by
  rw [ofFn_fin_one]
  have hval : (cexCode.G3 0).val = 2 := cexCode_G3_val 0
  have hlt : 2 < (freeVertexList cexRho).length := by
    rw [freeVertexList_rho_len]; decide
  have hget :
      (freeVertexList cexRho).get ⟨2, hlt⟩ = Sum.inr (0 : Fin 3) := by
    simp [freeVertexList_cexRho]
  have hhead :
      (freeVertexList cexRho).get ⟨(cexCode.G3 0).val, by
        rw [true_hlen_rho]; exact (cexCode.G3 0).isLt⟩ =
        Sum.inr (0 : Fin 3) := by
    refine Eq.trans ?_ hget
    congr 1
    exact Fin.ext hval
  simpa [cex_deepFeed, hhead]

/-- The spurious candidate `[[(0,0)]]` is a pure-replay fixed point. -/
theorem spur_fixed :
    PacketReplayTermsFixed cexD [term00] cexCode := by
  refine ⟨spur_hlen, ?_⟩
  rw [replayTermsFromTerms_eval cexD [term00] cexCode cexMu spur_base
    spur_hlen spur_hlen_mu, decoded_feed_mu, terms_mu_feed]

/-- The true entered-term list `[[(1,1)]]` is a pure-replay fixed point. -/
theorem true_fixed :
    PacketReplayTermsFixed cexD [term11] cexCode := by
  refine ⟨true_hlen, ?_⟩
  rw [replayTermsFromTerms_eval cexD [term11] cexCode cexRho true_base
    true_hlen true_hlen_rho, decoded_feed_rho, terms_rho_feed]

/-! ## The refutations -/

private theorem terms_ne : term00 ≠ term11 := by
  unfold term00 term11
  decide

private theorem term_lists_ne : ([term00] : List (MTerm 3 3)) ≠ [term11] := by
  intro h
  exact terms_ne (List.cons.inj h).1

/-- **Refutation (S2190).**  The S2189 fixed-point uniqueness residual is
false: the counterexample packet has two distinct pure-replay fixed
points. -/
theorem packetReplayTermsUnique_refuted :
    ¬ PacketReplayTermsUnique cexD cexCode := by
  intro hu
  exact term_lists_ne (hu [term00] [term11] spur_fixed true_fixed)

/-- **Refutation (S2190).**  `EncodeMatchReplayUniqueResidual` is
formally refuted as stated: it fails at `p = h = 3`, `w = 3`, `t = 1`,
`ell = 2` on `cexD`. -/
theorem encodeMatchReplayUniqueResidual_refuted :
    ¬ EncodeMatchReplayUniqueResidual (t := 1) (ell := 2) (w := 3)
      rfl cexD cex_hw := by
  intro hres
  exact packetReplayTermsUnique_refuted
    (hres cexRho cexRho_isMatching cex_ell cex_ht)

/-! ## S2196: coherent exclusion of the S2190 spur -/

private theorem spur_overlay_disagrees_G1 :
    ¬ OverlayAgreesG1 cexCode.G1 (decodeSigmaOverlay [term00] cexCode.G2) := by
  intro h
  have hsig :
      decodeSigmaOverlay [term00] cexCode.G2 (0 : Fin 3) = some (0 : Fin 3) := by
    rw [spur_overlay]; simp
  have hG1 : cexCode.G1 (0 : Fin 3) = some (0 : Fin 3) := h 0 0 hsig
  have hG1' : cexCode.G1 (0 : Fin 3) = some (2 : Fin 3) := by
    rw [cexCode_G1]; simp
  have hne : (0 : Fin 3) ≠ 2 := by decide
  exact hne (Option.some.inj (hG1.symm.trans hG1'))

/-- **S2196.**  The S2190 spurious fixed point is **not** coherent: its
sigma overlay assigns `0 ↦ 0` while packet `G1` has `0 ↦ 2`. -/
theorem spur_not_coherent :
    ¬ PacketReplayTermsCoherent cexD [term00] cexCode := by
  intro hc
  exact spur_overlay_disagrees_G1 hc.2.2.1

private theorem true_terms_eq_entered :
    enteredTermsOf cexRho cexD 1 = [term11] := by
  simp only [enteredTermsOf]
  rw [cex_deepFeed_eq, terms_rho_feed]

/-- **S2196.**  The true entered-term list on the counterexample packet is
coherent (via the general encode-image theorem). -/
theorem true_coherent :
    PacketReplayTermsCoherent cexD [term11] cexCode := by
  have h :=
    packetReplayTermsCoherent_encodeMatch rfl cexRho cexD
      cexRho_isMatching cex_ell cex_ht cex_hw
  simpa [cexCode, true_terms_eq_entered] using h

/-- Bounded manual search note (S2196): among length-`G2` (= 1) singleton
candidates drawn from `cexD`, only `[term11]` is coherent; `[term00]` is
excluded above.  No second coherent fixed point is known on this packet,
and no general coherent counterexample was found.  General
`PacketReplayTermsCoherentUnique` remains open. -/
theorem spur_and_true_coherent_status :
    ¬ PacketReplayTermsCoherent cexD [term00] cexCode ∧
      PacketReplayTermsCoherent cexD [term11] cexCode :=
  ⟨spur_not_coherent, true_coherent⟩

end PHPMatchingReplayCounterexample
end PvNP
