import PvNP.PHPMatchingDeterministicEncode
import PvNP.PHPMatchingEncodeDisposal

/-!
# GA-4 Stage A/B: decode scaffolding + conditional injectivity (S2189)

This module begins the pure replay/decode side of the deterministic matching
encode.  It proves that once the entered terms have been recovered, `G2`
recovers the exact blockwise sigma sets, and that once this sigma overlay is
known the corrected `(G1,sigma)` answer namespace decodes all of `G3` back to
the exact answer stream.

Stage B adds **conditional injectivity**: equal `encodeMatch` packets plus
equal entered-term sequences force equal bases (G1+G2 recovery).  The
module now performs the G2 side as a pure decoder: entered terms and G2
determine the sigma-overlay matching used by G1, independently of the
original rho, and `decodeMatchFromTerms` roundtrips to rho on every encode
image.  Full `Function.InjOn encodeMatch` is still blocked at the entered
term replay step: after the first block, the walk state needs the path
matching `ρ * π`, while G1 deliberately omits π and the G3 answer namespace
is decoded only after the sigma overlay is known.  The missing theorem is
therefore a pure packet replay lemma proving that `(G1,G2,G3)` determines
the entered-term sequence; once supplied,
`encodeMatch_eq_of_code_eq_of_entered_terms_eq` closes base injectivity.

This is encode/decode bookkeeping only.  It proves no bad-set cardinality or
switching statement.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeInjectivity

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingEncodeDisposal
open PHPMatchingDeterministicEncode
open PHPMatchingAnswerTransport

/-! ## Common trace abbreviations -/

/-- The deterministic entered-term sequence used by `encodeMatch`. -/
def enteredTermsOf {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (t : Nat) : List (MTerm p h) :=
  (blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t))).map
    (fun B => B.term)

/-! ## Decode one beta block -/

/-- Decode the pairs of an entered term whose positions are marked by a beta
block.  The output is a finite set because `G2` itself deliberately forgets
duplicate copies of a pair. -/
def decodeSigmaBlock {p h w : Nat} (term : MTerm p h)
    (beta : Finset (Fin w)) : Finset (Fin p × Fin h) :=
  term.toFinset.filter fun e =>
    ∃ i : Fin w, termMarkPos (w := w) term e = some i ∧ i ∈ beta

/-- Decode all sigma blocks from already replayed entered terms and `G2`.
Length mismatch is rejected by truncation; on an encode image the lengths
match by construction. -/
def decodeSigmaBlocks {p h w : Nat} :
    List (MTerm p h) → List (Finset (Fin w)) →
      List (Finset (Fin p × Fin h))
  | term :: terms, beta :: betas =>
      decodeSigmaBlock term beta :: decodeSigmaBlocks terms betas
  | _, _ => []

private theorem termIdx_lt_of_mem' {p h : Nat} :
    ∀ (term : MTerm p h) (e : Fin p × Fin h), e ∈ term →
      termIdx term e < term.length
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
        exact Nat.succ_lt_succ (termIdx_lt_of_mem' xs e he')

private theorem termIdx_get' {p h : Nat} :
    ∀ (term : MTerm p h) (e : Fin p × Fin h) (he : e ∈ term),
      term[termIdx term e]'(termIdx_lt_of_mem' term e he) = e
  | x :: xs, e, he => by
      unfold termIdx
      by_cases hx : x = e
      · simp only [hx, ↓reduceIte, List.getElem_cons_zero]
      · simp only [hx, ↓reduceIte]
        have he' : e ∈ xs := by
          cases he with
          | head => exact absurd rfl hx
          | tail _ h => exact h
        simpa [List.getElem_cons_succ] using termIdx_get' xs e he'

private theorem termMarkPos_exists {p h w : Nat} (term : MTerm p h)
    (e : Fin p × Fin h) (he : e ∈ term) (hw : term.length ≤ w) :
    ∃ i : Fin w, termMarkPos (w := w) term e = some i := by
  unfold termMarkPos
  simp only [he, ↓reduceDIte]
  have hlt := termIdx_lt_of_mem' term e he
  have hltw : termIdx term e < w := Nat.lt_of_lt_of_le hlt hw
  exact ⟨⟨termIdx term e, hltw⟩, by simp [hltw]⟩

private theorem termMarkPos_injective_on_term {p h w : Nat}
    (term : MTerm p h) (e f : Fin p × Fin h) (he : e ∈ term)
    (hf : f ∈ term) {i : Fin w}
    (hei : termMarkPos (w := w) term e = some i)
    (hfi : termMarkPos (w := w) term f = some i) : e = f := by
  unfold termMarkPos at hei hfi
  simp only [he, hf, ↓reduceDIte] at hei hfi
  split at hei <;> split at hfi
  next hew hfw =>
    have hidx : termIdx term e = termIdx term f := by
      have hi : (⟨termIdx term e, hew⟩ : Fin w) =
          ⟨termIdx term f, hfw⟩ := by
        simpa using hei.trans hfi.symm
      exact congrArg Fin.val hi
    let ie : Fin term.length := ⟨termIdx term e,
      termIdx_lt_of_mem' term e he⟩
    let iF : Fin term.length := ⟨termIdx term f,
      termIdx_lt_of_mem' term f hf⟩
    have hfin : ie = iF := Fin.ext hidx
    have heget : term.get ie = e := termIdx_get' term e he
    have hfget : term.get iF = f := termIdx_get' term f hf
    rw [hfin] at heget
    exact heget.symm.trans hfget
  all_goals simp_all

/-- A beta block is lossless for any selected pair list contained in its
entered term: decoding its positional marks recovers exactly that pair set. -/
theorem decodeSigmaBlock_sigmaMarks {p h w : Nat} (term : MTerm p h)
    (sigma : List (Fin p × Fin h))
    (hmem : ∀ e ∈ sigma, e ∈ term) (hw : term.length ≤ w) :
    decodeSigmaBlock term (sigmaMarks (w := w) term sigma) =
      sigma.toFinset := by
  ext e
  constructor
  · intro he
    simp only [decodeSigmaBlock, Finset.mem_filter] at he
    rcases he with ⟨het, i, hei, hibeta⟩
    change i ∈ (sigma.filterMap (termMarkPos (w := w) term)).toFinset at hibeta
    rw [List.mem_toFinset, List.mem_filterMap] at hibeta
    rcases hibeta with ⟨f, hf, hfi⟩
    have hft : f ∈ term := hmem f hf
    exact List.mem_toFinset.mpr (termMarkPos_injective_on_term term e f
      (List.mem_toFinset.mp het) hft hei hfi ▸ hf)
  · intro he
    rw [List.mem_toFinset] at he
    have het : e ∈ term := hmem e he
    rcases termMarkPos_exists term e het hw with ⟨i, hei⟩
    simp only [decodeSigmaBlock, Finset.mem_filter]
    refine ⟨List.mem_toFinset.mpr het, i, hei, ?_⟩
    change i ∈ (sigma.filterMap (termMarkPos (w := w) term)).toFinset
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨e, he, hei⟩

/-! ## Decode every block on the deterministic encode image -/

/-- `G2` recovers every sigma block as a finite pair set once replay has
identified the entered blocks.  This is the positional, blockwise
losslessness theorem used by the remaining pure replay. -/
theorem decodeSigmaBlocks_blockSigmasBeta {p h w : Nat}
    (blocks : List (VBlock p h))
    (hw : ∀ B ∈ blocks, B.term.length ≤ w) :
    decodeSigmaBlocks (blocks.map fun B => B.term)
        (blockSigmasBeta (w := w) blocks) =
      (blockSigmas blocks).map List.toFinset := by
  induction blocks with
  | nil => rfl
  | cons B blocks ih =>
      cases blocks with
      | nil =>
          simp only [List.map_cons, List.map_nil, blockSigmasBeta,
            blockSigmas, decodeSigmaBlocks]
          rw [decodeSigmaBlock_sigmaMarks]
          · intro e he
            exact ((mem_sigmaFull B e).mp
              (sigmaTrunc_subset_sigmaFull B e he)).1
          · exact hw B (List.mem_cons_self _ _)
      | cons B' blocks' =>
          have hhead := decodeSigmaBlock_sigmaMarks B.term (sigmaFull B)
            (fun e he => ((mem_sigmaFull B e).mp he).1)
            (hw B (List.mem_cons_self _ _))
          have htail := ih
            (fun C hC => hw C (List.mem_cons_of_mem _ hC))
          simpa [blockSigmasBeta, blockSigmas, decodeSigmaBlocks, hhead]
            using htail

private theorem block_term_mem_D {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h)) (hrho : IsMatching rho)
    (B : VBlock p h) (hB : B ∈ blocksOf (vtrace rho D feed)) :
    B.term ∈ D := by
  rcases blocksOf_entered_first (freePigeons rho).card rho [] D feed hrho B
      hB with ⟨pre, suf, hD, _⟩
  rw [hD]
  exact List.mem_append_right _ (List.mem_cons_self _ _)

/-- **Stage A image theorem.**  For an `encodeMatch` packet, its `G2`
component decodes to exactly the blockwise sigma sets after supplying only
the entered blocks produced by replay (not the sigma lists themselves). -/
theorem encodeMatch_decodeSigmaBlocks {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let code := encodeMatch hsq rho D hrho hell ht hw
    decodeSigmaBlocks (blocks.map fun B => B.term) code.G2 =
      (blockSigmas blocks).map List.toFinset := by
  intro feed blocks _code
  apply decodeSigmaBlocks_blockSigmasBeta
  intro B hB
  exact hw B.term (block_term_mem_D rho D feed hrho B hB)

/-! ## Decode the sigma overlay from entered terms and G2 -/

private theorem pairsToMatching_mem {p h : Nat} :
    ∀ {l : List (Fin p × Fin h)}, List.Pairwise PairDisjoint l →
      ∀ {i : Fin p} {a : Fin h}, (i, a) ∈ l →
        pairsToMatching l i = some a
  | [], _, _, _, hm => by cases hm
  | (j, b) :: es, hpd, i, a, hm => by
      rw [show pairsToMatching ((j, b) :: es) =
        compose (singleMatching j b) (pairsToMatching es) from rfl]
      rw [List.pairwise_cons] at hpd
      cases hm with
      | head =>
          simp [compose, singleMatching]
      | tail _ hm' =>
          have hne : j ≠ i := (hpd.1 (i, a) hm').1
          have hsingle : singleMatching j b i = none := by
            unfold singleMatching
            rw [if_neg (Ne.symm hne)]
          rw [compose_free_left _ _ i hsingle]
          exact pairsToMatching_mem hpd.2 hm'

private theorem pairsToMatching_eq_some_iff_of_pairwise {p h : Nat}
    {l : List (Fin p × Fin h)} (hpd : List.Pairwise PairDisjoint l)
    (i : Fin p) (a : Fin h) :
    pairsToMatching l i = some a ↔ (i, a) ∈ l := by
  constructor
  · exact pairsToMatching_eq_some l i a
  · exact pairsToMatching_mem hpd

private theorem pair_unique_of_pairwise_toFinset {p h : Nat}
    {l : List (Fin p × Fin h)} (hpd : List.Pairwise PairDisjoint l)
    {i : Fin p} {a b : Fin h}
    (ha : (i, a) ∈ l.toFinset) (hb : (i, b) ∈ l.toFinset) :
    a = b := by
  have hla : (i, a) ∈ l := List.mem_toFinset.mp ha
  have hlb : (i, b) ∈ l := List.mem_toFinset.mp hb
  by_cases hab : (i, a) = (i, b)
  · exact congrArg Prod.snd hab
  · have hdis := hpd.forall pairDisjoint_symm hla hlb hab
    exact False.elim (hdis.1 rfl)

private noncomputable def pairFinsetToMatching_aux {p h : Nat}
    (S : Finset (Fin p × Fin h)) (i : Fin p) :
    Option (Fin h) :=
  if h : ∃ a, (i, a) ∈ S then some (Classical.choose h) else none

/-- Interpret an orderless finite set of pair names as a matching.  The
roundtrip theorem below applies only when the set came from a pairwise
vertex-disjoint sigma list, so the chosen hole is unique. -/
noncomputable def pairFinsetToMatching {p h : Nat}
    (S : Finset (Fin p × Fin h)) : MatchingMap p h :=
  fun i => pairFinsetToMatching_aux S i

private theorem pairFinsetToMatching_eq_some_iff {p h : Nat}
    {S : Finset (Fin p × Fin h)}
    (huniq : ∀ {i : Fin p} {a b : Fin h},
      (i, a) ∈ S → (i, b) ∈ S → a = b)
    (i : Fin p) (a : Fin h) :
    pairFinsetToMatching S i = some a ↔ (i, a) ∈ S := by
  unfold pairFinsetToMatching pairFinsetToMatching_aux
  by_cases h : ∃ b, (i, b) ∈ S
  · rw [dif_pos h]
    constructor
    · intro hs
      have hca : Classical.choose h = a := by
        exact Option.some.inj hs
      simpa [hca] using Classical.choose_spec h
    · intro ha
      have hca : Classical.choose h = a :=
        huniq (Classical.choose_spec h) ha
      simp [hca]
  · rw [dif_neg h]
    constructor
    · intro hs
      cases hs
    · intro ha
      exact False.elim (h ⟨a, ha⟩)

private theorem pairFinsetToMatching_toFinset_eq_pairsToMatching {p h : Nat}
    {l : List (Fin p × Fin h)} (hpd : List.Pairwise PairDisjoint l) :
    pairFinsetToMatching l.toFinset = pairsToMatching l := by
  funext i
  cases hpi : pairsToMatching l i with
  | none =>
      by_cases hex : ∃ a, (i, a) ∈ l.toFinset
      · rcases hex with ⟨a, ha⟩
        have hsome : pairsToMatching l i = some a :=
          (pairsToMatching_eq_some_iff_of_pairwise hpd i a).mpr
            (List.mem_toFinset.mp ha)
        rw [hpi] at hsome
        cases hsome
      · unfold pairFinsetToMatching pairFinsetToMatching_aux
        rw [dif_neg hex]
  | some a =>
      have ha : (i, a) ∈ l.toFinset := by
        rw [List.mem_toFinset]
        exact (pairsToMatching_eq_some_iff_of_pairwise hpd i a).mp hpi
      have huniq : ∀ {i : Fin p} {a b : Fin h},
          (i, a) ∈ l.toFinset → (i, b) ∈ l.toFinset → a = b := by
        intro i a b ha hb
        exact pair_unique_of_pairwise_toFinset hpd ha hb
      exact (pairFinsetToMatching_eq_some_iff huniq i a).mpr ha

/-- Union a decoded block sequence into the orderless sigma-pair set. -/
def sigmaFinsetUnion {α : Type} [DecidableEq α] :
    List (Finset α) → Finset α
  | [] => ∅
  | S :: Ss => S ∪ sigmaFinsetUnion Ss

private theorem mem_sigmaFinsetUnion {α : Type} [DecidableEq α]
    (Ss : List (Finset α)) (x : α) :
    x ∈ sigmaFinsetUnion Ss ↔ ∃ S ∈ Ss, x ∈ S := by
  induction Ss with
  | nil =>
      simp [sigmaFinsetUnion]
  | cons S Ss ih =>
      simp [sigmaFinsetUnion, ih]

private theorem sigmaFinsetUnion_map_toFinset {α : Type} [DecidableEq α]
    (ls : List (List α)) :
    sigmaFinsetUnion (ls.map List.toFinset) = ls.join.toFinset := by
  ext x
  rw [mem_sigmaFinsetUnion]
  constructor
  · rintro ⟨S, hS, hx⟩
    rcases List.mem_map.mp hS with ⟨l, hl, hSl⟩
    rw [← hSl] at hx
    rw [List.mem_toFinset, List.mem_join]
    exact ⟨l, hl, List.mem_toFinset.mp hx⟩
  · intro hx
    rw [List.mem_toFinset, List.mem_join] at hx
    rcases hx with ⟨l, hl, hx⟩
    exact ⟨l.toFinset, List.mem_map.mpr ⟨l, hl, rfl⟩,
      List.mem_toFinset.mpr hx⟩

/-- Decode the orderless sigma-pair set from replayed entered terms and
the packet's G2 component. -/
def decodeSigmaSet {p h w : Nat} (terms : List (MTerm p h))
    (G2 : List (Finset (Fin w))) : Finset (Fin p × Fin h) :=
  sigmaFinsetUnion (decodeSigmaBlocks terms G2)

/-- Decode the sigma-overlay matching from replayed entered terms and G2.
This is independent of the original base matching; the only side input is
the entered-term list recovered by replay. -/
noncomputable def decodeSigmaOverlay {p h w : Nat} (terms : List (MTerm p h))
    (G2 : List (Finset (Fin w))) : MatchingMap p h :=
  pairFinsetToMatching (decodeSigmaSet terms G2)

/-- On an `encodeMatch` image, entered terms plus G2 reconstruct the exact
sigma-overlay matching consumed by G1. -/
theorem encodeMatch_decodeSigmaOverlay {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let code := encodeMatch hsq rho D hrho hell ht hw
    decodeSigmaOverlay (blocks.map fun B => B.term) code.G2 =
      pairsToMatching (blockSigmas blocks).join := by
  intro feed blocks code
  unfold decodeSigmaOverlay decodeSigmaSet
  have hdec :=
    encodeMatch_decodeSigmaBlocks hsq rho D hrho hell ht hw
  simp only at hdec
  rw [hdec, sigmaFinsetUnion_map_toFinset]
  have hpd :
      List.Pairwise PairDisjoint (blockSigmas blocks).join := by
    simpa [blocks, feed, vtrace] using
      blockSigmas_join_pairwise (freePigeons rho).card rho [] D feed
  exact pairFinsetToMatching_toFinset_eq_pairsToMatching hpd

/-! ## Decode G3 in the corrected replay namespace -/

/-- Decode a fixed-length G3 function after replay has recovered the sigma
overlay.  Both inputs are packet data (`G1`) or reconstructed from packet data
(`sigma`); the unknown base matching is not an argument. -/
def decodeAnswerCode {p h ell t : Nat} (G1 : MatchingMap p h)
    (sigma : List (Fin p × Fin h))
    (hlen : (replayVertexList G1 sigma).length = 2 * ell)
    (G3 : Fin t → Fin (2 * ell)) : List (Vertex p h) :=
  List.ofFn fun i => replayVertexDecode G1 sigma hlen (G3 i)

/-- The corrected G3 namespace roundtrips the complete answer stream on every
trace image once the trace sigma list is known.  This removes the former use
of `freeVertexList rho` from the decoder side. -/
theorem decodeAnswerCode_traceAnswerCode {p h ell t : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell) (feed : List (Vertex p h))
    (hans : (answerStream (vtrace rho D feed)).length = t) :
    let sigma := (blockSigmas (blocksOf (vtrace rho D feed))).join
    let G1 := encodeExt rho D feed
    let hlen : (replayVertexList G1 sigma).length = 2 * ell := by
      rw [replayVertexList_encodeExt rho D feed]
      exact freeVertexList_length_square hsq hrho hell
    decodeAnswerCode G1 sigma hlen
        (traceAnswerCode rho D hsq hrho hell feed hans) =
      answerStream (vtrace rho D feed) := by
  intro sigma G1 hlen
  apply List.ext_get
  · simp [decodeAnswerCode, hans]
  · intro n hn1 hn2
    have hnt : n < t := by simpa [decodeAnswerCode] using hn1
    let i : Fin t := ⟨n, hnt⟩
    simp only [decodeAnswerCode, List.get_ofFn]
    change replayVertexDecode G1 sigma hlen
        (traceAnswerCode rho D hsq hrho hell feed hans i) =
      (answerStream (vtrace rho D feed))[n]
    simp only [traceAnswerCode]
    exact replayVertexDecode_replayVertexCode G1 sigma hlen
      ((answerStream (vtrace rho D feed)).get ⟨n, by simpa [hans] using hnt⟩)
      (by
        rw [replayVertexList_encodeExt rho D feed]
        apply (mem_freeVertexList rho _).mpr
        have hmem :
            (answerStream (vtrace rho D feed)).get
                ⟨n, by simpa [hans] using hnt⟩ ∈
              answerStream (vtrace rho D feed) := List.get_mem _ _ _
        apply answerStream_mem_freeVertices (freePigeons rho).card rho [] D
          feed
        simpa [vtrace] using hmem)

/-- The deterministic feed is exactly the trace's answer stream on every
deep-feed image.  `vevents_feed_recoverable` gives the feed as the answer
stream plus an unused suffix; the synchronized length `t` forces that suffix
to be empty. -/
theorem leftmostLiveDeepFeed_eq_answerStream {p h t : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    leftmostLiveDeepFeed rho D t =
      answerStream (vtrace rho D (leftmostLiveDeepFeed rho D t)) := by
  have hrec :=
    vevents_feed_recoverable (freePigeons rho).card rho [] D
      (leftmostLiveDeepFeed rho D t)
  rcases hrec with ⟨rest, hrest⟩
  have hfeedLen :
      (leftmostLiveDeepFeed rho D t).length = t :=
    leftmostLiveDeepFeed_length hsq rho D hrho ht
  have hansLen :
      (answerStream (vtrace rho D (leftmostLiveDeepFeed rho D t))).length =
        t := by
    rw [answerStream_length]
    exact leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht
  have hansLen' :
      (answerStream
          (vevents (freePigeons rho).card rho [] D
            (leftmostLiveDeepFeed rho D t))).length = t := by
    simpa [vtrace] using hansLen
  have hrestLen : rest.length = 0 := by
    have hlen := congrArg List.length hrest
    rw [List.length_append, hfeedLen, hansLen'] at hlen
    omega
  have hrestNil : rest = [] := List.eq_nil_of_length_eq_zero hrestLen
  simpa [hrestNil] using hrest

/-! ## Base decoder interface for the next replay stage -/

/-- Recover a base point from `G1` once replay has reconstructed the sigma
overlay.  Stage B must replace the overlay argument by the output of pure
`(G1,G2,G3)` replay. -/
def decodeBasePoint {p h : Nat} (G1 sigma : MatchingMap p h) (i : Fin p) :
    Option (Fin h) :=
  if sigma i = none then G1 i else none

/-- Decode a base matching from a packet after replay has supplied the
entered-term list.  This is the pure G1/G2 base decoder for the closed
prefix: `decodeSigmaOverlay` reconstructs sigma from G2 and the terms,
then `decodeBasePoint` strips that sigma overlay out of G1. -/
noncomputable def decodeMatchFromTerms {p h w t ell : Nat}
    (terms : List (MTerm p h)) (code : MatchEncode p h w t ell) :
    MatchingMap p h :=
  fun i => decodeBasePoint code.G1 (decodeSigmaOverlay terms code.G2) i

/-- Decode `G3` after the entered-term list has supplied the `G2` sigma
overlay and hence the base matching.  This is the answer/feed analogue of
`decodeMatchFromTerms`: the list indexed by `G3` is computed from packet
data and the supplied entered terms, with no direct access to `rho`. -/
noncomputable def decodeAnswerCodeFromTerms {p h w t ell : Nat}
    (terms : List (MTerm p h)) (code : MatchEncode p h w t ell)
    (hlen : (freeVertexList (decodeMatchFromTerms terms code)).length =
      2 * ell) : List (Vertex p h) :=
  List.ofFn fun i =>
    (freeVertexList (decodeMatchFromTerms terms code)).get
      ⟨(code.G3 i).val, by
        have hc := (code.G3 i).isLt
        omega⟩

private theorem decodeAnswerCodeFromTerms_eq_of_base_eq
    {p h w t ell : Nat} (terms : List (MTerm p h))
    (code : MatchEncode p h w t ell) (rho : MatchingMap p h)
    (hlen : (freeVertexList (decodeMatchFromTerms terms code)).length =
      2 * ell)
    (hrhoLen : (freeVertexList rho).length = 2 * ell)
    (hbase : decodeMatchFromTerms terms code = rho) :
    decodeAnswerCodeFromTerms terms code hlen =
      List.ofFn fun i =>
        (freeVertexList rho).get
          ⟨(code.G3 i).val, by
            have hc := (code.G3 i).isLt
            omega⟩ := by
  subst rho
  unfold decodeAnswerCodeFromTerms
  rw [List.ofFn_inj]

/-- The base-decoder interface agrees with the existing G1 recovery theorem
on every deterministic trace image. -/
theorem decodeBasePoint_encodeExt {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h)) (i : Fin p) :
    decodeBasePoint (encodeExt rho D feed)
        (pairsToMatching
          (blockSigmas (blocksOf (vtrace rho D feed))).join) i = rho i := by
  unfold decodeBasePoint
  exact (encodeExt_recover_base rho D feed i).symm

/-! ## Stage B: encodeMatch image recovery and conditional injectivity shell -/

/-- Base recovery packaged on the `encodeMatch` image: `G1` plus the
trace-side sigma overlay recovers `rho` pointwise.  Pure decode still needs
to reconstruct that overlay from `(G1,G2,G3)` alone. -/
theorem encodeMatch_decodeBasePoint {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) (i : Fin p) :
    let feed := leftmostLiveDeepFeed rho D t
    let code := encodeMatch hsq rho D hrho hell ht hw
    decodeBasePoint code.G1
        (pairsToMatching
          (blockSigmas (blocksOf (vtrace rho D feed))).join) i = rho i := by
  intro feed _code
  simpa [encodeMatch] using decodeBasePoint_encodeExt rho D feed i

/-- Base recovery through the pure G2 sigma decoder, assuming the entered
blocks have already been replayed.  The decoder consumes only packet data
(`G1`, `G2`) plus the entered-term list; it does not take `rho` or the
trace sigma list as an input. -/
theorem encodeMatch_decodeBasePoint_from_terms {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) (i : Fin p) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let code := encodeMatch hsq rho D hrho hell ht hw
    decodeBasePoint code.G1
        (decodeSigmaOverlay (blocks.map fun B => B.term) code.G2) i =
      rho i := by
  intro feed blocks code
  have hoverlay :
      decodeSigmaOverlay (blocks.map fun B => B.term) code.G2 =
        pairsToMatching (blockSigmas blocks).join := by
    simpa [feed, blocks, code] using
      encodeMatch_decodeSigmaOverlay hsq rho D hrho hell ht hw
  have hbase :
      decodeBasePoint code.G1
          (pairsToMatching (blockSigmas blocks).join) i = rho i := by
    simpa [feed, blocks, code] using
      encodeMatch_decodeBasePoint hsq rho D hrho hell ht hw i
  rw [hoverlay]
  exact hbase

/-- `decodeMatchFromTerms` roundtrips on every encode image once replay has
identified the entered-term list. -/
theorem decodeMatchFromTerms_encodeMatch {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let code := encodeMatch hsq rho D hrho hell ht hw
    decodeMatchFromTerms (blocks.map fun B => B.term) code = rho := by
  intro feed blocks code
  funext i
  simpa [decodeMatchFromTerms, feed, blocks, code] using
    encodeMatch_decodeBasePoint_from_terms hsq rho D hrho hell ht hw i

/-- `G3` is also decoded from packet data once the entered-term list has
supplied the G2 sigma overlay. -/
theorem decodeAnswerCodeFromTerms_encodeMatch {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let terms := blocks.map fun B => B.term
    let code := encodeMatch hsq rho D hrho hell ht hw
    let hlen :
        (freeVertexList (decodeMatchFromTerms terms code)).length =
          2 * ell := by
      rw [decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw]
      exact freeVertexList_length_square hsq hrho hell
    decodeAnswerCodeFromTerms terms code hlen =
      answerStream (vtrace rho D feed) := by
  intro feed blocks terms code hlen
  have hbase :
      decodeMatchFromTerms terms code = rho := by
    simpa [feed, blocks, terms, code] using
      decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw
  have hans :
      (answerStream (vtrace rho D feed)).length = t := by
    rw [answerStream_length]
    simpa [feed] using
      leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht
  have hround :
      decodeAnswerCode (encodeExt rho D feed)
          (blockSigmas (blocksOf (vtrace rho D feed))).join
          (by
            rw [replayVertexList_encodeExt rho D feed]
            exact freeVertexList_length_square hsq hrho hell)
          (traceAnswerCode rho D hsq hrho hell feed hans) =
        answerStream (vtrace rho D feed) := by
    simpa using
      decodeAnswerCode_traceAnswerCode hsq rho D hrho hell feed hans
  have hdecoded :
      decodeAnswerCodeFromTerms terms code hlen =
        List.ofFn fun i =>
          (freeVertexList rho).get
            ⟨(code.G3 i).val, by
              have hc := (code.G3 i).isLt
              have hlenrho := freeVertexList_length_square hsq hrho hell
              omega⟩ := by
    exact decodeAnswerCodeFromTerms_eq_of_base_eq terms code rho hlen
      (freeVertexList_length_square hsq hrho hell) hbase
  refine hdecoded.trans ?_
  simpa [decodeAnswerCode, replayVertexDecode, code, encodeMatch,
    traceAnswerCodeDeep, feed, blocks, terms, replayVertexList_encodeExt]
    using hround

/-- Supplied entered terms decode the packet's answer codes back to the
deterministic deep feed itself. -/
theorem decodeFeedFromTerms_encodeMatch {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let terms := blocks.map fun B => B.term
    let code := encodeMatch hsq rho D hrho hell ht hw
    let hlen :
        (freeVertexList (decodeMatchFromTerms terms code)).length =
          2 * ell := by
      rw [decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw]
      exact freeVertexList_length_square hsq hrho hell
    decodeAnswerCodeFromTerms terms code hlen = feed := by
  intro feed blocks terms code hlen
  calc
    decodeAnswerCodeFromTerms terms code hlen =
        answerStream (vtrace rho D feed) := by
      simpa [feed, blocks, terms, code] using
        decodeAnswerCodeFromTerms_encodeMatch hsq rho D hrho hell ht hw
    _ = feed := by
      simpa [feed] using
        (leftmostLiveDeepFeed_eq_answerStream hsq rho D hrho ht).symm

/-- Replay an entered-term list from packet data and a candidate entered-term
list.  The candidate terms first decode the base from `G1/G2`; that decoded
base then decodes `G3` into the answer feed used to run the vertex trace. -/
noncomputable def replayTermsFromTerms {p h w t ell : Nat}
    (D : MDNF p h) (terms : List (MTerm p h))
    (code : MatchEncode p h w t ell)
    (hlen : (freeVertexList (decodeMatchFromTerms terms code)).length =
      2 * ell) : List (MTerm p h) :=
  (blocksOf (vtrace (decodeMatchFromTerms terms code) D
    (decodeAnswerCodeFromTerms terms code hlen))).map fun B => B.term

/-- A candidate entered-term list is accepted by pure packet replay when it
replays to itself. -/
def PacketReplayTermsFixed {p h w t ell : Nat} (D : MDNF p h)
    (terms : List (MTerm p h)) (code : MatchEncode p h w t ell) : Prop :=
  ∃ hlen, replayTermsFromTerms D terms code hlen = terms

/-- Exact residual for full packet injectivity: the packet has at most one
entered-term replay fixed point. -/
def PacketReplayTermsUnique {p h w t ell : Nat} (D : MDNF p h)
    (code : MatchEncode p h w t ell) : Prop :=
  ∀ terms₁ terms₂,
    PacketReplayTermsFixed D terms₁ code →
    PacketReplayTermsFixed D terms₂ code →
    terms₁ = terms₂

/-- The true deterministic entered-term sequence is a fixed point of the pure
packet replay operator on every encode image. -/
theorem replayTermsFromTerms_encodeMatch {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let terms := blocks.map fun B => B.term
    let code := encodeMatch hsq rho D hrho hell ht hw
    let hlen :
        (freeVertexList (decodeMatchFromTerms terms code)).length =
          2 * ell := by
      rw [decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw]
      exact freeVertexList_length_square hsq hrho hell
    replayTermsFromTerms D terms code hlen = terms := by
  intro feed blocks terms code hlen
  have hbase :
      decodeMatchFromTerms terms code = rho := by
    simpa [feed, blocks, terms, code] using
      decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw
  have hfeed :
      decodeAnswerCodeFromTerms terms code hlen = feed := by
    simpa [feed, blocks, terms, code] using
      decodeFeedFromTerms_encodeMatch hsq rho D hrho hell ht hw
  simp [replayTermsFromTerms, hbase, hfeed, terms, blocks]

/-- The actual entered-term sequence on an encode image is accepted by the
packet fixed-point predicate. -/
theorem packetReplayTermsFixed_encodeMatch {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    PacketReplayTermsFixed D (enteredTermsOf rho D t)
      (encodeMatch hsq rho D hrho hell ht hw) := by
  let feed := leftmostLiveDeepFeed rho D t
  let blocks := blocksOf (vtrace rho D feed)
  let terms := blocks.map fun B => B.term
  let code := encodeMatch hsq rho D hrho hell ht hw
  refine ⟨?_, ?_⟩
  · simpa [enteredTermsOf, feed, blocks, terms, code] using
      (show
        (freeVertexList
          (decodeMatchFromTerms terms code)).length = 2 * ell from by
          rw [decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw]
          exact freeVertexList_length_square hsq hrho hell)
  · simpa [enteredTermsOf, feed, blocks, terms, code] using
      replayTermsFromTerms_encodeMatch hsq rho D hrho hell ht hw

/-- **Entered-term conditional injectivity.**  Equal `encodeMatch` packets
and equal replayed entered-term sequences force equal bases.  All sigma
information used here is decoded from the common packet G2; the remaining
gap to full `InjOn encodeMatch` is exactly proving the entered-term
sequence is itself recoverable from `(G1,G2,G3)`. -/
theorem encodeMatch_eq_of_code_eq_of_entered_terms_eq
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hcode : encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
      encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw)
    (hterms :
      (blocksOf (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t))).map
          (fun B => B.term) =
        (blocksOf (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t))).map
          (fun B => B.term)) :
    rho₁ = rho₂ := by
  funext i
  let feed₁ := leftmostLiveDeepFeed rho₁ D t
  let feed₂ := leftmostLiveDeepFeed rho₂ D t
  let blocks₁ := blocksOf (vtrace rho₁ D feed₁)
  let blocks₂ := blocksOf (vtrace rho₂ D feed₂)
  let code₁ := encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw
  let code₂ := encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw
  have hG1 : code₁.G1 = code₂.G1 := by
    exact congrArg MatchEncode.G1 hcode
  have hG2 : code₁.G2 = code₂.G2 := by
    exact congrArg MatchEncode.G2 hcode
  have hterms' :
      (blocks₁.map fun B => B.term) = (blocks₂.map fun B => B.term) := by
    simpa [blocks₁, blocks₂, feed₁, feed₂] using hterms
  have hoverlay :
      decodeSigmaOverlay (blocks₁.map fun B => B.term) code₁.G2 =
        decodeSigmaOverlay (blocks₂.map fun B => B.term) code₂.G2 := by
    rw [hterms', hG2]
  have hr₁ :
      decodeBasePoint code₁.G1
          (decodeSigmaOverlay (blocks₁.map fun B => B.term) code₁.G2) i =
        rho₁ i := by
    simpa [feed₁, blocks₁, code₁] using
      encodeMatch_decodeBasePoint_from_terms hsq rho₁ D hrho₁ hell₁ ht₁ hw i
  have hr₂ :
      decodeBasePoint code₂.G1
          (decodeSigmaOverlay (blocks₂.map fun B => B.term) code₂.G2) i =
        rho₂ i := by
    simpa [feed₂, blocks₂, code₂] using
      encodeMatch_decodeBasePoint_from_terms hsq rho₂ D hrho₂ hell₂ ht₂ hw i
  calc
    rho₁ i =
        decodeBasePoint code₁.G1
          (decodeSigmaOverlay (blocks₁.map fun B => B.term) code₁.G2) i :=
      hr₁.symm
    _ =
        decodeBasePoint code₂.G1
          (decodeSigmaOverlay (blocks₂.map fun B => B.term) code₂.G2) i := by
      simp only [hG1, hoverlay]
    _ = rho₂ i := hr₂

/-- If the common packet has a unique pure replay fixed point, equal packets
force equal base matchings.  Thus full injectivity is reduced to a uniqueness
theorem about `PacketReplayTermsFixed`, with no direct access to `rho` in the
replay predicate. -/
theorem encodeMatch_eq_of_code_eq_of_packetReplayTermsUnique
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hcode : encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
      encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw)
    (huniq : PacketReplayTermsUnique D
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw)) :
    rho₁ = rho₂ := by
  let code₁ := encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw
  let code₂ := encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw
  have hfix₁ :
      PacketReplayTermsFixed D (enteredTermsOf rho₁ D t) code₁ := by
    simpa [code₁] using
      packetReplayTermsFixed_encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw
  have hfix₂_code₂ :
      PacketReplayTermsFixed D (enteredTermsOf rho₂ D t) code₂ := by
    simpa [code₂] using
      packetReplayTermsFixed_encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw
  have hfix₂ :
      PacketReplayTermsFixed D (enteredTermsOf rho₂ D t) code₁ := by
    simpa [code₁, code₂, hcode] using hfix₂_code₂
  have hterms :
      enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
    exact huniq _ _ hfix₁ hfix₂
  exact encodeMatch_eq_of_code_eq_of_entered_terms_eq hsq
    rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
    (by simpa [enteredTermsOf] using hterms)

/-- Subtype form of the fixed-point uniqueness reduction.  A proof that every
packet in the bad set has a unique pure replay fixed point gives injectivity
of the `encodeMatch` map on that bad set. -/
theorem encodeMatch_subtype_injective_of_packetReplayTermsUnique
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (huniq :
      ∀ rho : {rho : MatchingMap p h // rho ∈ vbadMatchings D (t - 1) ell},
        let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
        let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
          Nat.le_of_pred_lt hmem.2
        PacketReplayTermsUnique D
          (encodeMatch hsq rho.1 D hmem.1.1 hmem.1.2 ht hw)) :
    Function.Injective
      (fun rho : {rho : MatchingMap p h // rho ∈ vbadMatchings D (t - 1) ell} =>
        let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
        let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
          Nat.le_of_pred_lt hmem.2
        encodeMatch hsq rho.1 D hmem.1.1 hmem.1.2 ht hw) := by
  intro rho₁ rho₂ hcode
  let hmem₁ := (mem_vbadMatchings D (t - 1) ell rho₁.1).mp rho₁.2
  let hmem₂ := (mem_vbadMatchings D (t - 1) ell rho₂.1).mp rho₂.2
  let ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁.1) :=
    Nat.le_of_pred_lt hmem₁.2
  let ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂.1) :=
    Nat.le_of_pred_lt hmem₂.2
  have hcode' :
      encodeMatch hsq rho₁.1 D hmem₁.1.1 hmem₁.1.2 ht₁ hw =
        encodeMatch hsq rho₂.1 D hmem₂.1.1 hmem₂.1.2 ht₂ hw := by
    simpa [hmem₁, hmem₂, ht₁, ht₂] using hcode
  have huniq₁ :
      PacketReplayTermsUnique D
        (encodeMatch hsq rho₁.1 D hmem₁.1.1 hmem₁.1.2 ht₁ hw) := by
    simpa [hmem₁, ht₁] using huniq rho₁
  apply Subtype.ext
  exact encodeMatch_eq_of_code_eq_of_packetReplayTermsUnique hsq
    rho₁.1 rho₂.1 D hmem₁.1.1 hmem₂.1.1 hmem₁.1.2 hmem₂.1.2
    ht₁ ht₂ hw hcode' huniq₁

/-- **Conditional injectivity shell.** Equal codes and equal sigma-overlay
matchings force equal bases.  The stronger theorem
`encodeMatch_eq_of_code_eq_of_entered_terms_eq` discharges this side
condition from common entered terms plus G2; the residual GA-4 core is
pure recovery of those entered terms from `(G1,G2,G3)`. -/
theorem encodeMatch_eq_of_code_eq_of_sigma_eq
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hcode : encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
      encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw)
    (hsigma :
      pairsToMatching
          (blockSigmas (blocksOf
            (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t)))).join =
        pairsToMatching
          (blockSigmas (blocksOf
            (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t)))).join) :
    rho₁ = rho₂ := by
  funext i
  have hG1 :
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 :=
    congrArg MatchEncode.G1 hcode
  have hr₁ :=
    encodeMatch_decodeBasePoint hsq rho₁ D hrho₁ hell₁ ht₁ hw i
  have hr₂ :=
    encodeMatch_decodeBasePoint hsq rho₂ D hrho₂ hell₂ ht₂ hw i
  -- rewrite both recoveries through equal G1 and equal sigma matchings
  simp only at hr₁ hr₂
  -- hr₁/hr₂ are let-bound; unfold by simp on encodeMatch
  have hr₁' :
      decodeBasePoint (encodeExt rho₁ D (leftmostLiveDeepFeed rho₁ D t))
          (pairsToMatching
            (blockSigmas (blocksOf
              (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t)))).join) i =
        rho₁ i := by
    simpa [encodeMatch] using
      decodeBasePoint_encodeExt rho₁ D (leftmostLiveDeepFeed rho₁ D t) i
  have hr₂' :
      decodeBasePoint (encodeExt rho₂ D (leftmostLiveDeepFeed rho₂ D t))
          (pairsToMatching
            (blockSigmas (blocksOf
              (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t)))).join) i =
        rho₂ i := by
    simpa [encodeMatch] using
      decodeBasePoint_encodeExt rho₂ D (leftmostLiveDeepFeed rho₂ D t) i
  have hG1' :
      encodeExt rho₁ D (leftmostLiveDeepFeed rho₁ D t) =
        encodeExt rho₂ D (leftmostLiveDeepFeed rho₂ D t) := by
    simpa [encodeMatch] using hG1
  calc
    rho₁ i = decodeBasePoint
        (encodeExt rho₁ D (leftmostLiveDeepFeed rho₁ D t))
        (pairsToMatching
          (blockSigmas (blocksOf
            (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t)))).join) i :=
      hr₁'.symm
    _ = decodeBasePoint
        (encodeExt rho₂ D (leftmostLiveDeepFeed rho₂ D t))
        (pairsToMatching
          (blockSigmas (blocksOf
            (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t)))).join) i := by
          simp only [hG1', hsigma]
    _ = rho₂ i := hr₂'

end PHPMatchingEncodeInjectivity
end PvNP
