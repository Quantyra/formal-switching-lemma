import PvNP.PHPMatchingDeterministicEncode
import PvNP.PHPMatchingEncodeDisposal

/-!
# GA-4 Stage A/B/C + S2196 coherent replay: decode scaffolding + injectivity shells

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
image.  The true entered-term sequence is a fixed point of the pure
`(G1,G2,G3)` operator `replayTermsFromTerms`.

**S2190 residual status (closed as dead).**  The pure fixed-point uniqueness
predicate `PacketReplayTermsUnique` is **formally refuted** on encode images
(see `PHPMatchingReplayCounterexample`): a spurious fixed point can decode a
wrong sigma overlay that is inconsistent with `G1`.  The S2189 fixed-point
uniqueness route is therefore dead; its conditional shells remain valid but
their uniqueness premise cannot be discharged.

**S2196 coherent route.**  `PacketReplayTermsCoherent` strengthens the
fixed-point predicate by requiring length agreement with `G2`, directional
overlay–`G1` agreement (`OverlayAgreesG1`: every sigma assignment is present
in `G1`, not global equality), matching-hood of overlay and decoded base,
and free-pigeon count `ell` on the decoded base.  Encode images are coherent
(`packetReplayTermsCoherent_encodeMatch`); the S2190 spur is excluded.
Full multi-block injectivity reduces to uniqueness of coherent fixed points
(`PacketReplayTermsCoherentUnique` / `EncodeMatchCoherentReplayUniqueResidual`),
which remains **open** (no new coherent counterexample found; no general
uniqueness proof in this story).

**S2197 weaker preimage residual.**  Prefer proving equal codes force equal
`enteredTermsOf` (`EncodeMatchEnteredTermsEqResidual`), then discharge bases
via `encodeMatch_eq_of_code_eq_of_entered_terms_eq`.  Empty-G2 entered-term
equality is unconditional
(`enteredTermsOf_eq_of_encodeMatch_eq_of_G2_nil`); length transport and the
`firstNotFalsifiedTerm_eq_of_factor` / `compose_decodeBasePoint_of_overlayAgreesG1`
seeds are landed.

**S2198 genuine-head bridge.**  On nonempty encode images,
`firstNotFalsifiedTerm G1 D = some (enteredTermsOf).head`
(`enteredTermsOf_head_eq_firstNotFalsified_G1`).  Length-1 entered-term
equality from equal codes is unconditional
(`enteredTermsOf_eq_of_encodeMatch_eq_of_length_one`); the residual discharges
on families with entered-term length ≤ 1.  Full multi-block
`enteredTermsOf_eq_of_encodeMatch_eq` and unconditional
`encodeMatch_subtype_injective` remain open (same obstruction: G3 is
free-list-relative; multi-block term identity past the head still open).

**S2199 length-2 exit recovery.**  Encode-theoretic first-block exit
`firstBlockExitMatching = compose ρ (pairsToMatching (σ′₀))` factors `G1` on
length-≥2 images; every block term is the UF scan of its path entry
(`block_term_eq_firstNotFalsified_entry`); the second entered term is the
scan of the second block entry (`enteredTermsOf_second_eq_firstNotFalsified_exit`).
Equal codes plus equal second-block entries force length-2 entered-term
equality (`enteredTermsOf_eq_of_encodeMatch_eq_of_length_two_of_exit_eq`).
Unconditional multi-block residual remains open (need exit/second-entry
recovery from the packet alone).  Genuine-preimage collision search lives in
`PHPMatchingEncodeCollisionSearch`.

**S2200 path-entry vs σ-exit.**  On every length-≥2 root trace the second
block's path entry is the first entry composed with the first block's
**walked** pairs (`second_block_entry_eq_compose_first_steps`), while
`firstBlockExitMatching` overlays the first block's **σ′** pairs.  These
differ: σ-exit satisfies the first entered term, but a second block can
open only after that term has been falsified under the path matching
(`secondBlockEntry?_ne_some_firstBlockExitMatching`).  Packet-side recovery
of the first-block σ-set from `(G1, G2)` head data is landed
(`packetFirstBlockSigma_eq_of_encode_image`); recovering the **path** second
entry from the packet alone remains open, so
`EncodeMatchLengthTwoExitEqResidual` is not discharged.

Stage C adds dual sigma recovery (`decodeSigmaFromBase`), unconditional
empty-G2 injectivity (`encodeMatch_eq_of_code_eq_of_G2_nil`), the UF
`firstNotFalsifiedTerm` scan, and residual packaging.

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
open RestrictedPHPFloor

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

/-- Public unfolding form of the choice-based pair-set decoder (used by the
S2190 replay-uniqueness counterexample module). -/
theorem pairFinsetToMatching_eq_dite {p h : Nat}
    (S : Finset (Fin p × Fin h)) (i : Fin p) :
    pairFinsetToMatching S i =
      if h : ∃ a, (i, a) ∈ S then some (Classical.choose h) else none :=
  rfl

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

/-! ## S2196: coherent packet-replay predicate

Pure fixed-point uniqueness is dead (S2190).  Coherence adds the
structural side-conditions that genuine encode entered-terms satisfy and
that the S2190 spur violates: length agreement with `G2`, directional
overlay–`G1` agreement, matching-hood, and free-pigeon count. -/

/-- Directional overlay–G1 agreement: every sigma-overlay assignment is
present in `G1`.  This is **not** global overlay equality with `G1`
(which would force an empty base). -/
def OverlayAgreesG1 {p h : Nat} (G1 sigma : MatchingMap p h) : Prop :=
  ∀ i a, sigma i = some a → G1 i = some a

/-- A candidate entered-term list is **coherent** for a packet when it is a
pure-replay fixed point and additionally satisfies the structural
side-conditions of a genuine encode image. -/
def PacketReplayTermsCoherent {p h w t ell : Nat}
    (D : MDNF p h) (terms : List (MTerm p h))
    (code : MatchEncode p h w t ell) : Prop :=
  PacketReplayTermsFixed D terms code ∧
  terms.length = code.G2.length ∧
  OverlayAgreesG1 code.G1 (decodeSigmaOverlay terms code.G2) ∧
  IsMatching (decodeSigmaOverlay terms code.G2) ∧
  IsMatching (decodeMatchFromTerms terms code) ∧
  (freePigeons (decodeMatchFromTerms terms code)).card = ell

/-- **Sufficient** coherent-replay residual for full packet injectivity after
S2190: if the packet has at most one coherent pure-replay fixed point, the
existing shells close injectivity.  Not proved necessary (extraneous coherent
fixed points could exist while encodeMatch remains injective). -/
def PacketReplayTermsCoherentUnique {p h w t ell : Nat} (D : MDNF p h)
    (code : MatchEncode p h w t ell) : Prop :=
  ∀ terms₁ terms₂,
    PacketReplayTermsCoherent D terms₁ code →
    PacketReplayTermsCoherent D terms₂ code →
    terms₁ = terms₂

private theorem blockSigmasBeta_length {p h w : Nat} :
    ∀ (blocks : List (VBlock p h)),
      (blockSigmasBeta (w := w) blocks).length = blocks.length
  | [] => rfl
  | [B] => rfl
  | B :: B' :: Bs => by
      simp only [blockSigmasBeta, List.length_cons]
      exact congrArg Nat.succ
        (blockSigmasBeta_length (w := w) (B' :: Bs))

/-- On every encode image the entered-term list has the same length as G2. -/
theorem enteredTermsOf_length_eq_G2 {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    (enteredTermsOf rho D t).length =
      (encodeMatch hsq rho D hrho hell ht hw).G2.length := by
  simp only [enteredTermsOf, encodeMatch, traceBetaDeep, traceBeta,
    List.length_map]
  exact (blockSigmasBeta_length (w := w)
    (blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)))).symm

/-- Encode-image sigma overlay is hole-injective. -/
theorem isMatching_decodeSigmaOverlay_encodeMatch {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let code := encodeMatch hsq rho D hrho hell ht hw
    IsMatching (decodeSigmaOverlay (blocks.map fun B => B.term) code.G2) := by
  intro feed blocks code
  have hoverlay :
      decodeSigmaOverlay (blocks.map fun B => B.term) code.G2 =
        pairsToMatching (blockSigmas blocks).join := by
    simpa [feed, blocks, code] using
      encodeMatch_decodeSigmaOverlay hsq rho D hrho hell ht hw
  rw [hoverlay]
  exact isMatching_pairsToMatching _
    (blockSigmas_join_pairwise (freePigeons rho).card rho [] D feed)

/-- On every encode image the path sigma is directionally present in G1. -/
theorem overlayAgreesG1_encodeMatch {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let blocks := blocksOf (vtrace rho D feed)
    let code := encodeMatch hsq rho D hrho hell ht hw
    OverlayAgreesG1 code.G1
      (decodeSigmaOverlay (blocks.map fun B => B.term) code.G2) := by
  intro feed blocks code
  have hoverlay :
      decodeSigmaOverlay (blocks.map fun B => B.term) code.G2 =
        pairsToMatching (blockSigmas blocks).join := by
    simpa [feed, blocks, code] using
      encodeMatch_decodeSigmaOverlay hsq rho D hrho hell ht hw
  intro i a hsig
  rw [hoverlay] at hsig
  have hmem : (i, a) ∈ (blockSigmas blocks).join :=
    pairsToMatching_eq_some _ i a hsig
  have hfresh :=
    blockSigmas_join_fresh (freePigeons rho).card rho [] D feed (i, a) hmem
  have hrho_none : rho i = none := hfresh.1
  have hG1 :
      code.G1 i =
        compose rho (pairsToMatching (blockSigmas blocks).join) i := by
    simp [code, encodeMatch, feed, encodeExt, blocks]
  rw [hG1, compose_free_left rho _ i hrho_none, hsig]

/-- The true deterministic entered-term sequence is coherent on every
encode image. -/
theorem packetReplayTermsCoherent_encodeMatch {p h w t ell : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    PacketReplayTermsCoherent D (enteredTermsOf rho D t)
      (encodeMatch hsq rho D hrho hell ht hw) := by
  let feed := leftmostLiveDeepFeed rho D t
  let blocks := blocksOf (vtrace rho D feed)
  let terms := blocks.map fun B => B.term
  let code := encodeMatch hsq rho D hrho hell ht hw
  refine ⟨?fixed, ?len, ?agree, ?msig, ?mbase, ?free⟩
  · simpa [enteredTermsOf, feed, blocks, terms, code] using
      packetReplayTermsFixed_encodeMatch hsq rho D hrho hell ht hw
  · simpa [enteredTermsOf, feed, blocks, terms, code] using
      enteredTermsOf_length_eq_G2 hsq rho D hrho hell ht hw
  · simpa [enteredTermsOf, feed, blocks, terms, code] using
      overlayAgreesG1_encodeMatch hsq rho D hrho hell ht hw
  · simpa [enteredTermsOf, feed, blocks, terms, code] using
      isMatching_decodeSigmaOverlay_encodeMatch hsq rho D hrho hell ht hw
  · have hbase :
        decodeMatchFromTerms terms code = rho := by
      simpa [feed, blocks, terms, code] using
        decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw
    simpa [enteredTermsOf, feed, blocks, terms, code, hbase] using hrho
  · have hbase :
        decodeMatchFromTerms terms code = rho := by
      simpa [feed, blocks, terms, code] using
        decodeMatchFromTerms_encodeMatch hsq rho D hrho hell ht hw
    simpa [enteredTermsOf, feed, blocks, terms, code, hbase] using hell

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

/-! ## S2196 coherent uniqueness shells

Mirror the S2189 fixed-point uniqueness shells under the stronger
`PacketReplayTermsCoherentUnique` residual.  General uniqueness remains
open; these shells close injectivity once uniqueness is supplied. -/

/-- If the common packet has a unique coherent pure-replay fixed point,
equal packets force equal base matchings. -/
theorem encodeMatch_eq_of_code_eq_of_packetReplayTermsCoherentUnique
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
    (huniq : PacketReplayTermsCoherentUnique D
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw)) :
    rho₁ = rho₂ := by
  let code₁ := encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw
  let code₂ := encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw
  have hfix₁ :
      PacketReplayTermsCoherent D (enteredTermsOf rho₁ D t) code₁ := by
    simpa [code₁] using
      packetReplayTermsCoherent_encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw
  have hfix₂_code₂ :
      PacketReplayTermsCoherent D (enteredTermsOf rho₂ D t) code₂ := by
    simpa [code₂] using
      packetReplayTermsCoherent_encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw
  have hfix₂ :
      PacketReplayTermsCoherent D (enteredTermsOf rho₂ D t) code₁ := by
    simpa [code₁, code₂, hcode] using hfix₂_code₂
  have hterms :
      enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t :=
    huniq _ _ hfix₁ hfix₂
  exact encodeMatch_eq_of_code_eq_of_entered_terms_eq hsq
    rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
    (by simpa [enteredTermsOf] using hterms)

/-- Subtype form of the coherent fixed-point uniqueness reduction. -/
theorem encodeMatch_subtype_injective_of_packetReplayTermsCoherentUnique
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (huniq :
      ∀ rho : {rho : MatchingMap p h // rho ∈ vbadMatchings D (t - 1) ell},
        let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
        let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
          Nat.le_of_pred_lt hmem.2
        PacketReplayTermsCoherentUnique D
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
      PacketReplayTermsCoherentUnique D
        (encodeMatch hsq rho₁.1 D hmem₁.1.1 hmem₁.1.2 ht₁ hw) := by
    simpa [hmem₁, ht₁] using huniq rho₁
  apply Subtype.ext
  exact encodeMatch_eq_of_code_eq_of_packetReplayTermsCoherentUnique hsq
    rho₁.1 rho₂.1 D hmem₁.1.1 hmem₂.1.1 hmem₁.1.2 hmem₂.1.2
    ht₁ ht₂ hw hcode' huniq₁

/-- **Residual (S2196).**  Full `PacketReplayTermsCoherentUnique` on every
`encodeMatch` image.  The true entered-term sequence is coherent
(`packetReplayTermsCoherent_encodeMatch`); discharging uniqueness yields
`encodeMatch_subtype_injective` on the graded bad set via
`encodeMatch_subtype_injective_of_packetReplayTermsCoherentUnique`.

The S2189 pure-fixed-point residual is dead (S2190 refutation).  No second
coherent counterexample is known; general uniqueness remains open. -/
def EncodeMatchCoherentReplayUniqueResidual {p h w t ell : Nat}
    (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w) : Prop :=
  ∀ (rho : MatchingMap p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)),
    PacketReplayTermsCoherentUnique D
      (encodeMatch hsq rho D hrho hell ht hw)

/-- Unconditional injectivity on the graded bad-set subtype, assuming the
encode-image coherent-replay-uniqueness residual. -/
theorem encodeMatch_subtype_injective_of_coherent_residual
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hres : EncodeMatchCoherentReplayUniqueResidual (t := t) (ell := ell)
      (w := w) hsq D hw) :
    Function.Injective
      (fun rho : {rho : MatchingMap p h // rho ∈ vbadMatchings D (t - 1) ell} =>
        let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
        let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
          Nat.le_of_pred_lt hmem.2
        encodeMatch hsq rho.1 D hmem.1.1 hmem.1.2 ht hw) :=
  encodeMatch_subtype_injective_of_packetReplayTermsCoherentUnique hsq D hw
    (fun rho => by
      let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
      let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
        Nat.le_of_pred_lt hmem.2
      simpa [hmem, ht] using hres rho.1 hmem.1.1 hmem.1.2 ht)

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

/-! ## Stage C: dual recovery, empty-G2 injectivity, residual packaging -/

/-- Dual of `decodeBasePoint`: recover the sigma overlay from G1 and a
candidate base (the G1-assignments on free pigeons of the base). -/
def decodeSigmaFromBase {p h : Nat} (G1 rho : MatchingMap p h) :
    MatchingMap p h :=
  fun i => if rho i = none then G1 i else none

/-- On every encode image, the path sigma overlay is exactly G1 restricted
to the free pigeons of the base. -/
theorem decodeSigmaFromBase_encodeExt {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h)) :
    decodeSigmaFromBase (encodeExt rho D feed) rho =
      pairsToMatching
        (blockSigmas (blocksOf (vtrace rho D feed))).join := by
  funext i
  unfold decodeSigmaFromBase encodeExt
  by_cases hri : rho i = none
  · rw [if_pos hri, compose_free_left _ _ i hri]
  · have hri' : rho i ≠ none := hri
    rw [if_neg hri]
    cases hros : rho i with
    | none => exact absurd hros hri'
    | some a =>
        -- freshness: path sigma never lands on a rho-matched pigeon
        have hnone :
            pairsToMatching
                (blockSigmas (blocksOf (vtrace rho D feed))).join i =
              none := by
          cases hsm : pairsToMatching
              (blockSigmas (blocksOf (vtrace rho D feed))).join i with
          | none => rfl
          | some b =>
              have hm := pairsToMatching_eq_some _ i b hsm
              have hfr :=
                blockSigmas_join_fresh (freePigeons rho).card rho [] D feed
                  (i, b) (by simpa [vtrace] using hm)
              rw [hros] at hfr
              cases hfr.1
        exact hnone.symm

/-- On an encode image the dual recovers the path sigma, so base recovery
through the dual is the identity. -/
theorem decodeBasePoint_decodeSigmaFromBase_encodeExt {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (i : Fin p) :
    decodeBasePoint (encodeExt rho D feed)
        (decodeSigmaFromBase (encodeExt rho D feed) rho) i = rho i := by
  have hsig := decodeSigmaFromBase_encodeExt rho D feed
  rw [hsig]
  exact decodeBasePoint_encodeExt rho D feed i

/-- Packaged dual recovery on the `encodeMatch` image. -/
theorem encodeMatch_decodeSigmaFromBase {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let feed := leftmostLiveDeepFeed rho D t
    let code := encodeMatch hsq rho D hrho hell ht hw
    decodeSigmaFromBase code.G1 rho =
      pairsToMatching
        (blockSigmas (blocksOf (vtrace rho D feed))).join := by
  intro feed _code
  simpa [encodeMatch] using decodeSigmaFromBase_encodeExt rho D feed

private theorem blockSigmasBeta_eq_nil_iff {p h w : Nat} :
    ∀ Bs : List (VBlock p h),
      blockSigmasBeta (w := w) Bs = [] ↔ Bs = []
  | [] => by simp [blockSigmasBeta]
  | [B] => by simp [blockSigmasBeta]
  | B :: B' :: Bs => by simp [blockSigmasBeta]

/-- Empty G2 means empty path sigma, so G1 is already the base. -/
theorem encodeMatch_eq_of_code_eq_of_G2_nil
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
    (hG2 :
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 = []) :
    rho₁ = rho₂ := by
  have hG1 :
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 :=
    congrArg MatchEncode.G1 hcode
  have hG2₂ :
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 = [] := by
    have := congrArg MatchEncode.G2 hcode
    simpa [hG2] using this.symm
  have hblocks₁ :
      blocksOf (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t)) = [] := by
    have hβ :
        (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
          blockSigmasBeta (w := w)
            (blocksOf (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t))) := by
      simp [encodeMatch, traceBetaDeep, traceBeta]
    exact (blockSigmasBeta_eq_nil_iff _).mp (hβ.symm.trans hG2)
  have hblocks₂ :
      blocksOf (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t)) = [] := by
    have hβ :
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 =
          blockSigmasBeta (w := w)
            (blocksOf (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t))) := by
      simp [encodeMatch, traceBetaDeep, traceBeta]
    exact (blockSigmasBeta_eq_nil_iff _).mp (hβ.symm.trans hG2₂)
  have hsig₁ :
      pairsToMatching
          (blockSigmas (blocksOf
            (vtrace rho₁ D (leftmostLiveDeepFeed rho₁ D t)))).join =
        (emptyMatching p h) := by
    simp [hblocks₁, blockSigmas, pairsToMatching]
  have hsig₂ :
      pairsToMatching
          (blockSigmas (blocksOf
            (vtrace rho₂ D (leftmostLiveDeepFeed rho₂ D t)))).join =
        (emptyMatching p h) := by
    simp [hblocks₂, blockSigmas, pairsToMatching]
  have hr₁ :
      rho₁ = encodeExt rho₁ D (leftmostLiveDeepFeed rho₁ D t) := by
    funext i
    simpa [hsig₁, encodeExt, compose_empty_right] using
      (encodeExt_recover_base rho₁ D (leftmostLiveDeepFeed rho₁ D t) i).symm
  have hr₂ :
      rho₂ = encodeExt rho₂ D (leftmostLiveDeepFeed rho₂ D t) := by
    funext i
    simpa [hsig₂, encodeExt, compose_empty_right] using
      (encodeExt_recover_base rho₂ D (leftmostLiveDeepFeed rho₂ D t) i).symm
  calc
    rho₁ = encodeExt rho₁ D (leftmostLiveDeepFeed rho₁ D t) := hr₁
    _ = (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 := by
      simp [encodeMatch]
    _ = (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 := hG1
    _ = encodeExt rho₂ D (leftmostLiveDeepFeed rho₂ D t) := by
      simp [encodeMatch]
    _ = rho₂ := hr₂.symm

/-- Razborov/UF first-not-falsified scan: skip illegal and falsified terms.
Used by the multi-block prefix-replay residual (entered-term identification
under the satisfying overlay G1 = ρσ). -/
def firstNotFalsifiedTerm {p h : Nat} (mu : MatchingMap p h) :
    MDNF p h → Option (MTerm p h)
  | [] => none
  | t :: rest =>
      if termMatchingLegalB t = false then firstNotFalsifiedTerm mu rest
      else if termFalsifiedB mu t = true then firstNotFalsifiedTerm mu rest
      else some t

private theorem firstNotFalsifiedTerm_cons {p h : Nat} (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h) :
    firstNotFalsifiedTerm mu (t :: rest) =
      if termMatchingLegalB t = false then firstNotFalsifiedTerm mu rest
      else if termFalsifiedB mu t = true then firstNotFalsifiedTerm mu rest
      else some t :=
  rfl

/-- Factorization form of `firstNotFalsifiedTerm` (illegal/falsified prefix). -/
theorem firstNotFalsifiedTerm_eq_of_factor {p h : Nat} (mu : MatchingMap p h)
    (D : MDNF p h) (pre : List (MTerm p h)) (T : MTerm p h) (suf : MDNF p h)
    (hfactor : D = pre ++ T :: suf)
    (hpre : ∀ t' ∈ pre,
      termMatchingLegalB t' = false ∨ termFalsifiedB mu t' = true)
    (hTleg : termMatchingLegalB T = true)
    (hTnf : termFalsifiedB mu T = false) :
    firstNotFalsifiedTerm mu D = some T := by
  subst hfactor
  induction pre with
  | nil =>
      rw [List.nil_append, firstNotFalsifiedTerm_cons]
      simp [hTleg, hTnf]
  | cons p ps ih =>
      have hp := hpre p (List.mem_cons_self _ _)
      have hrest : ∀ t' ∈ ps,
          termMatchingLegalB t' = false ∨ termFalsifiedB mu t' = true :=
        fun t' ht' => hpre t' (List.mem_cons_of_mem _ ht')
      rw [List.cons_append, firstNotFalsifiedTerm_cons]
      rcases hp with hileg | hfals
      · simp only [hileg, ↓reduceIte]
        exact ih hrest
      · by_cases hileg' : termMatchingLegalB p = false
        · simp only [hileg', ↓reduceIte]
          exact ih hrest
        · have hleg' : termMatchingLegalB p = true :=
            Bool.eq_true_of_not_eq_false hileg'
          simp only [hleg', Bool.true_eq_false, ↓reduceIte, hfals]
          exact ih hrest

/-! ## S2198: genuine-head bridge under encode G1 -/

/-- First block of a root trace (empty pending) enters under the base matching. -/
private theorem blocksOf_vevents_nil_pending_head_entry {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (D : MDNF p h)
      (feed : List (Vertex p h)) (B : VBlock p h) (Bs : List (VBlock p h)),
      blocksOf (vevents fuel mu [] D feed) = B :: Bs →
      B.entry = mu
  | _, _, [], feed, B, Bs, hblocks => by
      rw [vevents_nil, blocksOf_nil] at hblocks
      cases hblocks
  | fuel, mu, t :: rest, feed, B, Bs, hblocks => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals] at hblocks
          exact blocksOf_vevents_nil_pending_head_entry fuel mu rest feed B Bs
            hblocks
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals' hsat,
              blocksOf_nil] at hblocks
            cases hblocks
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat',
                  blocksOf_nil] at hblocks
                cases hblocks
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t rest feed hleg
                      hfals' hsat' htv, blocksOf_nil] at hblocks
                    cases hblocks
                | cons v vs =>
                    cases v with
                    | inl i =>
                        cases feed with
                        | nil =>
                            rw [vevents_entry_feed_nil fuel' mu t rest i vs
                              hleg hfals' hsat' htv, blocksOf_nil] at hblocks
                            cases hblocks
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents_entry_feed_illkind fuel' mu t rest
                                  i vs q fs hleg hfals' hsat' htv,
                                  blocksOf_nil] at hblocks
                                cases hblocks
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv hha,
                                    blocksOf_nil] at hblocks
                                  cases hblocks
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t rest
                                    i vs a fs hleg hfals' hsat' htv hha',
                                    blocksOf_enter] at hblocks
                                  cases hblocks
                                  rfl
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg'] at hblocks
        exact blocksOf_vevents_nil_pending_head_entry fuel mu rest feed B Bs
          hblocks
  termination_by fuel _ D _ _ _ => (fuel, D.length)

private theorem pairsToMatching_mem_of_pairwise {p h : Nat} :
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
          exact pairsToMatching_mem_of_pairwise hpd.2 hm'

private theorem pairsToMatching_eq_none_of_not_mem_fst {p h : Nat} :
    ∀ (l : List (Fin p × Fin h)) (i : Fin p),
      (∀ a, (i, a) ∉ l) → pairsToMatching l i = none
  | [], i, _ => rfl
  | (j, b) :: es, i, hni => by
      rw [show pairsToMatching ((j, b) :: es) =
        compose (singleMatching j b) (pairsToMatching es) from rfl]
      by_cases hji : j = i
      · exact absurd (by rw [hji]; exact List.mem_cons_self _ _) (hni b)
      · have hsingle : singleMatching j b i = none := by
          unfold singleMatching
          rw [if_neg (Ne.symm hji)]
        rw [compose_free_left _ _ i hsingle]
        exact pairsToMatching_eq_none_of_not_mem_fst es i
          (fun a ha => hni a (List.mem_cons_of_mem _ ha))

/-- σ-join membership of a first-block full-σ pair, except last-block truncation. -/
private theorem mem_blockSigmas_join_of_mem_sigmaFull_head {p h : Nat}
    (B : VBlock p h) (Bs : List (VBlock p h)) (e : Fin p × Fin h)
    (he : e ∈ sigmaFull B) :
    e ∈ (blockSigmas (B :: Bs)).join ∨
      (Bs = [] ∧ e ∉ sigmaTrunc B) := by
  cases Bs with
  | nil =>
      rw [show blockSigmas [B] = [sigmaTrunc B] from rfl,
        List.join_cons, List.join_nil, List.append_nil]
      by_cases htr : e ∈ sigmaTrunc B
      · exact Or.inl htr
      · exact Or.inr ⟨rfl, htr⟩
  | cons B' Bs' =>
      rw [show blockSigmas (B :: B' :: Bs') =
        sigmaFull B :: blockSigmas (B' :: Bs') from rfl,
        List.join_cons]
      exact Or.inl (List.mem_append_left _ he)

private theorem pairFalsB_eq_false_of_pairSatB {p h : Nat}
    (mu : MatchingMap p h) (e : Fin p × Fin h)
    (hsat : pairSatB mu e = true) : pairFalsB mu e = false := by
  unfold pairSatB at hsat
  cases hmu : mu e.1 with
  | none =>
      simp [hmu] at hsat
  | some b =>
      have hb : b = e.2 := by simpa [hmu] using hsat
      unfold pairFalsB
      simp [hmu, hb]

private theorem pairSatB_of_eq_some {p h : Nat} (mu : MatchingMap p h)
    (e : Fin p × Fin h) (h : mu e.1 = some e.2) :
    pairSatB mu e = true := by
  unfold pairSatB
  simpa using h

/-- First entered term of a root trace is not falsified under `ρσ = encodeExt`. -/
private theorem termFalsifiedB_encodeExt_eq_false_of_head_block {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho) (B : VBlock p h) (Bs : List (VBlock p h))
    (hblocks : blocksOf (vtrace rho D feed) = B :: Bs) :
    termFalsifiedB (encodeExt rho D feed) B.term = false := by
  have hentry :
      B.entry = rho :=
    blocksOf_vevents_nil_pending_head_entry (freePigeons rho).card rho D feed
      B Bs (by simpa [vtrace] using hblocks)
  have hBmem : B ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]; exact List.mem_cons_self _ _
  have hspec :=
    blocksOf_entry_spec (freePigeons rho).card rho [] D feed B hBmem
  have hleg : termMatchingLegalB B.term = true := hspec.2.1
  have hnfals_entry : termFalsifiedB B.entry B.term = false := hspec.2.2.1
  rw [hentry] at hnfals_entry
  have hpd :
      List.Pairwise PairDisjoint
        (blockSigmas (blocksOf (vtrace rho D feed))).join :=
    blockSigmas_join_pairwise (freePigeons rho).card rho [] D feed
  rw [hblocks] at hpd
  let sigma := pairsToMatching (blockSigmas (B :: Bs)).join
  have hG1 : encodeExt rho D feed = compose rho sigma := by
    unfold encodeExt sigma
    rw [hblocks]
  have hfresh :
      ∀ e ∈ (blockSigmas (B :: Bs)).join,
        rho e.1 = none ∧ holeUsed rho e.2 = false := by
    intro e he
    have he' : e ∈ (blockSigmas (blocksOf (vtrace rho D feed))).join := by
      simpa [hblocks] using he
    exact blockSigmas_join_fresh (freePigeons rho).card rho [] D feed e he'
  have hsigma_none_of_rho :
      ∀ i a, rho i = some a → sigma i = none := by
    intro i a hi
    apply pairsToMatching_eq_none_of_not_mem_fst
    intro b hb
    have hfr := (hfresh (i, b) hb).1
    rw [hi] at hfr
    cases hfr
  have hG1m : IsMatching (encodeExt rho D feed) :=
    encodeExt_isMatching rho D feed hrho
  -- Show no pair of the head term is falsified under G1.
  unfold termFalsifiedB
  cases hany : B.term.any (pairFalsB (encodeExt rho D feed)) with
  | false => rfl
  | true =>
      rw [List.any_eq_true] at hany
      rcases hany with ⟨e, heT, hef⟩
      have hnfe : pairFalsB rho e = false := by
        cases hf : pairFalsB rho e with
        | false => rfl
        | true =>
            have htf : termFalsifiedB rho B.term = true := by
              unfold termFalsifiedB
              exact List.any_eq_true.mpr ⟨e, heT, hf⟩
            rw [hnfals_entry] at htf
            cases htf
      have htri := pair_status_trichotomy rho e
      have hnsat_or : pairSatB rho e = true ∨ pairUnresolvedB rho e = true := by
        cases hs : pairSatB rho e with
        | true => exact Or.inl rfl
        | false =>
            rw [hs, hnfe] at htri
            exact Or.inr (by simpa using htri)
      rcases hnsat_or with hsat | hunres
      · -- Already satisfied under ρ: survives into G1.
        have hrhoe : rho e.1 = some e.2 := by
          unfold pairSatB at hsat
          simpa using hsat
        have hG1e : encodeExt rho D feed e.1 = some e.2 := by
          rw [hG1, compose_fixed_left rho sigma e.1 e.2 hrhoe]
        have hsatG : pairSatB (encodeExt rho D feed) e = true :=
          pairSatB_of_eq_some _ e hG1e
        have hfalsG := pairFalsB_eq_false_of_pairSatB _ e hsatG
        rw [hfalsG] at hef
        cases hef
      · -- Unresolved under ρ: lies in σ′ of the head block.
        have heσ : e ∈ sigmaFull B := by
          rw [mem_sigmaFull]
          refine ⟨heT, ?_⟩
          simpa [hentry] using hunres
        rcases mem_blockSigmas_join_of_mem_sigmaFull_head B Bs e heσ with
          hmem | ⟨hBs, hntr⟩
        · -- Pair collected into ρσ: assigned correctly.
          have hsig : sigma e.1 = some e.2 :=
            pairsToMatching_mem_of_pairwise hpd hmem
          have hrho_none : rho e.1 = none := (hfresh e hmem).1
          have hG1e : encodeExt rho D feed e.1 = some e.2 := by
            rw [hG1, compose_free_left rho sigma e.1 hrho_none, hsig]
          have hsatG : pairSatB (encodeExt rho D feed) e = true :=
            pairSatB_of_eq_some _ e hG1e
          have hfalsG := pairFalsB_eq_false_of_pairSatB _ e hsatG
          rw [hfalsG] at hef
          cases hef
        · -- Last-block truncation: pair left free under ρσ, hole free.
          have hjoin : (blockSigmas (B :: Bs)).join = sigmaTrunc B := by
            subst hBs
            rw [show blockSigmas [B] = [sigmaTrunc B] from rfl,
              List.join_cons, List.join_nil, List.append_nil]
          have hnone_sigma : sigma e.1 = none := by
            apply pairsToMatching_eq_none_of_not_mem_fst
            intro b hb
            have hb' : (e.1, b) ∈ sigmaTrunc B := by
              simpa [hjoin] using hb
            have hbσ : (e.1, b) ∈ sigmaFull B :=
              sigmaTrunc_subset_sigmaFull B _ hb'
            have hpdB := sigmaFull_pairwise B hleg
            by_cases hbe : (e.1, b) = e
            · have : e ∈ sigmaTrunc B := by
                simpa [hbe] using hb'
              exact hntr this
            · exact (hpdB.forall pairDisjoint_symm hbσ heσ hbe).1 rfl
          unfold pairUnresolvedB at hunres
          rw [Bool.and_eq_true] at hunres
          have hrho_none : rho e.1 = none := by simpa using hunres.1
          have hhole_rho : holeUsed rho e.2 = false := by
            simpa using hunres.2
          have hG1e : encodeExt rho D feed e.1 = none := by
            rw [hG1, compose_free_left rho sigma e.1 hrho_none, hnone_sigma]
          have hhole_sigma : holeUsed sigma e.2 = false := by
            cases hs : holeUsed sigma e.2 with
            | false => rfl
            | true =>
                rcases (holeUsed_eq_true_iff sigma e.2).mp hs with ⟨j, hj⟩
                have hm : (j, e.2) ∈ (blockSigmas (B :: Bs)).join :=
                  pairsToMatching_eq_some _ j e.2 hj
                have hmtr : (j, e.2) ∈ sigmaTrunc B := by
                  simpa [hjoin] using hm
                have hmσ : (j, e.2) ∈ sigmaFull B :=
                  sigmaTrunc_subset_sigmaFull B _ hmtr
                have hpdB := sigmaFull_pairwise B hleg
                by_cases hje : (j, e.2) = e
                · have : e ∈ sigmaTrunc B := by
                    simpa [hje] using hmtr
                  exact absurd this hntr
                · exact absurd rfl
                    (hpdB.forall pairDisjoint_symm hmσ heσ hje).2
          have hhole_G1 : holeUsed (encodeExt rho D feed) e.2 = false := by
            rw [hG1,
              holeUsed_compose rho sigma hsigma_none_of_rho e.2,
              hhole_rho, hhole_sigma]
            rfl
          have hfalsG : pairFalsB (encodeExt rho D feed) e = false := by
            unfold pairFalsB
            rw [hG1e, hhole_G1]
          rw [hfalsG] at hef
          cases hef

/-- **S2198 head bridge (cons form).**  On every nonempty encode image the
first entered term is exactly the Razborov/UF first-not-falsified scan of
packet `G1` against `D`. -/
theorem enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons
    {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (T : MTerm p h) (rest : List (MTerm p h))
    (hcons : enteredTermsOf rho D t = T :: rest) :
    firstNotFalsifiedTerm
        (encodeMatch hsq rho D hrho hell ht hw).G1 D =
      some T := by
  let feed := leftmostLiveDeepFeed rho D t
  have hblocks_terms :
      (blocksOf (vtrace rho D feed)).map (fun B => B.term) = T :: rest := by
    simpa [enteredTermsOf, feed] using hcons
  have hne : blocksOf (vtrace rho D feed) ≠ [] := by
    intro hb
    rw [hb, List.map_nil] at hblocks_terms
    cases hblocks_terms
  rcases List.exists_cons_of_ne_nil hne with ⟨B, Bs, hblocks⟩
  have hT : B.term = T := by
    rw [hblocks, List.map_cons, List.cons.injEq] at hblocks_terms
    exact hblocks_terms.1
  have hentry :
      B.entry = rho :=
    blocksOf_vevents_nil_pending_head_entry (freePigeons rho).card rho D feed
      B Bs (by simpa [vtrace] using hblocks)
  have hBmem : B ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]; exact List.mem_cons_self _ _
  rcases blocksOf_entered_first (freePigeons rho).card rho [] D feed hrho B
      hBmem with ⟨pre, suf, hD, hpre⟩
  have hspec :=
    blocksOf_entry_spec (freePigeons rho).card rho [] D feed B hBmem
  have hleg : termMatchingLegalB B.term = true := hspec.2.1
  have hG1 :
      (encodeMatch hsq rho D hrho hell ht hw).G1 =
        encodeExt rho D feed := by
    simp [encodeMatch, feed]
  have hG1m : IsMatching (encodeExt rho D feed) :=
    encodeExt_isMatching rho D feed hrho
  have hag : MAgree rho (encodeExt rho D feed) := by
    simpa [encodeExt, feed] using
      (mAgree_compose_left rho
        (pairsToMatching
          (blockSigmas (blocksOf (vtrace rho D feed))).join))
  have hpreG1 : ∀ t' ∈ pre,
      termMatchingLegalB t' = false ∨
        termFalsifiedB (encodeExt rho D feed) t' = true := by
    intro t' ht'
    rcases hpre t' ht' with hileg | hfals
    · exact Or.inl hileg
    · right
      have hfalsρ : termFalsifiedB rho t' = true := by
        simpa [hentry] using hfals
      exact termFalsifiedB_mono hag hG1m t' hfalsρ
  have hTnf :
      termFalsifiedB (encodeExt rho D feed) B.term = false :=
    termFalsifiedB_encodeExt_eq_false_of_head_block rho D feed hrho B Bs
      hblocks
  have hscan :
      firstNotFalsifiedTerm (encodeExt rho D feed) D = some B.term :=
    firstNotFalsifiedTerm_eq_of_factor (encodeExt rho D feed) D pre B.term suf
      hD hpreG1 hleg hTnf
  rw [hG1, hscan, hT]

/-- **S2198 head bridge.**  Nonempty encode entered-term lists have head equal
to `firstNotFalsifiedTerm` under packet `G1`. -/
theorem enteredTermsOf_head_eq_firstNotFalsified_G1
    {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hne : enteredTermsOf rho D t ≠ []) :
    firstNotFalsifiedTerm
        (encodeMatch hsq rho D hrho hell ht hw).G1 D =
      some (enteredTermsOf rho D t).head! := by
  rcases List.exists_cons_of_ne_nil hne with ⟨T, rest, hcons⟩
  have hbridge :=
    enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq rho D hrho hell
      ht hw T rest hcons
  simpa [hcons, List.head!_cons] using hbridge

/-- **S2198 single-block residual slice.**  Equal codes with a length-1
entered-term list force equal entered-term sequences (head recovered from
shared `G1` via the head bridge). -/
theorem enteredTermsOf_eq_of_encodeMatch_eq_of_length_one
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
    (hlen : (enteredTermsOf rho₁ D t).length = 1) :
    enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
  have hlen₂ :
      (enteredTermsOf rho₂ D t).length = 1 := by
    have h1 := enteredTermsOf_length_eq_G2 hsq rho₁ D hrho₁ hell₁ ht₁ hw
    have h2 := enteredTermsOf_length_eq_G2 hsq rho₂ D hrho₂ hell₂ ht₂ hw
    have hG2 :
        (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 :=
      congrArg MatchEncode.G2 hcode
    calc
      (enteredTermsOf rho₂ D t).length =
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2.length := h2
      _ = (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2.length := by
        rw [hG2]
      _ = (enteredTermsOf rho₁ D t).length := h1.symm
      _ = 1 := hlen
  have hne₁ : enteredTermsOf rho₁ D t ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlen
    cases hlen
  have hne₂ : enteredTermsOf rho₂ D t ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlen₂
    cases hlen₂
  rcases List.exists_cons_of_ne_nil hne₁ with ⟨T₁, r₁, hc₁⟩
  rcases List.exists_cons_of_ne_nil hne₂ with ⟨T₂, r₂, hc₂⟩
  have hr₁ : r₁ = [] := by
    have : (T₁ :: r₁).length = 1 := by simpa [hc₁] using hlen
    simp only [List.length_cons] at this
    exact List.eq_nil_of_length_eq_zero (Nat.succ.inj this)
  have hr₂ : r₂ = [] := by
    have : (T₂ :: r₂).length = 1 := by simpa [hc₂] using hlen₂
    simp only [List.length_cons] at this
    exact List.eq_nil_of_length_eq_zero (Nat.succ.inj this)
  have hG1 :
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 :=
    congrArg MatchEncode.G1 hcode
  have hscan₁ :=
    enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq rho₁ D hrho₁
      hell₁ ht₁ hw T₁ r₁ hc₁
  have hscan₂ :=
    enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq rho₂ D hrho₂
      hell₂ ht₂ hw T₂ r₂ hc₂
  have hT : T₁ = T₂ := by
    have h :
        firstNotFalsifiedTerm
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 D = some T₁ :=
      hscan₁
    have h' :
        firstNotFalsifiedTerm
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 D = some T₂ := by
      rw [hG1, hscan₂]
    exact Option.some.inj (h.symm.trans h')
  rw [hc₁, hc₂, hr₁, hr₂, hT]

/-! ## S2199: first-block exit recovery and length-2 isolation -/

/-- Append of pair-lists is first-wins composition of their matchings. -/
theorem pairsToMatching_append {p h : Nat} :
    ∀ (l₁ l₂ : List (Fin p × Fin h)),
      pairsToMatching (l₁ ++ l₂) =
        compose (pairsToMatching l₁) (pairsToMatching l₂)
  | [], l₂ => by
      simp only [List.nil_append]
      funext i
      simp [pairsToMatching, compose, emptyMatching]
  | e :: es, l₂ => by
      rw [List.cons_append,
        show pairsToMatching (e :: (es ++ l₂)) =
          compose (singleMatching e.1 e.2) (pairsToMatching (es ++ l₂)) from rfl,
        show pairsToMatching (e :: es) =
          compose (singleMatching e.1 e.2) (pairsToMatching es) from rfl,
        pairsToMatching_append es l₂, compose_assoc]

/-- **S2199 block-entry bridge.**  Every entered block's term is exactly the
Razborov/UF first-not-falsified scan of `D` under that block's path entry. -/
theorem block_term_eq_firstNotFalsified_entry {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho) (B : VBlock p h)
    (hB : B ∈ blocksOf (vtrace rho D feed)) :
    firstNotFalsifiedTerm B.entry D = some B.term := by
  rcases blocksOf_entered_first (freePigeons rho).card rho [] D feed hrho B hB with
    ⟨pre, suf, hD, hpre⟩
  have hspec :=
    blocksOf_entry_spec (freePigeons rho).card rho [] D feed B hB
  exact firstNotFalsifiedTerm_eq_of_factor B.entry D pre B.term suf hD hpre
    hspec.2.1 hspec.2.2.1

/-- Encode-theoretic exit matching after the first entered block: base `ρ`
overlaid with that block's full σ′.  Empty-block traces leave the base
unchanged. -/
def firstBlockExitMatching {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (t : Nat) : MatchingMap p h :=
  match blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) with
  | [] => rho
  | B :: _ => compose rho (pairsToMatching (sigmaFull B))

/-- Path entry of the second entered block, when the entered-term list has
length at least two; otherwise `none`. -/
def secondBlockEntry? {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (t : Nat) : Option (MatchingMap p h) :=
  match blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) with
  | _ :: B₁ :: _ => some B₁.entry
  | _ => none

theorem firstBlockExitMatching_nil {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (t : Nat)
    (hblocks : blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) = []) :
    firstBlockExitMatching rho D t = rho := by
  simp only [firstBlockExitMatching, hblocks]

theorem firstBlockExitMatching_cons {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (t : Nat) (B : VBlock p h) (Bs : List (VBlock p h))
    (hblocks :
      blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) = B :: Bs) :
    firstBlockExitMatching rho D t =
      compose rho (pairsToMatching (sigmaFull B)) := by
  simp only [firstBlockExitMatching, hblocks]

/-- On every nonempty first-block encode image, the exit is `ρ` composed with
the first block's full σ′. -/
theorem firstBlockExit_eq_of_encode_image {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (B : VBlock p h) (Bs : List (VBlock p h))
    (hblocks :
      blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) = B :: Bs) :
    firstBlockExitMatching rho D t =
      compose rho (pairsToMatching (sigmaFull B)) :=
  firstBlockExitMatching_cons rho D t B Bs hblocks

/-- Length-≥2 factorization: packet `G1` is the first-block exit overlaid with
the join of all later block σ's. -/
theorem encodeExt_eq_compose_firstBlockExit_of_length_ge_two {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (B₀ B₁ : VBlock p h) (rest : List (VBlock p h))
    (hblocks : blocksOf (vtrace rho D feed) = B₀ :: B₁ :: rest) :
    encodeExt rho D feed =
      compose (compose rho (pairsToMatching (sigmaFull B₀)))
        (pairsToMatching (blockSigmas (B₁ :: rest)).join) := by
  unfold encodeExt
  have hσ :
      blockSigmas (blocksOf (vtrace rho D feed)) =
        sigmaFull B₀ :: blockSigmas (B₁ :: rest) := by
    rw [hblocks]
    rfl
  rw [hσ, List.join_cons, pairsToMatching_append, compose_assoc]

/-- Encode-image form of the length-≥2 `G1` factorization. -/
theorem encodeMatch_G1_eq_compose_firstBlockExit_of_length_ge_two
    {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (B₀ B₁ : VBlock p h) (rest : List (VBlock p h))
    (hblocks :
      blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) =
        B₀ :: B₁ :: rest) :
    (encodeMatch hsq rho D hrho hell ht hw).G1 =
      compose (firstBlockExitMatching rho D t)
        (pairsToMatching (blockSigmas (B₁ :: rest)).join) := by
  have hG1 :
      (encodeMatch hsq rho D hrho hell ht hw).G1 =
        encodeExt rho D (leftmostLiveDeepFeed rho D t) := by
    simp [encodeMatch]
  rw [hG1, encodeExt_eq_compose_firstBlockExit_of_length_ge_two rho D _
    B₀ B₁ rest hblocks, firstBlockExitMatching_cons rho D t B₀ (B₁ :: rest)
    hblocks]

/-- **S2199 second-head bridge (path entry).**  On every length-≥2 encode
image the second entered term is the UF first-not-falsified scan of `D`
under the second block's path entry. -/
theorem enteredTermsOf_second_eq_firstNotFalsified_exit
    {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (T₀ T₁ : MTerm p h) (rest : List (MTerm p h))
    (hcons : enteredTermsOf rho D t = T₀ :: T₁ :: rest) :
    ∃ exit : MatchingMap p h,
      secondBlockEntry? rho D t = some exit ∧
        firstNotFalsifiedTerm exit D = some T₁ := by
  let feed := leftmostLiveDeepFeed rho D t
  have hblocks_terms :
      (blocksOf (vtrace rho D feed)).map (fun B => B.term) =
        T₀ :: T₁ :: rest := by
    simpa [enteredTermsOf, feed] using hcons
  have hne : blocksOf (vtrace rho D feed) ≠ [] := by
    intro hb
    rw [hb, List.map_nil] at hblocks_terms
    cases hblocks_terms
  rcases List.exists_cons_of_ne_nil hne with ⟨B₀, Bs, hblocks₀⟩
  have hBs_ne : Bs ≠ [] := by
    intro hBs
    have hlen :
        ((blocksOf (vtrace rho D feed)).map (fun B => B.term)).length =
          (T₀ :: T₁ :: rest).length := by
      rw [hblocks_terms]
    rw [hblocks₀, hBs, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil, List.length_cons, List.length_cons] at hlen
    exact absurd hlen (by omega)
  rcases List.exists_cons_of_ne_nil hBs_ne with ⟨B₁, restB, hBs⟩
  have hblocks : blocksOf (vtrace rho D feed) = B₀ :: B₁ :: restB := by
    rw [hblocks₀, hBs]
  have hT₁ : B₁.term = T₁ := by
    have hmt :
        B₀.term :: B₁.term :: restB.map (fun B => B.term) =
          T₀ :: T₁ :: rest := by
      simpa [hblocks, List.map_cons] using hblocks_terms
    exact (List.cons.inj (List.cons.inj hmt).2).1
  have hB₁mem : B₁ ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]
    exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
  refine ⟨B₁.entry, ?_, ?_⟩
  · simp only [secondBlockEntry?, feed, hblocks]
  · have hscan :=
      block_term_eq_firstNotFalsified_entry rho D feed hrho B₁ hB₁mem
    simpa [hT₁] using hscan

/-- Second-block path entry, exposed when the entered-term list has length ≥ 2. -/
theorem secondBlockEntry?_eq_some_of_length_ge_two
    {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h) (t : Nat)
    (hlen : 2 ≤ (enteredTermsOf rho D t).length) :
    ∃ exit, secondBlockEntry? rho D t = some exit := by
  let feed := leftmostLiveDeepFeed rho D t
  have hlen' : 2 ≤ (blocksOf (vtrace rho D feed)).length := by
    simpa [enteredTermsOf, feed, List.length_map] using hlen
  match hblocks : blocksOf (vtrace rho D feed) with
  | [] =>
      rw [hblocks, List.length_nil] at hlen'
      exact absurd hlen' (by omega)
  | [B] =>
      rw [hblocks, List.length_singleton] at hlen'
      exact absurd hlen' (by omega)
  | B₀ :: B₁ :: rest =>
      exact ⟨B₁.entry, by simp [secondBlockEntry?, feed, hblocks]⟩

/-! ## S2200: path second-entry vs σ-exit; packet first-σ recovery -/

/-- Overlaying a block's full σ′ onto its entry satisfies the entered term:
already-satisfied pairs survive, and every still-unresolved pair is assigned
exactly by the pairwise-disjoint σ′ matching. -/
theorem termSatisfiedB_compose_entry_sigmaFull {p h : Nat} (B : VBlock p h)
    (hleg : termMatchingLegalB B.term = true)
    (hnf : termFalsifiedB B.entry B.term = false) :
    termSatisfiedB
      (compose B.entry (pairsToMatching (sigmaFull B))) B.term = true := by
  unfold termSatisfiedB
  rw [List.all_eq_true]
  intro e he
  have hnfals_e : pairFalsB B.entry e = false := by
    unfold termFalsifiedB at hnf
    have hany : B.term.any (pairFalsB B.entry) = false := hnf
    exact Bool.eq_false_iff.mpr ((List.any_eq_false.mp hany) e he)
  have hpd : List.Pairwise PairDisjoint (sigmaFull B) :=
    sigmaFull_pairwise B hleg
  by_cases hsat : pairSatB B.entry e = true
  · unfold pairSatB at hsat ⊢
    cases hmu : B.entry e.1 with
    | none => simp [hmu] at hsat
    | some b =>
        have hb : b = e.2 := by simpa [hmu, beq_iff_eq] using hsat
        rw [compose_fixed_left _ _ e.1 b hmu, hb]
        simp
  · have hsatf : pairSatB B.entry e = false := Bool.eq_false_iff.mpr hsat
    have hunres : pairUnresolvedB B.entry e = true := by
      have htri := pair_status_trichotomy B.entry e
      simp only [hsatf, hnfals_e, Bool.false_or, Bool.or_false] at htri
      exact htri
    have heσ : e ∈ sigmaFull B := (mem_sigmaFull B e).mpr ⟨he, hunres⟩
    have hfree : B.entry e.1 = none := by
      unfold pairUnresolvedB at hunres
      simp only [Bool.and_eq_true, beq_iff_eq] at hunres
      exact hunres.1
    have hassign : pairsToMatching (sigmaFull B) e.1 = some e.2 :=
      pairsToMatching_mem_of_pairwise hpd heσ
    unfold pairSatB
    rw [compose_free_left _ _ e.1 hfree, hassign]
    simp

/-- Satisfied terms are not falsified. -/
theorem termFalsifiedB_eq_false_of_termSatisfiedB {p h : Nat}
    (mu : MatchingMap p h) (t : MTerm p h)
    (hsat : termSatisfiedB mu t = true) :
    termFalsifiedB mu t = false := by
  unfold termSatisfiedB at hsat
  unfold termFalsifiedB
  apply Bool.eq_false_iff.mpr
  intro hany
  rcases List.any_eq_true.mp hany with ⟨e, he, hf⟩
  have hs := (List.all_eq_true.mp hsat) e he
  have hnf := pairFalsB_eq_false_of_pairSatB mu e hs
  exact Bool.noConfusion (hf.symm.trans hnf)

/-! ### S2200 kernel witness: path second-entry ≠ σ-exit

On a multi-block root walk that drains the singleton term `[(0,0)]` by the
off-diagonal pairs `(0,1),(1,0)` and then opens a later block, the path
matching at the second entry is `{0↦1,1↦0}` while the first-block σ-exit
`compose entry (pairsToMatching σ′)` is `{0↦0}`.  This is the structural
reason `secondBlockEntry? ≠ some firstBlockExitMatching` on length-≥2
images: path entry tracks walked pairs; the encode exit tracks σ′.
-/

/-- First block of the S2200 witness: enter `[(0,0)]` under empty base and
walk the off-diagonal pairs that cover its frozen vertices. -/
def exitBridgeB0 : VBlock 3 3 :=
  ⟨[((0 : Fin 3), (0 : Fin 3))], emptyMatching 3 3,
    [⟨Sum.inl 0, ((0 : Fin 3), (1 : Fin 3))⟩,
      ⟨Sum.inr 0, ((1 : Fin 3), (0 : Fin 3))⟩]⟩

/-- Path matching after the first witness block (second-block entry). -/
def exitBridgePathEntry : MatchingMap 3 3 :=
  compose (compose (emptyMatching 3 3) (singleMatching (0 : Fin 3) 1))
    (singleMatching (1 : Fin 3) 0)

/-- Encode-theoretic first-block σ-exit of the witness. -/
def exitBridgeSigmaExit : MatchingMap 3 3 :=
  compose exitBridgeB0.entry (pairsToMatching (sigmaFull exitBridgeB0))

private theorem exitBridgeB0_sigmaFull :
    sigmaFull exitBridgeB0 = [((0 : Fin 3), (0 : Fin 3))] := by
  unfold exitBridgeB0 sigmaFull pairUnresolvedB
  simp [emptyMatching, holeUsed, finList]

private theorem exitBridgePathEntry_zero :
    exitBridgePathEntry (0 : Fin 3) = some (1 : Fin 3) := by
  simp [exitBridgePathEntry, compose, singleMatching, emptyMatching]

private theorem exitBridgeSigmaExit_zero :
    exitBridgeSigmaExit (0 : Fin 3) = some (0 : Fin 3) := by
  unfold exitBridgeSigmaExit
  rw [exitBridgeB0_sigmaFull]
  simp [exitBridgeB0, compose, pairsToMatching, singleMatching, emptyMatching]

/-- **S2200 kernel counterexample.**  Path second-entry after the walked
off-diagonal drain is not the first-block σ-exit. -/
theorem exitBridge_second_entry_ne_sigma_exit :
    exitBridgePathEntry ≠ exitBridgeSigmaExit := by
  intro heq
  have h0 : exitBridgePathEntry (0 : Fin 3) = exitBridgeSigmaExit (0 : Fin 3) :=
    congrArg (fun m : MatchingMap 3 3 => m (0 : Fin 3)) heq
  rw [exitBridgePathEntry_zero, exitBridgeSigmaExit_zero] at h0
  have : (1 : Fin 3) = 0 := Option.some.inj h0
  exact absurd this (by decide)

/-- σ-exit satisfies the first entered term (instance of the general lemma). -/
theorem exitBridge_sigma_exit_satisfies_first_term :
    termSatisfiedB exitBridgeSigmaExit exitBridgeB0.term = true := by
  have hleg : termMatchingLegalB exitBridgeB0.term = true := by
    unfold exitBridgeB0 termMatchingLegalB hasDupB
    decide
  have hnf : termFalsifiedB exitBridgeB0.entry exitBridgeB0.term = false := by
    unfold exitBridgeB0 termFalsifiedB pairFalsB
    simp [emptyMatching, holeUsed, finList]
  simpa [exitBridgeSigmaExit] using
    termSatisfiedB_compose_entry_sigmaFull exitBridgeB0 hleg hnf

/-- Path second-entry falsifies the first entered term (so a later block can
open). -/
theorem exitBridge_path_entry_falsifies_first_term :
    termFalsifiedB exitBridgePathEntry exitBridgeB0.term = true := by
  unfold exitBridgePathEntry exitBridgeB0 termFalsifiedB pairFalsB
  simp [compose, singleMatching, emptyMatching]

/-- Packet-side first-block σ-set candidate: UF head under `G1` plus the
leading G2 β-mark, independent of `ρ`. -/
noncomputable def packetFirstBlockSigma {p h w t ell : Nat}
    (code : MatchEncode p h w t ell) (D : MDNF p h) :
    Option (Finset (Fin p × Fin h)) :=
  match firstNotFalsifiedTerm code.G1 D, code.G2 with
  | some T, beta :: _ => some (decodeSigmaBlock T beta)
  | _, _ => none

/-- Equal codes force equal packet-recovered first-block σ candidates
(both sides read only `(G1,G2)` and `D`). -/
theorem packetFirstBlockSigma_eq_of_encodeMatch_eq
    {p h w t ell : Nat}
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    {hsq : p = h}
    (hcode : encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
      encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw) :
    packetFirstBlockSigma (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw) D =
      packetFirstBlockSigma (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw) D := by
  simp only [packetFirstBlockSigma, hcode]

/-- On a nonempty encode image the packet head recovers the true first
entered term together with the leading β-decoded σ-block. -/
theorem packetFirstBlockSigma_eq_decode_head_of_encode_image
    {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (B : VBlock p h) (Bs : List (VBlock p h))
    (hblocks :
      blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) = B :: Bs) :
    ∃ beta betas,
      (encodeMatch hsq rho D hrho hell ht hw).G2 = beta :: betas ∧
        firstNotFalsifiedTerm
            (encodeMatch hsq rho D hrho hell ht hw).G1 D =
          some B.term ∧
        packetFirstBlockSigma (encodeMatch hsq rho D hrho hell ht hw) D =
          some (decodeSigmaBlock B.term beta) := by
  let code := encodeMatch hsq rho D hrho hell ht hw
  have hG2 :
      code.G2 =
        blockSigmasBeta (w := w)
          (blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t))) := by
    simp [code, encodeMatch, traceBetaDeep, traceBeta]
  rw [hblocks] at hG2
  have hβne : code.G2 ≠ [] := by
    intro hnil
    have : blockSigmasBeta (w := w) (B :: Bs) = [] := hG2.symm.trans hnil
    exact absurd this (by cases Bs <;> simp [blockSigmasBeta] at this)
  rcases List.exists_cons_of_ne_nil hβne with ⟨beta, betas, hβ⟩
  have hne : enteredTermsOf rho D t ≠ [] := by
    intro h
    have : (B :: Bs).map (fun c => c.term) = [] := by
      simpa [enteredTermsOf, hblocks] using h
    cases this
  rcases List.exists_cons_of_ne_nil hne with ⟨T, rest, hcons⟩
  have hT : B.term = T := by
    have : (B :: Bs).map (fun c => c.term) = T :: rest := by
      simpa [enteredTermsOf, hblocks] using hcons
    exact (List.cons.inj this).1
  have hscan :=
    enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq rho D hrho hell
      ht hw T rest hcons
  have hhead : firstNotFalsifiedTerm code.G1 D = some B.term := by
    simpa [code, hT] using hscan
  refine ⟨beta, betas, hβ, hhead, ?_⟩
  -- Unfold the packet decoder on the concrete `some`/`cons` shape.
  show packetFirstBlockSigma code D = some (decodeSigmaBlock B.term beta)
  simp only [packetFirstBlockSigma, hhead, hβ]

/-- **S2199 length-2 isolation.**  Equal codes with length-2 entered terms and
equal second-block path entries force equal entered-term sequences (head from
shared `G1` via the S2198 bridge; second from the shared exit via the
second-head bridge). -/
theorem enteredTermsOf_eq_of_encodeMatch_eq_of_length_two_of_exit_eq
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
    (hlen : (enteredTermsOf rho₁ D t).length = 2)
    (hexit : secondBlockEntry? rho₁ D t = secondBlockEntry? rho₂ D t) :
    enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
  have hlen₂ :
      (enteredTermsOf rho₂ D t).length = 2 := by
    have h1 := enteredTermsOf_length_eq_G2 hsq rho₁ D hrho₁ hell₁ ht₁ hw
    have h2 := enteredTermsOf_length_eq_G2 hsq rho₂ D hrho₂ hell₂ ht₂ hw
    have hG2 :
        (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 :=
      congrArg MatchEncode.G2 hcode
    calc
      (enteredTermsOf rho₂ D t).length =
          (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2.length := h2
      _ = (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2.length := by
        rw [hG2]
      _ = (enteredTermsOf rho₁ D t).length := h1.symm
      _ = 2 := hlen
  have hne₁ : enteredTermsOf rho₁ D t ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen; cases hlen
  have hne₂ : enteredTermsOf rho₂ D t ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen₂; cases hlen₂
  rcases List.exists_cons_of_ne_nil hne₁ with ⟨T₁, r₁, hc₁⟩
  rcases List.exists_cons_of_ne_nil hne₂ with ⟨T₂, r₂, hc₂⟩
  have hr₁_ne : r₁ ≠ [] := by
    intro hr
    have : (T₁ :: r₁).length = 2 := by simpa [hc₁] using hlen
    simp only [hr, List.length_cons, List.length_nil] at this
    cases this
  have hr₂_ne : r₂ ≠ [] := by
    intro hr
    have : (T₂ :: r₂).length = 2 := by simpa [hc₂] using hlen₂
    simp only [hr, List.length_cons, List.length_nil] at this
    cases this
  rcases List.exists_cons_of_ne_nil hr₁_ne with ⟨U₁, s₁, hr₁⟩
  rcases List.exists_cons_of_ne_nil hr₂_ne with ⟨U₂, s₂, hr₂⟩
  have hs₁ : s₁ = [] := by
    have : (T₁ :: U₁ :: s₁).length = 2 := by
      simpa [hc₁, hr₁] using hlen
    simp only [List.length_cons] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hs₂ : s₂ = [] := by
    have : (T₂ :: U₂ :: s₂).length = 2 := by
      simpa [hc₂, hr₂] using hlen₂
    simp only [List.length_cons] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hG1 :
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G1 :=
    congrArg MatchEncode.G1 hcode
  have hscan₁ :=
    enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq rho₁ D hrho₁
      hell₁ ht₁ hw T₁ (U₁ :: s₁) (by simpa [hr₁] using hc₁)
  have hscan₂ :=
    enteredTermsOf_head_eq_firstNotFalsified_G1_of_cons hsq rho₂ D hrho₂
      hell₂ ht₂ hw T₂ (U₂ :: s₂) (by simpa [hr₂] using hc₂)
  have hT : T₁ = T₂ := by
    have h :
        firstNotFalsifiedTerm
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 D = some T₁ :=
      hscan₁
    have h' :
        firstNotFalsifiedTerm
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G1 D = some T₂ := by
      rw [hG1, hscan₂]
    exact Option.some.inj (h.symm.trans h')
  rcases enteredTermsOf_second_eq_firstNotFalsified_exit hsq rho₁ D hrho₁
      hell₁ ht₁ hw T₁ U₁ s₁ (by simpa [hr₁, hs₁] using hc₁) with
    ⟨exit₁, hex₁, hU₁⟩
  rcases enteredTermsOf_second_eq_firstNotFalsified_exit hsq rho₂ D hrho₂
      hell₂ ht₂ hw T₂ U₂ s₂ (by simpa [hr₂, hs₂] using hc₂) with
    ⟨exit₂, hex₂, hU₂⟩
  have hexit' : some exit₁ = some exit₂ := by
    calc
      some exit₁ = secondBlockEntry? rho₁ D t := hex₁.symm
      _ = secondBlockEntry? rho₂ D t := hexit
      _ = some exit₂ := hex₂
  have hexit_eq : exit₁ = exit₂ := Option.some.inj hexit'
  have hU : U₁ = U₂ := by
    have h : firstNotFalsifiedTerm exit₁ D = some U₁ := hU₁
    have h' : firstNotFalsifiedTerm exit₁ D = some U₂ := by
      rw [hexit_eq, hU₂]
    exact Option.some.inj (h.symm.trans h')
  rw [hc₁, hc₂, hr₁, hr₂, hs₁, hs₂, hT, hU]

/-- Length-≤2 residual under a global second-entry agreement hypothesis on
equal-code pairs (sufficient packaging; not discharged in general). -/
def EncodeMatchLengthTwoExitEqResidual {p h w t ell : Nat} (hsq : p = h)
    (D : MDNF p h) (hw : ∀ term ∈ D, term.length ≤ w) : Prop :=
  ∀ (rho₁ rho₂ : MatchingMap p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂)),
    encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
        encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw →
      (enteredTermsOf rho₁ D t).length = 2 →
        secondBlockEntry? rho₁ D t = secondBlockEntry? rho₂ D t

/-- Coherent overlay agreement upgrades to full `G1 = compose rho sigma`
when `rho` is the base decoder strip of that overlay. -/
theorem compose_decodeBasePoint_of_overlayAgreesG1 {p h : Nat}
    (G1 sigma : MatchingMap p h) (hagree : OverlayAgreesG1 G1 sigma) :
    compose (fun i => decodeBasePoint G1 sigma i) sigma = G1 := by
  funext i
  dsimp only [compose, decodeBasePoint]
  split_ifs with hs
  · -- sigma i = none: left branch of compose is G1 i
    cases hG : G1 i <;> simp [hs, hG]
  · -- sigma i ≠ none
    rcases Option.ne_none_iff_exists'.mp hs with ⟨a, hsig⟩
    have hG1 : G1 i = some a := hagree i a hsig
    simp [hsig, hG1]

/-- On every encode image the entered-term list is empty iff G2 is empty. -/
theorem enteredTermsOf_eq_nil_iff_G2_nil {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    enteredTermsOf rho D t = [] ↔
      (encodeMatch hsq rho D hrho hell ht hw).G2 = [] := by
  constructor
  · intro hterms
    have hlen := enteredTermsOf_length_eq_G2 hsq rho D hrho hell ht hw
    rw [hterms, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  · intro hG2
    have hβ :
        (encodeMatch hsq rho D hrho hell ht hw).G2 =
          blockSigmasBeta (w := w)
            (blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t))) := by
      simp [encodeMatch, traceBetaDeep, traceBeta]
    have hblocks :
        blocksOf (vtrace rho D (leftmostLiveDeepFeed rho D t)) = [] :=
      (blockSigmasBeta_eq_nil_iff _).mp (hβ.symm.trans hG2)
    simp [enteredTermsOf, hblocks]

/-- **S2197 empty-G2 entered-term recovery.** Equal codes with empty G2 force
equal (empty) entered-term sequences. -/
theorem enteredTermsOf_eq_of_encodeMatch_eq_of_G2_nil
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
    (hG2 : (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 = []) :
    enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t := by
  have hG2₂ :
      (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 = [] := by
    have := congrArg MatchEncode.G2 hcode
    simpa [hG2] using this.symm
  have h1 :
      enteredTermsOf rho₁ D t = [] :=
    (enteredTermsOf_eq_nil_iff_G2_nil hsq rho₁ D hrho₁ hell₁ ht₁ hw).mpr hG2
  have h2 :
      enteredTermsOf rho₂ D t = [] :=
    (enteredTermsOf_eq_nil_iff_G2_nil hsq rho₂ D hrho₂ hell₂ ht₂ hw).mpr hG2₂
  exact h1.trans h2.symm

/-- **S2197 length transport.** Equal `encodeMatch` codes force equal entered-term
list lengths (both equal the common G2 length). -/
theorem enteredTermsOf_length_eq_of_encodeMatch_eq
    {p h w t ell : Nat} (hsq : p = h)
    (rho₁ rho₂ : MatchingMap p h) (D : MDNF p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂))
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hcode : encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
      encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw) :
    (enteredTermsOf rho₁ D t).length = (enteredTermsOf rho₂ D t).length := by
  have h1 := enteredTermsOf_length_eq_G2 hsq rho₁ D hrho₁ hell₁ ht₁ hw
  have h2 := enteredTermsOf_length_eq_G2 hsq rho₂ D hrho₂ hell₂ ht₂ hw
  have hG2 :
      (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 =
        (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2 :=
    congrArg MatchEncode.G2 hcode
  calc
    (enteredTermsOf rho₁ D t).length =
        (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2.length := h1
    _ = (encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw).G2.length := by
      rw [hG2]
    _ = (enteredTermsOf rho₂ D t).length := h2.symm

/-- **S2197 residual (active).** Full multi-block
`enteredTermsOf_eq_of_encodeMatch_eq` — equal codes alone force equal entered-term
sequences on encode images.  Empty-G2 and length-1 cases are discharged
(`enteredTermsOf_eq_of_encodeMatch_eq_of_G2_nil`,
`enteredTermsOf_eq_of_encodeMatch_eq_of_length_one` / S2198 head bridge).
Length-2 is conditional on second-block path-entry agreement
(`enteredTermsOf_eq_of_encodeMatch_eq_of_length_two_of_exit_eq` / S2199);
`EncodeMatchLengthTwoExitEqResidual` packages the missing exit-recovery step.
S2200 refutes identifying path second-entry with the first-block σ-exit
(`exitBridge_second_entry_ne_sigma_exit`) and lands packet recovery of the
first-block σ-set from `(G1,G2)` head data
(`packetFirstBlockSigma_eq_decode_head_of_encode_image`); path second-entry
recovery from the packet alone remains open.  Combined with
`encodeMatch_eq_of_code_eq_of_entered_terms_eq` this yields unconditional
`encodeMatch_eq_of_code_eq` / `encodeMatch_subtype_injective`.

Alternative (stronger) sufficient residual: `EncodeMatchCoherentReplayUniqueResidual`
(S2196) — not proved equivalent; it quantifies over all coherent candidates,
while this residual compares only genuine encode preimages.  Obstruction: G3
answer codes are indices into `freeVertexList rho`, so pure multi-block term
replay past the head still needs base/free-list / path second-entry recovery
from the packet alone. -/
def EncodeMatchEnteredTermsEqResidual {p h w t ell : Nat} (hsq : p = h)
    (D : MDNF p h) (hw : ∀ term ∈ D, term.length ≤ w) : Prop :=
  ∀ (rho₁ rho₂ : MatchingMap p h)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT D rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT D rho₂)),
    encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw =
        encodeMatch hsq rho₂ D hrho₂ hell₂ ht₂ hw →
      enteredTermsOf rho₁ D t = enteredTermsOf rho₂ D t

/-- Full base equality from equal codes, given the S2197 entered-term residual. -/
theorem encodeMatch_eq_of_code_eq_of_enteredTermsEqResidual
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
    (hres : EncodeMatchEnteredTermsEqResidual (t := t) (ell := ell) (w := w)
      hsq D hw) :
    rho₁ = rho₂ :=
  encodeMatch_eq_of_code_eq_of_entered_terms_eq hsq
    rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
    (by
      simpa [enteredTermsOf] using
        hres rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode)

/-- Subtype injectivity from the S2197 entered-term residual. -/
theorem encodeMatch_subtype_injective_of_enteredTermsEqResidual
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hres : EncodeMatchEnteredTermsEqResidual (t := t) (ell := ell) (w := w)
      hsq D hw) :
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
  apply Subtype.ext
  exact encodeMatch_eq_of_code_eq_of_enteredTermsEqResidual hsq
    rho₁.1 rho₂.1 D hmem₁.1.1 hmem₂.1.1 hmem₁.1.2 hmem₂.1.2
    ht₁ ht₂ hw hcode' hres

/-- If every eligible encode image has empty G2, the full S2197 residual
holds (via the pairwise empty-G2 equality theorem).  This is a global
empty-G2 hypothesis on the family, not a restriction of the residual's
domain to an empty-G2 subtype. -/
theorem encodeMatchEnteredTermsEqResidual_of_G2_nil
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hnil :
      ∀ (rho : MatchingMap p h) (hrho : IsMatching rho)
        (hell : (freePigeons rho).card = ell)
        (ht : t ≤ vmdtDepth (canonicalVMDT D rho)),
        (encodeMatch hsq rho D hrho hell ht hw).G2 = []) :
    EncodeMatchEnteredTermsEqResidual (t := t) (ell := ell) (w := w)
      hsq D hw := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode
  exact enteredTermsOf_eq_of_encodeMatch_eq_of_G2_nil hsq
    rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
    (hnil rho₁ hrho₁ hell₁ ht₁)

/-- Length-≤1 entered-term images discharge the S2197 residual (empty via
G2-nil; singleton via the S2198 head bridge). -/
theorem encodeMatchEnteredTermsEqResidual_of_length_le_one
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hbound :
      ∀ (rho : MatchingMap p h) (hrho : IsMatching rho)
        (hell : (freePigeons rho).card = ell)
        (ht : t ≤ vmdtDepth (canonicalVMDT D rho)),
        (enteredTermsOf rho D t).length ≤ 1) :
    EncodeMatchEnteredTermsEqResidual (t := t) (ell := ell) (w := w)
      hsq D hw := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode
  have hlen₁ := hbound rho₁ hrho₁ hell₁ ht₁
  match hlt : (enteredTermsOf rho₁ D t).length with
  | 0 =>
      have hnil₁ : enteredTermsOf rho₁ D t = [] :=
        List.eq_nil_of_length_eq_zero (by simpa [hlt] using rfl)
      have hG2 :
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 = [] :=
        (enteredTermsOf_eq_nil_iff_G2_nil hsq rho₁ D hrho₁ hell₁ ht₁ hw).mp
          hnil₁
      exact enteredTermsOf_eq_of_encodeMatch_eq_of_G2_nil hsq
        rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode hG2
  | 1 =>
      exact enteredTermsOf_eq_of_encodeMatch_eq_of_length_one hsq
        rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
        (by simpa [hlt])
  | n + 2 =>
      have : (enteredTermsOf rho₁ D t).length ≤ 1 := hlen₁
      rw [hlt] at this
      exact absurd this (by omega)

/-- Length-≤2 entered-term residual from the S2198 length-≤1 discharge plus
the S2199 exit-agreement residual on length-2 images. -/
theorem encodeMatchEnteredTermsEqResidual_of_length_le_two_of_exit
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hbound :
      ∀ (rho : MatchingMap p h) (hrho : IsMatching rho)
        (hell : (freePigeons rho).card = ell)
        (ht : t ≤ vmdtDepth (canonicalVMDT D rho)),
        (enteredTermsOf rho D t).length ≤ 2)
    (hexit : EncodeMatchLengthTwoExitEqResidual (t := t) (ell := ell) (w := w)
      hsq D hw) :
    EncodeMatchEnteredTermsEqResidual (t := t) (ell := ell) (w := w)
      hsq D hw := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode
  have hlen₁ := hbound rho₁ hrho₁ hell₁ ht₁
  match hlt : (enteredTermsOf rho₁ D t).length with
  | 0 =>
      have hnil₁ : enteredTermsOf rho₁ D t = [] :=
        List.eq_nil_of_length_eq_zero (by simpa [hlt] using rfl)
      have hG2 :
          (encodeMatch hsq rho₁ D hrho₁ hell₁ ht₁ hw).G2 = [] :=
        (enteredTermsOf_eq_nil_iff_G2_nil hsq rho₁ D hrho₁ hell₁ ht₁ hw).mp
          hnil₁
      exact enteredTermsOf_eq_of_encodeMatch_eq_of_G2_nil hsq
        rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode hG2
  | 1 =>
      exact enteredTermsOf_eq_of_encodeMatch_eq_of_length_one hsq
        rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
        (by simpa [hlt])
  | 2 =>
      exact enteredTermsOf_eq_of_encodeMatch_eq_of_length_two_of_exit_eq hsq
        rho₁ rho₂ D hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hw hcode
        (by simpa [hlt])
        (hexit rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode
          (by simpa [hlt]))
  | n + 3 =>
      have : (enteredTermsOf rho₁ D t).length ≤ 2 := hlen₁
      rw [hlt] at this
      exact absurd this (by omega)

/-- **Residual (S2189 Stage C — DEAD after S2190).**  Full
`PacketReplayTermsUnique` on every `encodeMatch` image.  Formally refuted
by `PHPMatchingReplayCounterexample`; retained only as historical packaging
for the S2189 shells.  Active residual is
`EncodeMatchCoherentReplayUniqueResidual` (S2196) /
`EncodeMatchEnteredTermsEqResidual` (S2197).

Empty-G2 injectivity is unconditional (`encodeMatch_eq_of_code_eq_of_G2_nil`).
-/
def EncodeMatchReplayUniqueResidual {p h w t ell : Nat} (hsq : p = h)
    (D : MDNF p h) (hw : ∀ term ∈ D, term.length ≤ w) : Prop :=
  ∀ (rho : MatchingMap p h) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)),
    PacketReplayTermsUnique D (encodeMatch hsq rho D hrho hell ht hw)

/-- Unconditional injectivity on the graded bad-set subtype, assuming the
encode-image replay-uniqueness residual. -/
theorem encodeMatch_subtype_injective_of_residual
    {p h w t ell : Nat} (hsq : p = h) (D : MDNF p h)
    (hw : ∀ term ∈ D, term.length ≤ w)
    (hres : EncodeMatchReplayUniqueResidual (t := t) (ell := ell) (w := w)
      hsq D hw) :
    Function.Injective
      (fun rho : {rho : MatchingMap p h // rho ∈ vbadMatchings D (t - 1) ell} =>
        let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
        let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
          Nat.le_of_pred_lt hmem.2
        encodeMatch hsq rho.1 D hmem.1.1 hmem.1.2 ht hw) :=
  encodeMatch_subtype_injective_of_packetReplayTermsUnique hsq D hw
    (fun rho => by
      let hmem := (mem_vbadMatchings D (t - 1) ell rho.1).mp rho.2
      let ht : t ≤ vmdtDepth (canonicalVMDT D rho.1) :=
        Nat.le_of_pred_lt hmem.2
      simpa [hmem, ht] using hres rho.1 hmem.1.1 hmem.1.2 ht)

end PHPMatchingEncodeInjectivity
end PvNP
