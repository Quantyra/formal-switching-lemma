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
equal entered-term sequences force equal bases (G1+G2 recovery).  Full
`Function.InjOn encodeMatch` still requires recovering entered terms from
`(G1,G2,G3)` alone — the residual GA-4 core.

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

/-! ## Base decoder interface for the next replay stage -/

/-- Recover a base point from `G1` once replay has reconstructed the sigma
overlay.  Stage B must replace the overlay argument by the output of pure
`(G1,G2,G3)` replay. -/
def decodeBasePoint {p h : Nat} (G1 sigma : MatchingMap p h) (i : Fin p) :
    Option (Fin h) :=
  if sigma i = none then G1 i else none

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
  intro feed code
  simpa [encodeMatch] using decodeBasePoint_encodeExt rho D feed i

/-- **Conditional injectivity shell.** Equal codes and equal sigma-overlay
matchings force equal bases.  Full `InjOn encodeMatch` reduces to proving
that equal codes imply equal sigma overlays (via entered-term replay from
G2/G3) — the residual GA-4 core. -/
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
