import PvNP.PHPMatchingDeterministicEncode
import PvNP.PHPMatchingEncodeDisposal

/-!
# GA-4 Stage A: positional decode scaffolding (S2189)

This module begins the pure replay/decode side of the deterministic matching
encode.  It isolates and proves the first losslessness fact needed by replay:
once the entered terms have been recovered, `G2` recovers, block by block, the
exact finite sets of sigma pairs selected by `blockSigmas`.  The theorem is
then specialized to the `encodeMatch` image.

The remaining GA-4 work is explicit: recover the entered terms (and then the
walked pi segments) from `(G1,G2,G3)` alone.  Until that replay theorem is
available, the decoder below takes the entered-term list as intermediate
replay state; consequently this module does not claim `Function.InjOn` for
`encodeMatch`.

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

end PHPMatchingEncodeInjectivity
end PvNP
