import PvNP.PHPMatchingCodeBound

/-!
# GA-3 Stage 3: the mandatory counterexample-disposal test (S2187)

Fourth formal stage of the GA-3 extension-encode rung (S2187 story): the
memo §3(c) mandatory test, bound to the pin 3.6 convention resolution per
amendment M3 — the test may not evaporate through the convention pin.

On the packet's pinned instance (`divD`: square 3×3, width 1, three terms
all demanding hole 0, base μ = ∅ — the very instance whose pigeon-only
walk/vertex-tree divergence is already kernel-pinned):

* **(i) Anti-collision, in general form** (`divD_at_most_one_block`):
  over **every** answer feed, the canonical vertex trace enters at most
  one block — no path ever enters two hole-0-demanding terms, because a
  second entered term's still-unset satisfying pair would collide with
  the first block's on hole 0, contradicting the proved cross-block
  σ-compatibility. The packet's pinned failure mode is disposed of
  structurally, not instance-by-instance.
* **(ii) The encode of μ = ∅ along the deep path**
  (`disposal_blocks`, `disposal_sigma`, `disposal_encodeExt`,
  `disposal_beta_starData`): with the deep feed (answer hole 1 to the
  pigeon-0 query, then pigeon 1 to the hole-0 query — UF's
  π = {(p₁,h₂),(p₂,h₁)}, s = 2), the trace has exactly one block with
  those two steps, σ = [(p₁,h₁)] with **j = 1 = ⌈s/2⌉** (the s/2-type
  deficit realized: two walked pairs covered the one satisfying pair's
  endpoints), the extension G1 is exactly the single satisfying pair,
  and the block's β-vector ({position 0} on the width-1 term, per the
  L1 convention that marks are σ-positions) star-codes to `[(0, true)]`.
  The answer stream G3 is the feed itself; its `[2ℓ]`-index packaging
  is Stage 4's transport pin (3.0) — recorded, not evaporated.
* **(iii) Recovery of μ, in general form** (`encodeExt_recover_base`):
  for any trace, the base is recovered pointwise from G1 plus the σ-overlay (side information), not pure decode from the encoded tuple alone — σ-free pigeons G1 *is* the base, and on σ-pigeons the base was free.
  Instantiated on the pinned instance (`disposal_decode`).
* **Pin 3.6, the badness off-by-one** (`mem_vbadMatchings_succ_le`):
  the packet's `depth > s` bad-set convention is identified with UF's
  `depth ≥ s + 1` reading; together with the already-pinned
  depth-exactly-2 witness (`div_vertex_depth`) this discharges the M3
  binding — the test runs at the memo's s = 2 with the identification
  stated, not silently absorbed.

Feed-parametric / concrete-path validation and one generic recovery lemma
(G1 + σ side information), not a general encoder from bad matchings and
not pure decode from an encoded tuple alone. No injectivity claim (GA-4),
no cardinality-vs-space bound (GA-5), no probability statement, not a
switching lemma, not Gate A closure, not Frege/PHP, NP/circuit, or
P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeDisposal

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound

/-! ## (iii) in general form: the base is recoverable from G1 and σ -/

/-- **G1-decode**: the encode's base matching is recovered pointwise from
the extension and the σ-overlay — σ-pigeons were free in the base
(freshness), and off σ the extension is the base. -/
theorem encodeExt_recover_base {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h)) (i : Fin p) :
    rho i =
      if (pairsToMatching
          (blockSigmas (blocksOf (vtrace rho D feed))).join) i = none
        then encodeExt rho D feed i else none := by
  unfold encodeExt vtrace
  by_cases hov : (pairsToMatching
      (blockSigmas (blocksOf (vevents (freePigeons rho).card rho [] D
        feed))).join) i = none
  · rw [if_pos hov]
    cases hri : rho i with
    | some b =>
        rw [compose_fixed_left _ _ i b hri]
    | none =>
        rw [compose_free_left _ _ i hri]
        rw [hov]
  · rw [if_neg hov]
    cases hosv : (pairsToMatching
        (blockSigmas (blocksOf (vevents (freePigeons rho).card rho [] D
          feed))).join) i with
    | none => exact absurd hosv hov
    | some b =>
        have hm := pairsToMatching_eq_some _ i b hosv
        have hfr := blockSigmas_join_fresh (freePigeons rho).card rho []
          D feed (i, b) hm
        exact hfr.1

/-! ## Pin 3.6: the badness off-by-one identification -/

/-- The packet's `depth > s` bad-set membership is UF's `depth ≥ s + 1`:
the two conventions differ by exactly this recorded off-by-one. -/
theorem mem_vbadMatchings_succ_le {p h : Nat} (D : MDNF p h)
    (s ell : Nat) (mu : MatchingMap p h) :
    mu ∈ vbadMatchings D s ell ↔
      (IsMatching mu ∧ (freePigeons mu).card = ell) ∧
        s + 1 ≤ vmdtDepth (canonicalVMDT D mu) := by
  rw [mem_vbadMatchings]
  constructor
  · rintro ⟨hh, hd⟩
    exact ⟨hh, hd⟩
  · rintro ⟨hh, hd⟩
    exact ⟨hh, hd⟩

/-! ## (i) in general form: no path enters two hole-0-demanding terms -/

/-- On a legal single-pair term that is neither falsified nor satisfied,
the pair is unresolved — so it is the term's σ′. -/
theorem singleton_sigmaFull {p h : Nat} (B : VBlock p h)
    (e : Fin p × Fin h) (hterm : B.term = [e])
    (hfals : termFalsifiedB B.entry B.term = false)
    (hsat : termSatisfiedB B.entry B.term = false) :
    e ∈ sigmaFull B := by
  rw [mem_sigmaFull]
  constructor
  · rw [hterm]
    exact List.mem_cons_self _ _
  · rw [hterm] at hfals hsat
    unfold termFalsifiedB at hfals
    unfold termSatisfiedB at hsat
    simp only [List.any_cons, List.any_nil, Bool.or_false] at hfals
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hsat
    have htri := pair_status_trichotomy B.entry e
    rw [hfals, hsat] at htri
    simpa using htri

/-- **The disposal, general form**: on the pinned instance, every
canonical trace — over every answer feed — enters at most one block.
Two entered blocks would put two still-unset satisfying pairs on hole 0,
contradicting cross-block σ-compatibility: the collision the packet's
counterexample probes cannot form. -/
theorem divD_at_most_one_block (feed : List (Vertex 3 3)) :
    (blocksOf (vtrace (emptyMatching 3 3) divD feed)).length ≤ 1 := by
  by_contra hgt
  push_neg at hgt
  obtain ⟨B1, tl, hbl⟩ : ∃ B1 tl,
      blocksOf (vtrace (emptyMatching 3 3) divD feed) = B1 :: tl := by
    cases hc : blocksOf (vtrace (emptyMatching 3 3) divD feed) with
    | nil =>
        rw [hc] at hgt
        simp at hgt
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨B2, tl2, htl⟩ : ∃ B2 tl2, tl = B2 :: tl2 := by
    cases hc : tl with
    | nil =>
        rw [hc] at hbl
        rw [hbl] at hgt
        simp at hgt
    | cons a b => exact ⟨a, b, rfl⟩
  · 
          have hcross := blocksOf_sigma_cross
            (freePigeons (emptyMatching 3 3)).card (emptyMatching 3 3) []
            divD feed
          unfold vtrace at hbl
          rw [hbl, htl, List.pairwise_cons] at hcross
          have hrel := hcross.1 B2 (List.mem_cons_self _ _)
          -- each entered term is a single pair demanding hole 0
          have hterm : ∀ B : VBlock 3 3,
              B ∈ blocksOf (vevents
                (freePigeons (emptyMatching 3 3)).card
                (emptyMatching 3 3) [] divD feed) →
              ∃ k : Fin 3, B.term = [(k, (0 : Fin 3))] := by
            intro B hB
            rcases blocksOf_entered_first _ _ [] divD feed
              (isMatching_empty 3 3) B hB with ⟨pre, suf, hD, _⟩
            have hmem : B.term ∈ divD := by
              rw [hD]
              exact List.mem_append_right _ (List.mem_cons_self _ _)
            unfold divD at hmem
            have hd : B.term = [((0 : Fin 3), (0 : Fin 3))] ∨
                B.term = [((1 : Fin 3), (0 : Fin 3))] ∨
                B.term = [((2 : Fin 3), (0 : Fin 3))] := by
              simpa using hmem
            rcases hd with h1 | h2 | h3
            · exact ⟨0, h1⟩
            · exact ⟨1, h2⟩
            · exact ⟨2, h3⟩
          have hB1 : B1 ∈ blocksOf (vevents
              (freePigeons (emptyMatching 3 3)).card (emptyMatching 3 3)
              [] divD feed) := by
            rw [hbl]
            exact List.mem_cons_self _ _
          have hB2 : B2 ∈ blocksOf (vevents
              (freePigeons (emptyMatching 3 3)).card (emptyMatching 3 3)
              [] divD feed) := by
            rw [hbl, htl]
            exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
          rcases hterm B1 hB1 with ⟨k1, ht1⟩
          rcases hterm B2 hB2 with ⟨k2, ht2⟩
          have hs1 := blocksOf_entry_spec _ _ [] divD feed B1 hB1
          have hs2 := blocksOf_entry_spec _ _ [] divD feed B2 hB2
          have he1 : (k1, (0 : Fin 3)) ∈ sigmaFull B1 :=
            singleton_sigmaFull B1 _ ht1 hs1.2.2.1 hs1.2.2.2
          have he2 : (k2, (0 : Fin 3)) ∈ sigmaFull B2 :=
            singleton_sigmaFull B2 _ ht2 hs2.2.2.1 hs2.2.2.2
          have hd := hrel _ he1 _ he2
          exact hd.2 rfl

/-! ## (ii) the concrete deep-path encode -/

/-- The deep feed: answer hole 1 to the pigeon-0 query, then pigeon 1 to
the hole-0 query — UF's π = {(p₁,h₂),(p₂,h₁)}, trimmed at s = 2. -/
def deepFeed : List (Vertex 3 3) :=
  [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3)]

/-- The deep-path trace, computed: one entry, two steps. -/
theorem disposal_trace :
    vtrace (emptyMatching 3 3) divD deepFeed =
      [VEvent.enter [((0 : Fin 3), (0 : Fin 3))] (emptyMatching 3 3),
        VEvent.qstep ⟨Sum.inl 0, ((0 : Fin 3), (1 : Fin 3))⟩,
        VEvent.qstep ⟨Sum.inr 0, ((1 : Fin 3), (0 : Fin 3))⟩] := by
  unfold vtrace deepFeed divD
  rw [div_freePigeons_card]
  rw [vevents_entry_pigeon_live 2 (emptyMatching 3 3)
    [((0 : Fin 3), (0 : Fin 3))]
    [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]]
    (0 : Fin 3) [Sum.inr (0 : Fin 3)] (1 : Fin 3) [Sum.inl (1 : Fin 3)]
    (by decide) (by decide) (by decide) div_termVertices (by decide)]
  rw [vevents_block_hole_live 1
    (compose (emptyMatching 3 3) (singleMatching 0 1)) (0 : Fin 3) []
    ([((0 : Fin 3), (0 : Fin 3))] ::
      [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]])
    (1 : Fin 3) [] (by decide) (by decide)]
  rw [vevents_skip_falsified 1
    (compose (compose (emptyMatching 3 3) (singleMatching 0 1))
      (singleMatching 1 0))
    [((0 : Fin 3), (0 : Fin 3))]
    [[((1 : Fin 3), (0 : Fin 3))], [((2 : Fin 3), (0 : Fin 3))]] []
    (by decide) (by decide)]
  rw [vevents_stop_satisfied 1
    (compose (compose (emptyMatching 3 3) (singleMatching 0 1))
      (singleMatching 1 0))
    [((1 : Fin 3), (0 : Fin 3))] [[((2 : Fin 3), (0 : Fin 3))]] []
    (by decide) (by decide) (by decide)]

/-- One block, the two walked pairs as its steps. -/
theorem disposal_blocks :
    blocksOf (vtrace (emptyMatching 3 3) divD deepFeed) =
      [⟨[((0 : Fin 3), (0 : Fin 3))], emptyMatching 3 3,
        [⟨Sum.inl 0, ((0 : Fin 3), (1 : Fin 3))⟩,
          ⟨Sum.inr 0, ((1 : Fin 3), (0 : Fin 3))⟩]⟩] := by
  rw [disposal_trace, blocksOf_enter,
    show afterSteps
      [VEvent.qstep ⟨Sum.inl 0, ((0 : Fin 3), (1 : Fin 3))⟩,
        VEvent.qstep ⟨Sum.inr 0, ((1 : Fin 3), (0 : Fin 3))⟩] =
      ([] : List (VEvent 3 3)) from rfl,
    blocksOf_nil]
  simp [stepsPrefix]

/-- σ = the one satisfying pair, after the queried-vertex truncation:
j = 1 = ⌈s/2⌉ at s = 2 — the s/2-type deficit realized. -/
theorem disposal_sigma :
    (blockSigmas (blocksOf (vtrace (emptyMatching 3 3) divD
      deepFeed))).join = [((0 : Fin 3), (0 : Fin 3))] := by
  rw [disposal_blocks]
  decide

/-- **G1 on the pinned instance**: the extension is exactly the single
satisfying pair p₁ ↦ h₁. -/
theorem disposal_encodeExt (i : Fin 3) :
    encodeExt (emptyMatching 3 3) divD deepFeed i =
      singleMatching (0 : Fin 3) (0 : Fin 3) i := by
  unfold encodeExt
  unfold vtrace
  rw [show blockSigmas (blocksOf (vevents
      (freePigeons (emptyMatching 3 3)).card (emptyMatching 3 3) [] divD
      deepFeed)) = blockSigmas (blocksOf (vtrace (emptyMatching 3 3)
      divD deepFeed)) from rfl]
  rw [disposal_sigma]
  rw [compose_empty_left]
  rw [show pairsToMatching [((0 : Fin 3), (0 : Fin 3))] =
    compose (singleMatching 0 0) (pairsToMatching []) from rfl]
  rw [show pairsToMatching ([] : List (Fin 3 × Fin 3)) =
    emptyMatching 3 3 from rfl]
  rw [compose_empty_right]

/-- **Decode on the pinned instance**: the base μ = ∅ is recovered. -/
theorem disposal_decode (i : Fin 3) :
    emptyMatching 3 3 i =
      if (pairsToMatching (blockSigmas (blocksOf (vtrace
          (emptyMatching 3 3) divD deepFeed))).join) i = none
        then encodeExt (emptyMatching 3 3) divD deepFeed i else none :=
  encodeExt_recover_base (emptyMatching 3 3) divD deepFeed i

/-- **G2 on the pinned instance**: the block's β-vector — the σ-position
set {0} on the width-1 entered term, per the L1 marks-are-σ-positions
convention — star-codes to one entry: position 0, last of its block. -/
theorem disposal_beta_starData :
    starData ([{0}] : List (Finset (Fin 1))) = [((0 : Fin 1), true)] := by
  unfold starData
  rw [List.map_cons, List.map_nil, Finset.sort_singleton]
  rfl

/-- The M3 companion: the pinned instance's canonical vertex tree has
depth exactly 2 — the deep path is genuinely deep for the s = 2 test
under the `≥ s` reading and depth-exactly-2 witnesses the `> s`
identification at s = 1 (`div_vertex_depth`, restated here as the bad-set
membership at the packet convention). -/
theorem disposal_bad_at_one :
    emptyMatching 3 3 ∈ vbadMatchings divD 1 3 := by
  rw [mem_vbadMatchings]
  refine ⟨⟨isMatching_empty 3 3, div_freePigeons_card⟩, ?_⟩
  rw [div_vertex_depth]
  omega

end PHPMatchingEncodeDisposal
end PvNP
