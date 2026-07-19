import PvNP.PHPMatchingVertexTree

/-!
# GA-3 Stage 1a: walk traces, blocks, and the extension-encode surface (S2187)

Second formal stage of the GA-3 extension-encode rung (S2187 story,
Option A of record). The located encode (UF Lemma 6.2 / Beame §5 Lemma 4)
operates on the **path and block structure** of the canonical vertex walk
— data the tree object does not carry — so this stage builds the walk's
**event trace**: a deterministic, choice-free replay of `vwalkAux` against
an explicit answer feed (one partner vertex per query; the feed length
realizes UF's "leftmost path trimmed to `s` pairs" without any
path-selection choice), recording block entries (`enter`: the entered term
and the path matching at entry) and query steps (`qstep`: the query label
and the walked answer pair). On top of the trace:

* `blocksOf` — pure chunking of an event trace into blocks
  (entered term, entry matching, steps).
* `sigmaFull`/`sigmaTrunc` — the block's still-unset satisfying pairs
  (σ′_i: the unresolved pairs of the entered term at entry, dedup'd), and
  the last-block **queried-vertex truncation** (amendment H1: keep exactly
  the σ′-pairs containing a vertex appearing as a *query label* of the
  block; pairs touched only through an answer's far endpoint are NOT
  collected).
* `blockSigmas`/`encodeExt` — σ = full σ′ on every non-final block, the
  truncated σ on the final block; the extension G1 = ρ overlaid with σ.
* Foundational structure lemmas (the seeds of pin 3.1):
  - every walked pair is **fresh** over the trace's base matching (pigeon
    free, hole unused) — `vevents_pairs_fresh`;
  - the walked pairs are **pairwise vertex-disjoint** —
    `vevents_pairs_pairwise` — so every step is a GA-1
    `DisjointExtension` and the walked path is itself a partial matching
    over the base;
  - σ′ is contained in the entered term's unresolved pairs
    (`mem_sigmaFull`), is duplicate-free, and is **pairwise
    vertex-disjoint on legal terms** (`sigmaFull_pairwise`) — the
    in-block half of the σ-compatibility invariant, discharged by the
    GA-2 legality gate.

The cross-block σ-compatibility (vertex-cover disjointness through the
block coverage invariant), the well-definedness `ρσ ∈ M`, the drop range
`⌈s/2⌉ ≤ j ≤ s`, and the block-alignment family (pin 3.2) are the
remaining Stage 1 obligations built on this surface.

Deterministic trace/encode infrastructure only. No injectivity claim
(GA-4), no cardinality bound (Stage 2/GA-5), no probability statement, no
PHP switching lemma, not Gate A closure, not Frege/PHP, NP/circuit, or
P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingExtensionEncode

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree

/-! ## Steps, events, and the trace -/

/-- One walked query: the query label and the answer pair it added to the
path matching (`pquery i` answered `a` gives `⟨inl i, (i, a)⟩`; `hquery b`
answered `q` gives `⟨inr b, (q, b)⟩`). -/
structure VStep (p h : Nat) where
  vertex : Vertex p h
  pair : Fin p × Fin h

/-- A trace event: a block entry (the entered term and the path matching
at entry — UF's boundary node) or a query step. -/
inductive VEvent (p h : Nat) where
  | enter (t : MTerm p h) (entry : MatchingMap p h)
  | qstep (s : VStep p h)

/-- The walk's event trace against an explicit answer feed. The recursion
mirrors `vwalkAux` case-for-case: scan skips and stops emit nothing; a
block entry emits `enter` together with its first query step; in-block
queries emit steps. The feed supplies one partner vertex per query
(`inr a`: the hole answering a pigeon query; `inl q`: the pigeon
answering a hole query); an exhausted, ill-kinded, or dead answer
truncates the trace — so a feed of length `s` realizes the located
design's "path trimmed to `s` pairs" with no path-selection choice. -/
def vevents {p h : Nat} :
    Nat → MatchingMap p h → List (Vertex p h) → MDNF p h →
    List (Vertex p h) → List (VEvent p h)
  | _, _, [], [], _ => []
  | fuel, mu, [], t :: rest, feed =>
      if termMatchingLegalB t = false then vevents fuel mu [] rest feed
      else if termFalsifiedB mu t = true then vevents fuel mu [] rest feed
      else if termSatisfiedB mu t = true then []
      else
        match fuel with
        | 0 => []
        | fuel' + 1 =>
            match termVertices mu t with
            | [] => []
            | .inl i :: vs =>
                match feed with
                | [] => []
                | .inl _ :: _ => []
                | .inr a :: fs =>
                    if holeUsed mu a = true then []
                    else .enter t mu :: .qstep ⟨.inl i, (i, a)⟩ ::
                      vevents fuel' (compose mu (singleMatching i a)) vs
                        (t :: rest) fs
            | .inr b :: vs =>
                match feed with
                | [] => []
                | .inr _ :: _ => []
                | .inl q :: fs =>
                    if (mu q).isSome = true then []
                    else .enter t mu :: .qstep ⟨.inr b, (q, b)⟩ ::
                      vevents fuel' (compose mu (singleMatching q b)) vs
                        (t :: rest) fs
  | fuel, mu, v :: vs, D, feed =>
      if vertexCoveredB mu v = true then vevents fuel mu vs D feed
      else
        match fuel with
        | 0 => []
        | fuel' + 1 =>
            match v with
            | .inl i =>
                match feed with
                | [] => []
                | .inl _ :: _ => []
                | .inr a :: fs =>
                    if holeUsed mu a = true then []
                    else .qstep ⟨.inl i, (i, a)⟩ ::
                      vevents fuel' (compose mu (singleMatching i a)) vs D
                        fs
            | .inr b =>
                match feed with
                | [] => []
                | .inr _ :: _ => []
                | .inl q :: fs =>
                    if (mu q).isSome = true then []
                    else .qstep ⟨.inr b, (q, b)⟩ ::
                      vevents fuel' (compose mu (singleMatching q b)) vs D
                        fs
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

/-- Canonical trace entry: no open block, fuel = free-pigeon count. -/
def vtrace {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (feed : List (Vertex p h)) : List (VEvent p h) :=
  vevents (freePigeons rho).card rho [] D feed

/-! ## Trace equation lemmas (the trace is WF-compiled) -/

theorem vevents_nil {p h : Nat} (fuel : Nat) (mu : MatchingMap p h)
    (feed : List (Vertex p h)) :
    vevents fuel mu [] ([] : MDNF p h) feed = [] := by
  rw [vevents.eq_def]

theorem vevents_skip_illegal {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (feed : List (Vertex p h)) (hbad : termMatchingLegalB t = false) :
    vevents fuel mu [] (t :: rest) feed = vevents fuel mu [] rest feed := by
  rw [vevents.eq_def]
  simp [hbad]

theorem vevents_skip_falsified {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (feed : List (Vertex p h)) (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = true) :
    vevents fuel mu [] (t :: rest) feed = vevents fuel mu [] rest feed := by
  rw [vevents.eq_def]
  simp [hleg, hfals]

theorem vevents_stop_satisfied {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (feed : List (Vertex p h)) (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = true) :
    vevents fuel mu [] (t :: rest) feed = [] := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat]

theorem vevents_entry_zero {p h : Nat} (mu : MatchingMap p h)
    (t : MTerm p h) (rest : MDNF p h) (feed : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false) :
    vevents 0 mu [] (t :: rest) feed = [] := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat]

/-- Block entry with a live pigeon-query answer: `enter` and the first
step are emitted together — every block of a trace is nonempty. -/
theorem vevents_entry_pigeon_live {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h) (i : Fin p)
    (vs : List (Vertex p h)) (a : Fin h) (fs : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inl i :: vs)
    (hha : holeUsed mu a = false) :
    vevents (fuel' + 1) mu [] (t :: rest) (Sum.inr a :: fs) =
      .enter t mu :: .qstep ⟨.inl i, (i, a)⟩ ::
        vevents fuel' (compose mu (singleMatching i a)) vs (t :: rest)
          fs := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat, htv, hha]

theorem vevents_entry_pigeon_dead {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h) (i : Fin p)
    (vs : List (Vertex p h)) (a : Fin h) (fs : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inl i :: vs)
    (hha : holeUsed mu a = true) :
    vevents (fuel' + 1) mu [] (t :: rest) (Sum.inr a :: fs) = [] := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat, htv, hha]

theorem vevents_entry_hole_live {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h) (b : Fin h)
    (vs : List (Vertex p h)) (q : Fin p) (fs : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inr b :: vs)
    (hq : (mu q).isSome = false) :
    vevents (fuel' + 1) mu [] (t :: rest) (Sum.inl q :: fs) =
      .enter t mu :: .qstep ⟨.inr b, (q, b)⟩ ::
        vevents fuel' (compose mu (singleMatching q b)) vs (t :: rest)
          fs := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat, htv, hq]

theorem vevents_block_skip_covered {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (v : Vertex p h) (vs : List (Vertex p h))
    (D : MDNF p h) (feed : List (Vertex p h))
    (hcov : vertexCoveredB mu v = true) :
    vevents fuel mu (v :: vs) D feed = vevents fuel mu vs D feed := by
  rw [vevents.eq_def]
  simp [hcov]

theorem vevents_block_zero {p h : Nat} (mu : MatchingMap p h)
    (v : Vertex p h) (vs : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (hcov : vertexCoveredB mu v = false) :
    vevents 0 mu (v :: vs) D feed = [] := by
  rw [vevents.eq_def]
  simp [hcov]

theorem vevents_block_pigeon_live {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (i : Fin p) (vs : List (Vertex p h))
    (D : MDNF p h) (a : Fin h) (fs : List (Vertex p h))
    (hcov : vertexCoveredB mu (.inl i) = false)
    (hha : holeUsed mu a = false) :
    vevents (fuel' + 1) mu (.inl i :: vs) D (Sum.inr a :: fs) =
      .qstep ⟨.inl i, (i, a)⟩ ::
        vevents fuel' (compose mu (singleMatching i a)) vs D fs := by
  rw [vevents.eq_def]
  simp [hcov, hha]

theorem vevents_block_hole_live {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (b : Fin h) (vs : List (Vertex p h))
    (D : MDNF p h) (q : Fin p) (fs : List (Vertex p h))
    (hcov : vertexCoveredB mu (.inr b) = false)
    (hq : (mu q).isSome = false) :
    vevents (fuel' + 1) mu (.inr b :: vs) D (Sum.inl q :: fs) =
      .qstep ⟨.inr b, (q, b)⟩ ::
        vevents fuel' (compose mu (singleMatching q b)) vs D fs := by
  rw [vevents.eq_def]
  simp [hcov, hq]

/-! Dead-arm equation lemmas: every truncation of the trace, pinned. -/

theorem vevents_entry_novertices {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h)
    (feed : List (Vertex p h)) (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = []) :
    vevents (fuel' + 1) mu [] (t :: rest) feed = [] := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat, htv]

theorem vevents_entry_feed_nil {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h) (i : Fin p)
    (vs : List (Vertex p h)) (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inl i :: vs) :
    vevents (fuel' + 1) mu [] (t :: rest) [] = [] := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat, htv]

theorem vevents_entry_feed_illkind {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (t : MTerm p h) (rest : MDNF p h) (i : Fin p)
    (vs : List (Vertex p h)) (q : Fin p) (fs : List (Vertex p h))
    (hleg : termMatchingLegalB t = true)
    (hfals : termFalsifiedB mu t = false)
    (hsat : termSatisfiedB mu t = false)
    (htv : termVertices mu t = .inl i :: vs) :
    vevents (fuel' + 1) mu [] (t :: rest) (Sum.inl q :: fs) = [] := by
  rw [vevents.eq_def]
  simp [hleg, hfals, hsat, htv]

theorem vevents_block_feed_nil {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (v : Vertex p h) (vs : List (Vertex p h))
    (D : MDNF p h) (hcov : vertexCoveredB mu v = false) :
    vevents (fuel' + 1) mu (v :: vs) D [] = [] := by
  cases v with
  | inl i =>
      rw [vevents.eq_def]
      simp [hcov]
  | inr b =>
      rw [vevents.eq_def]
      simp [hcov]

theorem vevents_block_pigeon_illkind {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (i : Fin p) (vs : List (Vertex p h))
    (D : MDNF p h) (q : Fin p) (fs : List (Vertex p h))
    (hcov : vertexCoveredB mu (.inl i) = false) :
    vevents (fuel' + 1) mu (.inl i :: vs) D (Sum.inl q :: fs) = [] := by
  rw [vevents.eq_def]
  simp [hcov]

theorem vevents_block_pigeon_dead {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (i : Fin p) (vs : List (Vertex p h))
    (D : MDNF p h) (a : Fin h) (fs : List (Vertex p h))
    (hcov : vertexCoveredB mu (.inl i) = false)
    (hha : holeUsed mu a = true) :
    vevents (fuel' + 1) mu (.inl i :: vs) D (Sum.inr a :: fs) = [] := by
  rw [vevents.eq_def]
  simp [hcov, hha]

theorem vevents_block_hole_illkind {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (b : Fin h) (vs : List (Vertex p h))
    (D : MDNF p h) (a : Fin h) (fs : List (Vertex p h))
    (hcov : vertexCoveredB mu (.inr b) = false) :
    vevents (fuel' + 1) mu (.inr b :: vs) D (Sum.inr a :: fs) = [] := by
  rw [vevents.eq_def]
  simp [hcov]

theorem vevents_block_hole_dead {p h : Nat} (fuel' : Nat)
    (mu : MatchingMap p h) (b : Fin h) (vs : List (Vertex p h))
    (D : MDNF p h) (q : Fin p) (fs : List (Vertex p h))
    (hcov : vertexCoveredB mu (.inr b) = false)
    (hq : (mu q).isSome = true) :
    vevents (fuel' + 1) mu (.inr b :: vs) D (Sum.inl q :: fs) = [] := by
  rw [vevents.eq_def]
  simp [hcov, hq]

/-! ## Walked pairs -/

/-- The walked pairs of a trace, in walk order — the path matching π as a
pair list. -/
def eventsPairs {p h : Nat} : List (VEvent p h) → List (Fin p × Fin h)
  | [] => []
  | .enter _ _ :: es => eventsPairs es
  | .qstep s :: es => s.pair :: eventsPairs es

theorem eventsPairs_nil {p h : Nat} :
    eventsPairs ([] : List (VEvent p h)) = [] := rfl

theorem eventsPairs_enter {p h : Nat} (t : MTerm p h)
    (ent : MatchingMap p h) (es : List (VEvent p h)) :
    eventsPairs (.enter t ent :: es) = eventsPairs es := rfl

theorem eventsPairs_qstep {p h : Nat} (s : VStep p h)
    (es : List (VEvent p h)) :
    eventsPairs (.qstep s :: es) = s.pair :: eventsPairs es := rfl

/-! ## Freshness and disjointness of the walked path (pin 3.1 seeds) -/

/-- Two pairs are vertex-disjoint: distinct pigeons and distinct holes. -/
def PairDisjoint {p h : Nat} (e f : Fin p × Fin h) : Prop :=
  e.1 ≠ f.1 ∧ e.2 ≠ f.2

/-- Composition with a single pair frees no pigeon: a pigeon free in the
composite was free before. -/
theorem free_of_compose_free {p h : Nat} (mu m1 : MatchingMap p h)
    (j : Fin p) (hj : compose mu m1 j = none) : mu j = none := by
  cases hmj : mu j with
  | none => rfl
  | some c =>
      rw [compose_fixed_left mu m1 j c hmj] at hj
      cases hj

/-- Composition uses no fewer holes: a hole unused in the composite was
unused before. -/
theorem holeUnused_of_compose_unused {p h : Nat} (mu m1 : MatchingMap p h)
    (b : Fin h) (hb : holeUsed (compose mu m1) b = false) :
    holeUsed mu b = false := by
  cases hub : holeUsed mu b with
  | false => rfl
  | true =>
      exfalso
      rcases (holeUsed_eq_true_iff mu b).mp hub with ⟨j, hj⟩
      have : holeUsed (compose mu m1) b = true :=
        (holeUsed_eq_true_iff (compose mu m1) b).mpr
          ⟨j, compose_fixed_left mu m1 j b hj⟩
      rw [hb] at this
      cases this

/-- The queried pigeon is matched in the extended composite. -/
theorem compose_single_self {p h : Nat} (mu : MatchingMap p h) (i : Fin p)
    (a : Fin h) (hfree : mu i = none) :
    compose mu (singleMatching i a) i = some a := by
  rw [compose_free_left mu (singleMatching i a) i hfree]
  exact singleMatching_self i a

/-- The answered hole is used in the extended composite. -/
theorem holeUsed_compose_single {p h : Nat} (mu : MatchingMap p h)
    (i : Fin p) (a : Fin h) (hfree : mu i = none) :
    holeUsed (compose mu (singleMatching i a)) a = true :=
  (holeUsed_eq_true_iff _ a).mpr ⟨i, compose_single_self mu i a hfree⟩

/-- **Path freshness** (pin 3.1 seed): every walked pair of a trace is
fresh over the trace's base matching — its pigeon is free and its hole
unused. In particular every step composes a GA-1 `DisjointExtension`
along the actual walked path. -/
theorem vevents_pairs_fresh {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)),
      ∀ e ∈ eventsPairs (vevents fuel mu pending D feed),
        mu e.1 = none ∧ holeUsed mu e.2 = false
  | _, _, [], [], feed => by
      rw [vevents_nil]
      intro e he
      cases he
  | fuel, mu, [], t :: rest, feed => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals]
          exact vevents_pairs_fresh fuel mu [] rest feed
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals'
              hsat]
            intro e he
            cases he
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat']
                intro e he
                cases he
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hleg, hfals', hsat', htv]
                    intro e he
                    simp [eventsPairs] at he
                | cons v vs =>
                    cases v with
                    | inl i =>
                        have hfree : mu i = none :=
                          termVertices_head_pigeon_free mu t i vs htv
                        cases feed with
                        | nil =>
                            rw [vevents.eq_def]
                            simp only [hleg, hfals', hsat', htv]
                            intro e he
                            simp [eventsPairs] at he
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents.eq_def]
                                simp only [hleg, hfals', hsat', htv]
                                intro e he
                                simp [eventsPairs] at he
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha]
                                  intro e he
                                  cases he
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha']
                                  rw [eventsPairs_enter, eventsPairs_qstep]
                                  intro e he
                                  cases he with
                                  | head =>
                                      exact ⟨hfree, hha'⟩
                                  | tail _ hte =>
                                      have hrec := vevents_pairs_fresh
                                        fuel'
                                        (compose mu (singleMatching i a))
                                        vs (t :: rest) fs e hte
                                      exact ⟨free_of_compose_free mu _ e.1
                                          hrec.1,
                                        holeUnused_of_compose_unused mu _
                                          e.2 hrec.2⟩
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg']
        exact vevents_pairs_fresh fuel mu [] rest feed
  | fuel, mu, v :: vs, D, feed => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov]
        exact vevents_pairs_fresh fuel mu vs D feed
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov']
            intro e he
            cases he
        | succ fuel' =>
            cases v with
            | inl i =>
                have hfree : mu i = none := by
                  simp only [vertexCoveredB] at hcov'
                  cases hmi : mu i with
                  | none => rfl
                  | some c =>
                      rw [hmi] at hcov'
                      simp at hcov'
                cases feed with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hcov']
                    intro e he
                    simp [eventsPairs] at he
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents.eq_def]
                        simp only [hcov']
                        intro e he
                        simp [eventsPairs] at he
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents.eq_def]
                          simp only [hcov', hha]
                          intro e he
                          simp [eventsPairs] at he
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a
                            fs hcov' hha']
                          rw [eventsPairs_qstep]
                          intro e he
                          cases he with
                          | head => exact ⟨hfree, hha'⟩
                          | tail _ hte =>
                              have hrec := vevents_pairs_fresh fuel'
                                (compose mu (singleMatching i a)) vs D fs
                                e hte
                              exact ⟨free_of_compose_free mu _ e.1 hrec.1,
                                holeUnused_of_compose_unused mu _ e.2
                                  hrec.2⟩
            | inr b =>
                have hbfree : holeUsed mu b = false := by
                  simpa only [vertexCoveredB] using hcov'
                cases feed with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hcov']
                    intro e he
                    simp [eventsPairs] at he
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents.eq_def]
                        simp only [hcov']
                        intro e he
                        simp [eventsPairs] at he
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents.eq_def]
                          simp only [hcov', hq]
                          intro e he
                          simp [eventsPairs] at he
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          have hfreeq : mu q = none := by
                            cases hmq : mu q with
                            | none => rfl
                            | some c =>
                                rw [hmq] at hq'
                                simp at hq'
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq']
                          rw [eventsPairs_qstep]
                          intro e he
                          cases he with
                          | head => exact ⟨hfreeq, hbfree⟩
                          | tail _ hte =>
                              have hrec := vevents_pairs_fresh fuel'
                                (compose mu (singleMatching q b)) vs D fs
                                e hte
                              exact ⟨free_of_compose_free mu _ e.1 hrec.1,
                                holeUnused_of_compose_unused mu _ e.2
                                  hrec.2⟩
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

/-- Head-versus-tail disjointness at a live query step: pairs fresh over
the extended composite are vertex-disjoint from the pair just walked. -/
theorem pairDisjoint_of_fresh_over_extension {p h : Nat}
    (mu : MatchingMap p h) (i : Fin p) (a : Fin h) (hfree : mu i = none)
    (e : Fin p × Fin h)
    (hef : compose mu (singleMatching i a) e.1 = none)
    (heh : holeUsed (compose mu (singleMatching i a)) e.2 = false) :
    PairDisjoint (i, a) e := by
  constructor
  · intro hie
    rw [← hie] at hef
    rw [compose_single_self mu i a hfree] at hef
    cases hef
  · intro hae
    rw [← hae] at heh
    rw [holeUsed_compose_single mu i a hfree] at heh
    cases heh

/-- **Path disjointness** (pin 3.1 seed): the walked pairs of a trace are
pairwise vertex-disjoint — the walked path is a partial matching in its
own right, disjoint from the base. -/
theorem vevents_pairs_pairwise {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)),
      List.Pairwise PairDisjoint (eventsPairs (vevents fuel mu pending D
        feed))
  | _, _, [], [], feed => by
      rw [vevents_nil]
      exact List.Pairwise.nil
  | fuel, mu, [], t :: rest, feed => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals]
          exact vevents_pairs_pairwise fuel mu [] rest feed
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals'
              hsat]
            exact List.Pairwise.nil
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat']
                exact List.Pairwise.nil
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hleg, hfals', hsat', htv]
                    exact List.Pairwise.nil
                | cons v vs =>
                    cases v with
                    | inl i =>
                        have hfree : mu i = none :=
                          termVertices_head_pigeon_free mu t i vs htv
                        cases feed with
                        | nil =>
                            rw [vevents.eq_def]
                            simp only [hleg, hfals', hsat', htv]
                            exact List.Pairwise.nil
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents.eq_def]
                                simp only [hleg, hfals', hsat', htv]
                                exact List.Pairwise.nil
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha]
                                  exact List.Pairwise.nil
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha']
                                  rw [eventsPairs_enter, eventsPairs_qstep]
                                  rw [List.pairwise_cons]
                                  constructor
                                  · intro e he
                                    have hef := vevents_pairs_fresh fuel'
                                      (compose mu (singleMatching i a)) vs
                                      (t :: rest) fs e he
                                    exact pairDisjoint_of_fresh_over_extension
                                      mu i a hfree e hef.1 hef.2
                                  · exact vevents_pairs_pairwise fuel'
                                      (compose mu (singleMatching i a)) vs
                                      (t :: rest) fs
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg']
        exact vevents_pairs_pairwise fuel mu [] rest feed
  | fuel, mu, v :: vs, D, feed => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov]
        exact vevents_pairs_pairwise fuel mu vs D feed
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov']
            exact List.Pairwise.nil
        | succ fuel' =>
            cases v with
            | inl i =>
                have hfree : mu i = none := by
                  simp only [vertexCoveredB] at hcov'
                  cases hmi : mu i with
                  | none => rfl
                  | some c =>
                      rw [hmi] at hcov'
                      simp at hcov'
                cases feed with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hcov']
                    exact List.Pairwise.nil
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents.eq_def]
                        simp only [hcov']
                        exact List.Pairwise.nil
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents.eq_def]
                          simp only [hcov', hha]
                          exact List.Pairwise.nil
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a
                            fs hcov' hha']
                          rw [eventsPairs_qstep, List.pairwise_cons]
                          constructor
                          · intro e he
                            have hef := vevents_pairs_fresh fuel'
                              (compose mu (singleMatching i a)) vs D fs e
                              he
                            exact pairDisjoint_of_fresh_over_extension mu
                              i a hfree e hef.1 hef.2
                          · exact vevents_pairs_pairwise fuel'
                              (compose mu (singleMatching i a)) vs D fs
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hcov']
                    exact List.Pairwise.nil
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents.eq_def]
                        simp only [hcov']
                        exact List.Pairwise.nil
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents.eq_def]
                          simp only [hcov', hq]
                          exact List.Pairwise.nil
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          have hfreeq : mu q = none := by
                            cases hmq : mu q with
                            | none => rfl
                            | some c =>
                                rw [hmq] at hq'
                                simp at hq'
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq']
                          rw [eventsPairs_qstep, List.pairwise_cons]
                          constructor
                          · intro e he
                            have hef := vevents_pairs_fresh fuel'
                              (compose mu (singleMatching q b)) vs D fs e
                              he
                            exact pairDisjoint_of_fresh_over_extension mu
                              q b hfreeq e hef.1 hef.2
                          · exact vevents_pairs_pairwise fuel'
                              (compose mu (singleMatching q b)) vs D fs
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

/-! ## Blocks and their σ-data -/

/-- A walk block: the entered term, the path matching at entry (UF's
boundary node), and the block's query steps in walk order. -/
structure VBlock (p h : Nat) where
  term : MTerm p h
  entry : MatchingMap p h
  steps : List (VStep p h)

/-- Leading query steps of an event list (the open block's steps). -/
def stepsPrefix {p h : Nat} : List (VEvent p h) → List (VStep p h)
  | .qstep s :: es => s :: stepsPrefix es
  | _ => []

/-- Drop the leading query steps (to the next block boundary). -/
def afterSteps {p h : Nat} : List (VEvent p h) → List (VEvent p h)
  | .qstep _ :: es => afterSteps es
  | es => es

theorem afterSteps_length_le {p h : Nat} :
    ∀ es : List (VEvent p h), (afterSteps es).length ≤ es.length
  | [] => Nat.le_refl _
  | .enter _ _ :: _ => Nat.le_refl _
  | .qstep _ :: es =>
      Nat.le_trans (afterSteps_length_le es) (Nat.le_succ _)

/-- Chunk an event trace into blocks: each `enter` opens a block that
collects the following steps. (Traces emit `enter` only together with a
first step, so canonical blocks are nonempty; orphan leading steps of
non-canonical event lists are discarded.) -/
def blocksOf {p h : Nat} : List (VEvent p h) → List (VBlock p h)
  | [] => []
  | .qstep _ :: es => blocksOf es
  | .enter t ent :: es =>
      ⟨t, ent, stepsPrefix es⟩ :: blocksOf (afterSteps es)
  termination_by es => es.length
  decreasing_by
    all_goals
      first
        | (simp_wf; omega)
        | (simp_wf
           have := afterSteps_length_le (p := p) (h := h) es
           omega)
        | simp_wf

theorem blocksOf_nil {p h : Nat} :
    blocksOf ([] : List (VEvent p h)) = [] := by
  rw [blocksOf.eq_def]

theorem blocksOf_qstep {p h : Nat} (st : VStep p h)
    (es : List (VEvent p h)) :
    blocksOf (.qstep st :: es) = blocksOf es := by
  rw [blocksOf.eq_def]

theorem blocksOf_enter {p h : Nat} (t : MTerm p h)
    (ent : MatchingMap p h) (es : List (VEvent p h)) :
    blocksOf (.enter t ent :: es) =
      ⟨t, ent, stepsPrefix es⟩ :: blocksOf (afterSteps es) := by
  rw [blocksOf.eq_def]

/-- σ′ of a block: the still-unset satisfying pairs of the entered term
at entry — the unique minimal matching satisfying the entered restricted
term (duplicate pair copies removed; they are semantically inert under
the dedup-tolerant legality gate). -/
def sigmaFull {p h : Nat} (B : VBlock p h) : List (Fin p × Fin h) :=
  (B.term.filter (pairUnresolvedB B.entry)).dedup

/-- The block's query labels. -/
def blockQueried {p h : Nat} (B : VBlock p h) : List (Vertex p h) :=
  B.steps.map VStep.vertex

/-- The queried-vertex collection rule (amendment H1): a pair is
collected iff one of its endpoints appears as a **query label** — pairs
touched only through an answer's far endpoint are not collected. -/
def pairQueriedB {p h : Nat} (qs : List (Vertex p h))
    (e : Fin p × Fin h) : Bool :=
  qs.contains (Sum.inl e.1) || qs.contains (Sum.inr e.2)

/-- σ of a truncated block: σ′ cut down by the queried-vertex rule. -/
def sigmaTrunc {p h : Nat} (B : VBlock p h) : List (Fin p × Fin h) :=
  (sigmaFull B).filter (pairQueriedB (blockQueried B))

/-- The σ-blocks of the encode: full σ′ on every non-final block, the
queried-vertex truncation on the final block (UF Lemma 6.2's last-block
rule, uniformly applied to the trace's final block — the feed length
realizes the path trim, so the final block is the trimmed one). -/
def blockSigmas {p h : Nat} : List (VBlock p h) →
    List (List (Fin p × Fin h))
  | [] => []
  | [B] => [sigmaTrunc B]
  | B :: Bs => sigmaFull B :: blockSigmas Bs

/-- Overlay a pair list as a first-wins matching map. -/
def pairsToMatching {p h : Nat} : List (Fin p × Fin h) → MatchingMap p h
  | [] => emptyMatching p h
  | e :: es => compose (singleMatching e.1 e.2) (pairsToMatching es)

/-- **The extension encode's G1 component**: the base matching overlaid
with the satisfying pairs σ = σ_1 ∪ ... ∪ σ_k of the trace's blocks
(final block truncated by the queried-vertex rule). The walked pairs
never sit in the extension — the classical anti-misidentification
design. -/
def encodeExt {p h : Nat} (rho : MatchingMap p h) (D : MDNF p h)
    (feed : List (Vertex p h)) : MatchingMap p h :=
  compose rho
    (pairsToMatching (blockSigmas (blocksOf (vtrace rho D feed))).join)

/-! ## σ structural lemmas (pin 3.1 seeds) -/

theorem mem_sigmaFull {p h : Nat} (B : VBlock p h) (e : Fin p × Fin h) :
    e ∈ sigmaFull B ↔
      e ∈ B.term ∧ pairUnresolvedB B.entry e = true := by
  unfold sigmaFull
  rw [List.mem_dedup, List.mem_filter]

theorem sigmaFull_nodup {p h : Nat} (B : VBlock p h) :
    (sigmaFull B).Nodup :=
  List.nodup_dedup _

theorem mem_sigmaTrunc {p h : Nat} (B : VBlock p h) (e : Fin p × Fin h) :
    e ∈ sigmaTrunc B ↔
      e ∈ sigmaFull B ∧ pairQueriedB (blockQueried B) e = true := by
  unfold sigmaTrunc
  rw [List.mem_filter]

theorem sigmaTrunc_subset_sigmaFull {p h : Nat} (B : VBlock p h) :
    ∀ e ∈ sigmaTrunc B, e ∈ sigmaFull B := by
  intro e he
  exact ((mem_sigmaTrunc B e).mp he).1

/-- Duplicate images on a duplicate-free list force `hasDupB` — the
converse of GA-2's `exists_distinct_of_hasDupB_map`. -/
theorem hasDupB_map_of_mem_eq {alpha beta : Type} [BEq beta]
    [LawfulBEq beta] (f : alpha → beta) :
    ∀ (l : List alpha) (x y : alpha), x ∈ l → y ∈ l → x ≠ y →
      f x = f y → hasDupB (l.map f) = true
  | [], _, _, hx, _, _, _ => by cases hx
  | z :: zs, x, y, hx, hy, hxy, hf => by
      unfold hasDupB
      rw [List.map_cons, Bool.or_eq_true]
      cases hx with
      | head =>
          cases hy with
          | head => exact absurd rfl hxy
          | tail _ hy' =>
              left
              have hm : f y ∈ zs.map f := List.mem_map.mpr ⟨y, hy', rfl⟩
              rw [← hf] at hm
              simpa using hm
      | tail _ hx' =>
          cases hy with
          | head =>
              left
              have hm : f x ∈ zs.map f := List.mem_map.mpr ⟨x, hx', rfl⟩
              rw [hf] at hm
              simpa using hm
          | tail _ hy' =>
              right
              exact hasDupB_map_of_mem_eq f zs x y hx' hy' hxy hf

/-- **σ-internal disjointness** (pin 3.1 seed): on a legal entered term,
the still-unset satisfying pairs are pairwise vertex-disjoint — the GA-2
self-collision gate is exactly what makes each σ_i a partial matching. -/
theorem sigmaFull_pairwise {p h : Nat} (B : VBlock p h)
    (hleg : termMatchingLegalB B.term = true) :
    List.Pairwise PairDisjoint (sigmaFull B) := by
  have hnd : (sigmaFull B).Nodup := sigmaFull_nodup B
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro x y hx hy hxy
  unfold termMatchingLegalB at hleg
  rw [Bool.and_eq_true] at hleg
  have hxt : x ∈ B.term.dedup :=
    List.mem_dedup.mpr ((mem_sigmaFull B x).mp hx).1
  have hyt : y ∈ B.term.dedup :=
    List.mem_dedup.mpr ((mem_sigmaFull B y).mp hy).1
  constructor
  · intro hfst
    have hdup : hasDupB (B.term.dedup.map Prod.fst) = true :=
      hasDupB_map_of_mem_eq Prod.fst B.term.dedup x y hxt hyt hxy hfst
    have hno := hleg.1
    rw [hdup] at hno
    simp at hno
  · intro hsnd
    have hdup : hasDupB (B.term.dedup.map Prod.snd) = true :=
      hasDupB_map_of_mem_eq Prod.snd B.term.dedup x y hxt hyt hxy hsnd
    have hno := hleg.2
    rw [hdup] at hno
    simp at hno

/-! ## Stage 1b: trace invariants (entry spec, block membership, σ freshness) -/

/-- `afterSteps` is a suffix: its members are members. -/
theorem mem_of_mem_afterSteps {p h : Nat} :
    ∀ (es : List (VEvent p h)) (e : VEvent p h),
      e ∈ afterSteps es → e ∈ es
  | [], _, hm => hm
  | .enter _ _ :: _, _, hm => hm
  | .qstep _ :: es, e, hm =>
      List.mem_cons_of_mem _ (mem_of_mem_afterSteps es e hm)

/-- Chunking ignores leading steps, so it commutes with dropping them. -/
theorem blocksOf_afterSteps {p h : Nat} :
    ∀ es : List (VEvent p h), blocksOf (afterSteps es) = blocksOf es
  | [] => rfl
  | .enter _ _ :: _ => rfl
  | .qstep st :: es => by
      show blocksOf (afterSteps es) = blocksOf (.qstep st :: es)
      rw [blocksOf_qstep]
      exact blocksOf_afterSteps es

/-- Every chunked block's boundary node is an `enter` event of the
underlying event list. -/
theorem enter_mem_of_mem_blocksOf {p h : Nat} :
    ∀ (es : List (VEvent p h)) (B : VBlock p h), B ∈ blocksOf es →
      VEvent.enter B.term B.entry ∈ es
  | [], B, hm => by
      rw [blocksOf_nil] at hm
      cases hm
  | .qstep st :: es, B, hm => by
      rw [blocksOf_qstep] at hm
      exact List.mem_cons_of_mem _ (enter_mem_of_mem_blocksOf es B hm)
  | .enter t ent :: es, B, hm => by
      rw [blocksOf_enter] at hm
      cases hm with
      | head => exact List.mem_cons_self _ _
      | tail _ hm' =>
          have hrec := enter_mem_of_mem_blocksOf (afterSteps es) B hm'
          exact List.mem_cons_of_mem _ (mem_of_mem_afterSteps es _ hrec)
  termination_by es _ => es.length
  decreasing_by
    all_goals
      first
        | (simp_wf; omega)
        | (simp_wf
           have := afterSteps_length_le (p := p) (h := h) es
           omega)
        | simp_wf

/-- Hole usage is monotone under `MAgree`. -/
theorem holeUsed_mono_mAgree {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) (b : Fin h) (hb : holeUsed mu b = true) :
    holeUsed nu b = true := by
  rcases (holeUsed_eq_true_iff mu b).mp hb with ⟨j, hj⟩
  exact (holeUsed_eq_true_iff nu b).mpr ⟨j, hag j b hj⟩

/-- Pigeon freeness pulls back along `MAgree`. -/
theorem free_of_mAgree_free {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) (i : Fin p) (hi : nu i = none) : mu i = none := by
  cases hmi : mu i with
  | none => rfl
  | some c =>
      have := hag i c hmi
      rw [hi] at this
      cases this

/-- Hole non-usage pulls back along `MAgree`. -/
theorem holeUnused_of_mAgree_unused {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) (b : Fin h) (hb : holeUsed nu b = false) :
    holeUsed mu b = false := by
  cases hub : holeUsed mu b with
  | false => rfl
  | true =>
      have := holeUsed_mono_mAgree hag b hub
      rw [hb] at this
      cases this

/-- **Entry specification** (one induction, all boundary-node facts):
every `enter` event of a trace records an entry matching extending the
trace's base, and its entered term passed the walk's gates — legal,
not falsified, and not satisfied at entry. -/
theorem vevents_enter_spec {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)) (t' : MTerm p h)
      (ent' : MatchingMap p h),
      VEvent.enter t' ent' ∈ vevents fuel mu pending D feed →
      MAgree mu ent' ∧ termMatchingLegalB t' = true ∧
        termFalsifiedB ent' t' = false ∧ termSatisfiedB ent' t' = false
  | _, _, [], [], feed, t', ent', hm => by
      rw [vevents_nil] at hm
      cases hm
  | fuel, mu, [], t :: rest, feed, t', ent', hm => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals] at hm
          exact vevents_enter_spec fuel mu [] rest feed t' ent' hm
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals'
              hsat] at hm
            cases hm
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat']
                  at hm
                cases hm
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents.eq_def] at hm
                    simp only [hleg, hfals', hsat', htv] at hm
                    simp at hm
                | cons v vs =>
                    cases v with
                    | inl i =>
                        cases feed with
                        | nil =>
                            rw [vevents.eq_def] at hm
                            simp only [hleg, hfals', hsat', htv] at hm
                            simp at hm
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents.eq_def] at hm
                                simp only [hleg, hfals', hsat', htv] at hm
                                simp at hm
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha] at hm
                                  cases hm
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha'] at hm
                                  cases hm with
                                  | head =>
                                      exact ⟨mAgree_refl mu, hleg, hfals',
                                        hsat'⟩
                                  | tail _ hm' =>
                                      cases hm' with
                                      | tail _ hm'' =>
                                          have hrec := vevents_enter_spec
                                            fuel'
                                            (compose mu
                                              (singleMatching i a)) vs
                                            (t :: rest) fs t' ent' hm''
                                          exact ⟨mAgree_trans
                                            (mAgree_compose_left mu _)
                                            hrec.1, hrec.2⟩
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg'] at hm
        exact vevents_enter_spec fuel mu [] rest feed t' ent' hm
  | fuel, mu, v :: vs, D, feed, t', ent', hm => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov] at hm
        exact vevents_enter_spec fuel mu vs D feed t' ent' hm
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov'] at hm
            cases hm
        | succ fuel' =>
            cases v with
            | inl i =>
                cases feed with
                | nil =>
                    rw [vevents.eq_def] at hm
                    simp only [hcov'] at hm
                    simp at hm
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents.eq_def] at hm
                        simp only [hcov'] at hm
                        simp at hm
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents.eq_def] at hm
                          simp only [hcov', hha] at hm
                          simp at hm
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a
                            fs hcov' hha'] at hm
                          cases hm with
                          | tail _ hm' =>
                              have hrec := vevents_enter_spec fuel'
                                (compose mu (singleMatching i a)) vs D fs
                                t' ent' hm'
                              exact ⟨mAgree_trans
                                (mAgree_compose_left mu _) hrec.1,
                                hrec.2⟩
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents.eq_def] at hm
                    simp only [hcov'] at hm
                    simp at hm
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents.eq_def] at hm
                        simp only [hcov'] at hm
                        simp at hm
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents.eq_def] at hm
                          simp only [hcov', hq] at hm
                          simp at hm
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq'] at hm
                          cases hm with
                          | tail _ hm' =>
                              have hrec := vevents_enter_spec fuel'
                                (compose mu (singleMatching q b)) vs D fs
                                t' ent' hm'
                              exact ⟨mAgree_trans
                                (mAgree_compose_left mu _) hrec.1,
                                hrec.2⟩
  termination_by fuel _ pending D _ _ _ _ =>
    (fuel, pending.length + D.length)

/-- **Block entry specification**: every block of a trace has an entry
matching extending the base and an entered term that passed the walk's
gates. -/
theorem blocksOf_entry_spec {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (B : VBlock p h)
    (hB : B ∈ blocksOf (vevents fuel mu pending D feed)) :
    MAgree mu B.entry ∧ termMatchingLegalB B.term = true ∧
      termFalsifiedB B.entry B.term = false ∧
      termSatisfiedB B.entry B.term = false :=
  vevents_enter_spec fuel mu pending D feed B.term B.entry
    (enter_mem_of_mem_blocksOf _ B hB)

/-- **σ freshness over the base** (pin 3.1 seed): every still-unset
satisfying pair of every block is fresh over the trace's base matching —
σ never collides with ρ. -/
theorem sigmaFull_fresh_over_base {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (B : VBlock p h)
    (hB : B ∈ blocksOf (vevents fuel mu pending D feed))
    (e : Fin p × Fin h) (he : e ∈ sigmaFull B) :
    mu e.1 = none ∧ holeUsed mu e.2 = false := by
  have hspec := blocksOf_entry_spec fuel mu pending D feed B hB
  have hunres := ((mem_sigmaFull B e).mp he).2
  unfold pairUnresolvedB at hunres
  rw [Bool.and_eq_true] at hunres
  have hfree : B.entry e.1 = none := by
    have hb := hunres.1
    simpa using hb
  have hhole : holeUsed B.entry e.2 = false := by
    have hb := hunres.2
    simpa using hb
  exact ⟨free_of_mAgree_free hspec.1 e.1 hfree,
    holeUnused_of_mAgree_unused hspec.1 e.2 hhole⟩

/-! ## Stage 1b.2: pending coverage and cross-block σ-compatibility -/

/-- Vertex coverage is monotone under `MAgree`. -/
theorem vertexCoveredB_mono_mAgree {p h : Nat} {mu nu : MatchingMap p h}
    (hag : MAgree mu nu) (v : Vertex p h)
    (hv : vertexCoveredB mu v = true) : vertexCoveredB nu v = true := by
  cases v with
  | inl i =>
      simp only [vertexCoveredB] at hv ⊢
      cases hmi : mu i with
      | none =>
          rw [hmi] at hv
          simp at hv
      | some c =>
          rw [hag i c hmi]
          rfl
  | inr b =>
      simp only [vertexCoveredB] at hv ⊢
      exact holeUsed_mono_mAgree hag b hv

/-- **Pending coverage**: every vertex still pending in an open block is
covered by the entry matching of every later block of the trace — the
walk drains its frozen list (query or covered-skip) before it ever opens
another block. -/
theorem vevents_pending_covered {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)) (v : Vertex p h),
      v ∈ pending →
      ∀ B ∈ blocksOf (vevents fuel mu pending D feed),
        vertexCoveredB B.entry v = true
  | _, _, [], [], _, v, hv => by cases hv
  | _, _, [], _ :: _, _, v, hv => by cases hv
  | fuel, mu, v' :: vs, D, feed, v, hv => by
      by_cases hcov : vertexCoveredB mu v' = true
      · rw [vevents_block_skip_covered fuel mu v' vs D feed hcov]
        cases hv with
        | head =>
            intro B hB
            exact vertexCoveredB_mono_mAgree
              (blocksOf_entry_spec fuel mu vs D feed B hB).1 v' hcov
        | tail _ hv' =>
            exact vevents_pending_covered fuel mu vs D feed v hv'
      · have hcov' : vertexCoveredB mu v' = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v' vs D feed hcov']
            intro B hB
            rw [blocksOf_nil] at hB
            cases hB
        | succ fuel' =>
            cases v' with
            | inl i =>
                have hfree : mu i = none := by
                  simp only [vertexCoveredB] at hcov'
                  cases hmi : mu i with
                  | none => rfl
                  | some c =>
                      rw [hmi] at hcov'
                      simp at hcov'
                cases feed with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hcov']
                    intro B hB
                    simp [blocksOf_nil] at hB
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents.eq_def]
                        simp only [hcov']
                        intro B hB
                        simp [blocksOf_nil] at hB
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents.eq_def]
                          simp only [hcov', hha]
                          intro B hB
                          simp [blocksOf_nil] at hB
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a
                            fs hcov' hha']
                          intro B hB
                          rw [blocksOf_qstep] at hB
                          cases hv with
                          | head =>
                              have hcv : vertexCoveredB
                                  (compose mu (singleMatching i a))
                                  (Sum.inl i) = true := by
                                simp only [vertexCoveredB]
                                rw [compose_single_self mu i a hfree]
                                rfl
                              exact vertexCoveredB_mono_mAgree
                                (blocksOf_entry_spec fuel' _ vs D fs B
                                  hB).1 _ hcv
                          | tail _ hv' =>
                              exact vevents_pending_covered fuel'
                                (compose mu (singleMatching i a)) vs D fs
                                v hv' B hB
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents.eq_def]
                    simp only [hcov']
                    intro B hB
                    simp [blocksOf_nil] at hB
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents.eq_def]
                        simp only [hcov']
                        intro B hB
                        simp [blocksOf_nil] at hB
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents.eq_def]
                          simp only [hcov', hq]
                          intro B hB
                          simp [blocksOf_nil] at hB
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          have hfreeq : mu q = none := by
                            cases hmq : mu q with
                            | none => rfl
                            | some c =>
                                rw [hmq] at hq'
                                simp at hq'
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq']
                          intro B hB
                          rw [blocksOf_qstep] at hB
                          cases hv with
                          | head =>
                              have hcv : vertexCoveredB
                                  (compose mu (singleMatching q b))
                                  (Sum.inr b) = true := by
                                simp only [vertexCoveredB]
                                exact holeUsed_compose_single mu q b
                                  hfreeq
                              exact vertexCoveredB_mono_mAgree
                                (blocksOf_entry_spec fuel' _ vs D fs B
                                  hB).1 _ hcv
                          | tail _ hv' =>
                              exact vevents_pending_covered fuel'
                                (compose mu (singleMatching q b)) vs D fs
                                v hv' B hB
  termination_by fuel _ pending D _ _ _ =>
    (fuel, pending.length + D.length)

/-- The endpoints of a σ′-pair sit in the block's frozen vertex list. -/
theorem sigma_vertices_mem_termVertices {p h : Nat} (B : VBlock p h)
    (e : Fin p × Fin h) (he : e ∈ sigmaFull B) :
    Sum.inl e.1 ∈ termVertices B.entry B.term ∧
      Sum.inr e.2 ∈ termVertices B.entry B.term := by
  rcases (mem_sigmaFull B e).mp he with ⟨hmem, hunres⟩
  have hf : e ∈ B.term.filter (pairUnresolvedB B.entry) :=
    List.mem_filter.mpr ⟨hmem, hunres⟩
  unfold termVertices
  constructor
  · exact List.mem_bind.mpr ⟨e, hf, List.mem_cons_self _ _⟩
  · refine List.mem_bind.mpr ⟨e, hf, ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)

/-- Coverage against an entry beats unresolvedness: a pair covered at a
block's entry is vertex-disjoint from every σ′-pair of that block. -/
theorem pairDisjoint_of_covered_at_entry {p h : Nat} (B : VBlock p h)
    (e f : Fin p × Fin h)
    (he1 : vertexCoveredB B.entry (Sum.inl e.1) = true)
    (he2 : vertexCoveredB B.entry (Sum.inr e.2) = true)
    (hf : f ∈ sigmaFull B) : PairDisjoint e f := by
  have hunres := ((mem_sigmaFull B f).mp hf).2
  unfold pairUnresolvedB at hunres
  rw [Bool.and_eq_true] at hunres
  have hffree : B.entry f.1 = none := by
    have hb := hunres.1
    simpa using hb
  have hfhole : holeUsed B.entry f.2 = false := by
    have hb := hunres.2
    simpa using hb
  constructor
  · intro hef
    simp only [vertexCoveredB] at he1
    rw [hef, hffree] at he1
    simp at he1
  · intro hef
    simp only [vertexCoveredB] at he2
    rw [hef, hfhole] at he2
    cases he2

/-- **Cross-block σ-compatibility** (pin 3.1, the counterexample-killing
invariant): the σ′-families of distinct blocks are pairwise
vertex-disjoint — an earlier block's still-unset satisfying pairs have
both endpoints in its frozen list, the frozen list is drained (covered)
before any later block opens, and coverage beats the later block's
unresolvedness. This is exactly what vertex queries buy: no later term
can re-demand a hole the entered block owed. -/
theorem blocksOf_sigma_cross {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)),
      List.Pairwise
        (fun Bi Bj => ∀ e ∈ sigmaFull Bi, ∀ f ∈ sigmaFull Bj,
          PairDisjoint e f)
        (blocksOf (vevents fuel mu pending D feed))
  | _, _, [], [], feed => by
      rw [vevents_nil, blocksOf_nil]
      exact List.Pairwise.nil
  | fuel, mu, [], t :: rest, feed => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals]
          exact blocksOf_sigma_cross fuel mu [] rest feed
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals'
              hsat, blocksOf_nil]
            exact List.Pairwise.nil
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat',
                  blocksOf_nil]
                exact List.Pairwise.nil
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t rest feed hleg
                      hfals' hsat' htv, blocksOf_nil]
                    exact List.Pairwise.nil
                | cons v vs =>
                    cases v with
                    | inl i =>
                        have hfree : mu i = none :=
                          termVertices_head_pigeon_free mu t i vs htv
                        cases feed with
                        | nil =>
                            rw [vevents_entry_feed_nil fuel' mu t rest i
                              vs hleg hfals' hsat' htv, blocksOf_nil]
                            exact List.Pairwise.nil
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents_entry_feed_illkind fuel' mu t
                                  rest i vs q fs hleg hfals' hsat' htv,
                                  blocksOf_nil]
                                exact List.Pairwise.nil
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha, blocksOf_nil]
                                  exact List.Pairwise.nil
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv
                                    hha']
                                  rw [blocksOf_enter]
                                  rw [List.pairwise_cons]
                                  constructor
                                  · intro Bj hBj e he f hf
                                    have hBj' : Bj ∈ blocksOf
                                        (vevents fuel'
                                          (compose mu
                                            (singleMatching i a)) vs
                                          (t :: rest) fs) := by
                                      have h1 := hBj
                                      rw [show afterSteps
                                          (VEvent.qstep
                                            ⟨Sum.inl i, (i, a)⟩ ::
                                            vevents fuel'
                                              (compose mu
                                                (singleMatching i a)) vs
                                              (t :: rest) fs) =
                                          afterSteps (vevents fuel'
                                            (compose mu
                                              (singleMatching i a)) vs
                                            (t :: rest) fs) from rfl]
                                        at h1
                                      rw [blocksOf_afterSteps] at h1
                                      exact h1
                                    have hverts :=
                                      sigma_vertices_mem_termVertices
                                        ⟨t, mu, stepsPrefix
                                          (VEvent.qstep
                                            ⟨Sum.inl i, (i, a)⟩ ::
                                            vevents fuel'
                                              (compose mu
                                                (singleMatching i a)) vs
                                              (t :: rest) fs)⟩ e he
                                    have hcov1 : vertexCoveredB Bj.entry
                                        (Sum.inl e.1) = true := by
                                      have hv1 := hverts.1
                                      rw [htv] at hv1
                                      cases hv1 with
                                      | head =>
                                          have hcv : vertexCoveredB
                                              (compose mu
                                                (singleMatching e.1 a))
                                              (Sum.inl e.1) = true := by
                                            simp only [vertexCoveredB]
                                            rw [compose_single_self mu
                                              e.1 a hfree]
                                            rfl
                                          exact vertexCoveredB_mono_mAgree
                                            (blocksOf_entry_spec fuel' _
                                              vs (t :: rest) fs Bj
                                              hBj').1 _ hcv
                                      | tail _ hv' =>
                                          exact vevents_pending_covered
                                            fuel'
                                            (compose mu
                                              (singleMatching i a)) vs
                                            (t :: rest) fs _ hv' Bj hBj'
                                    have hcov2 : vertexCoveredB Bj.entry
                                        (Sum.inr e.2) = true := by
                                      have hv2 := hverts.2
                                      rw [htv] at hv2
                                      cases hv2 with
                                      | tail _ hv' =>
                                          exact vevents_pending_covered
                                            fuel'
                                            (compose mu
                                              (singleMatching i a)) vs
                                            (t :: rest) fs _ hv' Bj hBj'
                                    exact pairDisjoint_of_covered_at_entry
                                      Bj e f hcov1 hcov2 hf
                                  · have hrec := blocksOf_sigma_cross
                                      fuel'
                                      (compose mu (singleMatching i a))
                                      vs (t :: rest) fs
                                    rw [show afterSteps
                                        (VEvent.qstep
                                          ⟨Sum.inl i, (i, a)⟩ ::
                                          vevents fuel'
                                            (compose mu
                                              (singleMatching i a)) vs
                                            (t :: rest) fs) =
                                        afterSteps (vevents fuel'
                                          (compose mu
                                            (singleMatching i a)) vs
                                          (t :: rest) fs) from rfl]
                                    rw [blocksOf_afterSteps]
                                    exact hrec
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg']
        exact blocksOf_sigma_cross fuel mu [] rest feed
  | fuel, mu, v :: vs, D, feed => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov]
        exact blocksOf_sigma_cross fuel mu vs D feed
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov', blocksOf_nil]
            exact List.Pairwise.nil
        | succ fuel' =>
            cases v with
            | inl i =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov',
                      blocksOf_nil]
                    exact List.Pairwise.nil
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents_block_pigeon_illkind fuel' mu i vs D q
                          fs hcov', blocksOf_nil]
                        exact List.Pairwise.nil
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents_block_pigeon_dead fuel' mu i vs D a
                            fs hcov' hha, blocksOf_nil]
                          exact List.Pairwise.nil
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a
                            fs hcov' hha', blocksOf_qstep]
                          exact blocksOf_sigma_cross fuel'
                            (compose mu (singleMatching i a)) vs D fs
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov',
                      blocksOf_nil]
                    exact List.Pairwise.nil
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents_block_hole_illkind fuel' mu b vs D a
                          fs hcov', blocksOf_nil]
                        exact List.Pairwise.nil
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents_block_hole_dead fuel' mu b vs D q fs
                            hcov' hq, blocksOf_nil]
                          exact List.Pairwise.nil
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq', blocksOf_qstep]
                          exact blocksOf_sigma_cross fuel'
                            (compose mu (singleMatching q b)) vs D fs
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

/-! ## Stage 1b.3: the σ-join and the extension's well-definedness -/

/-- `PairDisjoint` is symmetric. -/
theorem pairDisjoint_symm {p h : Nat} :
    Symmetric (PairDisjoint (p := p) (h := h)) := by
  intro e f hef
  exact ⟨Ne.symm hef.1, Ne.symm hef.2⟩

/-- Every σ-list of the encode is the full or truncated σ′ of a member
block. -/
theorem mem_blockSigmas {p h : Nat} :
    ∀ (Bs : List (VBlock p h)) (l : List (Fin p × Fin h)),
      l ∈ blockSigmas Bs →
      ∃ B, B ∈ Bs ∧ (l = sigmaFull B ∨ l = sigmaTrunc B)
  | [], _, hl => by cases hl
  | [B], l, hl => by
      rw [show blockSigmas [B] = [sigmaTrunc B] from rfl] at hl
      cases hl with
      | head => exact ⟨B, List.mem_cons_self _ _, Or.inr rfl⟩
      | tail _ h' => cases h'
  | B :: B' :: Bs, l, hl => by
      rw [show blockSigmas (B :: B' :: Bs) =
        sigmaFull B :: blockSigmas (B' :: Bs) from rfl] at hl
      cases hl with
      | head => exact ⟨B, List.mem_cons_self _ _, Or.inl rfl⟩
      | tail _ h' =>
          rcases mem_blockSigmas (B' :: Bs) l h' with ⟨B'', hB'', hf⟩
          exact ⟨B'', List.mem_cons_of_mem _ hB'', hf⟩

/-- Elements of a σ-list lie in the σ′ of its block. -/
theorem mem_of_mem_blockSigmas {p h : Nat} (Bs : List (VBlock p h))
    (l : List (Fin p × Fin h)) (hl : l ∈ blockSigmas Bs)
    (e : Fin p × Fin h) (he : e ∈ l) :
    ∃ B, B ∈ Bs ∧ e ∈ sigmaFull B := by
  rcases mem_blockSigmas Bs l hl with ⟨B, hB, hf⟩
  refine ⟨B, hB, ?_⟩
  cases hf with
  | inl hfull =>
      rw [hfull] at he
      exact he
  | inr htrunc =>
      rw [htrunc] at he
      exact sigmaTrunc_subset_sigmaFull B e he

/-- The block-level cross relation transports to the σ-lists. -/
theorem blockSigmas_pairwise_transport {p h : Nat} :
    ∀ (Bs : List (VBlock p h)),
      List.Pairwise (fun Bi Bj => ∀ e ∈ sigmaFull Bi,
        ∀ f ∈ sigmaFull Bj, PairDisjoint e f) Bs →
      List.Pairwise (fun l1 l2 => ∀ x ∈ l1, ∀ y ∈ l2, PairDisjoint x y)
        (blockSigmas Bs)
  | [], _ => List.Pairwise.nil
  | [B], _ => by
      rw [show blockSigmas [B] = [sigmaTrunc B] from rfl]
      exact List.pairwise_singleton _ _
  | B :: B' :: Bs, hp => by
      rw [show blockSigmas (B :: B' :: Bs) =
        sigmaFull B :: blockSigmas (B' :: Bs) from rfl]
      rw [List.pairwise_cons] at hp ⊢
      constructor
      · intro l2 hl2 x hx y hy
        rcases mem_of_mem_blockSigmas (B' :: Bs) l2 hl2 y hy with
          ⟨B'', hB'', hy'⟩
        exact hp.1 B'' hB'' x hx y hy'
      · exact blockSigmas_pairwise_transport (B' :: Bs) hp.2

/-- **The σ-join is pairwise vertex-disjoint** (pin 3.1): in-block
disjointness from the legality gate, cross-block disjointness from the
coverage invariant. -/
theorem blockSigmas_join_pairwise {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) :
    List.Pairwise PairDisjoint
      (blockSigmas (blocksOf (vevents fuel mu pending D feed))).join := by
  rw [List.pairwise_join]
  constructor
  · intro l hl
    rcases mem_blockSigmas _ l hl with ⟨B, hB, hf⟩
    have hleg := (blocksOf_entry_spec fuel mu pending D feed B hB).2.1
    have hfull := sigmaFull_pairwise B hleg
    cases hf with
    | inl hfl =>
        rw [hfl]
        exact hfull
    | inr htr =>
        rw [htr]
        exact hfull.filter _
  · exact blockSigmas_pairwise_transport _
      (blocksOf_sigma_cross fuel mu pending D feed)

/-- The σ-join is fresh over the base matching. -/
theorem blockSigmas_join_fresh {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (e : Fin p × Fin h)
    (he : e ∈ (blockSigmas (blocksOf
      (vevents fuel mu pending D feed))).join) :
    mu e.1 = none ∧ holeUsed mu e.2 = false := by
  rcases List.mem_join.mp he with ⟨l, hl, hel⟩
  rcases mem_of_mem_blockSigmas _ l hl e hel with ⟨B, hB, he'⟩
  exact sigmaFull_fresh_over_base fuel mu pending D feed B hB e he'

/-- The pairs a pair-list overlay actually assigns are its members. -/
theorem pairsToMatching_eq_some {p h : Nat} :
    ∀ (l : List (Fin p × Fin h)) (j : Fin p) (b : Fin h),
      pairsToMatching l j = some b → (j, b) ∈ l
  | [], _, _, hj => by cases hj
  | e :: es, j, b, hj => by
      rw [show pairsToMatching (e :: es) =
        compose (singleMatching e.1 e.2) (pairsToMatching es) from rfl]
        at hj
      by_cases hje : j = e.1
      · have hsome : singleMatching e.1 e.2 j = some e.2 := by
          unfold singleMatching
          rw [if_pos hje]
        rw [compose_fixed_left _ _ j e.2 hsome] at hj
        have hbe : b = e.2 := by
          cases hj
          rfl
        have : (j, b) = e := by
          rw [hje, hbe]
        rw [this]
        exact List.mem_cons_self _ _
      · have hnone : singleMatching e.1 e.2 j = none := by
          unfold singleMatching
          rw [if_neg hje]
        rw [compose_free_left _ _ j hnone] at hj
        exact List.mem_cons_of_mem _ (pairsToMatching_eq_some es j b hj)

/-- A pairwise vertex-disjoint pair list overlays to a hole-injective
map. -/
theorem isMatching_pairsToMatching {p h : Nat}
    (l : List (Fin p × Fin h)) (hl : List.Pairwise PairDisjoint l) :
    IsMatching (pairsToMatching l) := by
  intro i j b hi hj
  have hmi : (i, b) ∈ l := pairsToMatching_eq_some l i b hi
  have hmj : (j, b) ∈ l := pairsToMatching_eq_some l j b hj
  by_contra hij
  have hne : (i, b) ≠ (j, b) := by
    intro hcontra
    apply hij
    exact congrArg Prod.fst hcontra
  have hd := hl.forall pairDisjoint_symm hmi hmj hne
  exact hd.2 rfl

/-- Freshness gives cross-consistency: the overlay never sends a fresh
pigeon into a hole the base already uses. -/
theorem crossConsistent_of_fresh {p h : Nat} (mu : MatchingMap p h)
    (l : List (Fin p × Fin h))
    (hfresh : ∀ e ∈ l, mu e.1 = none ∧ holeUsed mu e.2 = false) :
    CrossConsistent mu (pairsToMatching l) := by
  intro i j a hi _ hj1
  have hm : (j, a) ∈ l := pairsToMatching_eq_some l j a hj1
  have hfr := (hfresh (j, a) hm).2
  have hused : holeUsed mu a = true :=
    (holeUsed_eq_true_iff mu a).mpr ⟨i, hi⟩
  rw [hfr] at hused
  cases hused

/-- **Pin 3.1, well-definedness**: the extension `ρσ` is a partial
matching — `encodeExt` lands in `M`. σ's internal disjointness comes
from the legality gate, its cross-block disjointness from the coverage
invariant, and its ρ-compatibility from entry freshness; the walked
pairs never enter the overlay at all. -/
theorem encodeExt_isMatching {p h : Nat} (rho : MatchingMap p h)
    (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho) : IsMatching (encodeExt rho D feed) := by
  unfold encodeExt vtrace
  apply isMatching_compose hrho
  · exact isMatching_pairsToMatching _
      (blockSigmas_join_pairwise (freePigeons rho).card rho [] D feed)
  · exact crossConsistent_of_fresh rho _
      (blockSigmas_join_fresh (freePigeons rho).card rho [] D feed)

end PHPMatchingExtensionEncode
end PvNP
