import PvNP.AutoReviewedIteration

/-!
# Schedule-driven automatic many-round iterated collapse

The generated refined collapse machinery so far consumed per-stage layered
views and per-stage counting beats as SUPPLIED plan data.  This module removes
that: from one width-bounded start layer and a purely NUMERIC schedule (a list
of stage budgets `sᵢ` and star counts `ℓᵢ` whose beat conditions are
arithmetic propositions over `Nat` only), the whole many-round certificate is
generated automatically —

* `BeatArith m p s ℓ w` is the closed-form stage beat over a `p`-star base
  (via `restrictionsWithStars_card` / `refinesSubspace_card`);
* `ValidFrom m n w p sched` says every scheduled stage beats arithmetically,
  each stage entering at width `sᵢ₋₁ - 1` and star count `ℓᵢ₋₁`;
* `autoIteratedCollapse` builds, for EVERY schedule length `k`, a
  `GeneratedRefinedIteratedCertificate` of length `k`.  The PROOF constructs
  the witness so that every layer after the first is the automatic
  `nextLayer` re-viewing of the previous stage's generated trees; the
  STATEMENT records only the stage gate counts, budgets, and star counts.
  No layered views are supplied; the beats are supplied only as closed-form
  `Nat` arithmetic (`ValidFrom`), never as `Finset`-cardinality proofs.
  The empty schedule yields the trivial `.done` certificate; content lives
  in nonempty schedules, where each stage forces a real generated one-step
  certificate (a restriction with exactly `ℓᵢ` stars refining the
  accumulated base, trees of depth `< sᵢ`, semantics on all agreeing
  assignments).

## HONEST SCOPE STATEMENT (read this)

* The schedule's beat conditions are still PER-STAGE arithmetic side
  conditions; they are numeric (checkable by pure `Nat` arithmetic) but are
  not yet derived from a single product hypothesis.  Frozen-form B4 (single
  upfront depth-`d` view, product hypothesis `B(m, w, s, d)`, `t(d, s)` tree
  bound) remains OPEN.
* Realized widths of auto re-viewed gates may be smaller than the `sᵢ - 1`
  budgets (generated trees may be constants); width claims are BUDGET claims.
* A stage with `sᵢ = 1` threads entering width `0` to its tail: all later
  gates are width-budget-0 (constants) and their beats hold whenever `ℓᵢ`
  does not exceed the remaining star count (the `(8·0)^s` factor vanishes
  for `s ≥ 1`).  Such tails are real but degenerate stages.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.
  Gate A rung 4 remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace ScheduledAutoCollapse

set_option maxRecDepth 8192

attribute [local irreducible] SwitchingLemmaStatement.restrictionsWithStars
attribute [local irreducible] RefinedSubspace.refinesSubspace
attribute [local irreducible] SwitchingLemmaStatement.stars

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open RestrictionComposition
open RefinedSubspace
open GeneratedOneStepDepthReduction
open GeneratedIteratedCollapseFinal
open GeneratedRefinedCollapse

/-! ## Numeric schedules -/

/-- One stage of a numeric collapse schedule: a query budget `s` and a target
star count `ℓ`. -/
structure ScheduleStage where
  s : Nat
  ℓ : Nat

/-- The purely arithmetic stage beat for `m` gates of width `≤ w` over a
`p`-star base: the closed form of
`m * (|restrictionsWithStars p (ℓ - s)| * (8w)^s) < |refinesSubspace base ℓ|`
(and, with `p := n`, of the plain full-space beat). -/
def BeatArith (m p s ℓ w : Nat) : Prop :=
  m * (Nat.choose p (ℓ - s) * 2 ^ (p - (ℓ - s)) * (8 * w) ^ s) <
    Nat.choose p ℓ * 2 ^ (p - ℓ)

/-- Arithmetic validity of a schedule entered at width `w` and star count `p`
for `m` gates over `n` ambient variables: every stage's refined beat (over the
accumulated `p`-star base) and plain beat (over the `n`-variable full space)
hold, with the next stage entered at width `s - 1` and star count `ℓ`. -/
def ValidFrom (m n : Nat) : Nat → Nat → List ScheduleStage → Prop
  | _, _, [] => True
  | w, p, st :: rest =>
      BeatArith m p st.s st.ℓ w ∧ BeatArith m n st.s st.ℓ w ∧
        ValidFrom m n (st.s - 1) st.ℓ rest

/-! ## From arithmetic beats to a refined step input -/

/-- Package a width-bounded layer and the two arithmetic beats of one schedule
stage into a generated refined step input. -/
def stepInput {n : Nat} (base : Restriction n) (L : MinimalLayeredFormula n)
    (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    GeneratedRefinedStepInput n base where
  layer := L
  w := w
  s := st.s
  ℓ := st.ℓ
  width := hw
  beatRefined := by
    rw [restrictionsWithStars_card, refinesSubspace_card]
    exact hbr
  beatPlain := by
    rw [restrictionsWithStars_card, restrictionsWithStars_card]
    exact hbp

theorem stepInput_layer {n : Nat} (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    (stepInput base L w st hw hbr hbp).layer = L := rfl

theorem stepInput_s {n : Nat} (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    (stepInput base L w st hw hbr hbp).s = st.s := rfl

theorem stepInput_ℓ {n : Nat} (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    (stepInput base L w st hw hbr hbp).ℓ = st.ℓ := rfl

theorem stepInput_toPlain_layer {n : Nat} (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    (stepInput base L w st hw hbr hbp).toPlain.layer = L := rfl

theorem stepInput_toPlain_s {n : Nat} (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    (stepInput base L w st hw hbr hbp).toPlain.s = st.s := rfl

theorem stepInput_toPlain_ℓ {n : Nat} (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat) (st : ScheduleStage)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hbr : BeatArith L.gates.length (stars base) st.s st.ℓ w)
    (hbp : BeatArith L.gates.length n st.s st.ℓ w) :
    (stepInput base L w st hw hbr hbp).toPlain.ℓ = st.ℓ := rfl

/-! ## Formula-cast transport for certificates

Certificates are indexed by their start formula; the automatic iteration
rewrites the next stage's formula through `nextLayer_originalFormula`.  All
bookkeeping is transported through the cast by `subst`, never by kernel
reduction of the cast itself. -/

/-- Transport a certificate along an equality of start formulas. -/
def castFormula {n : Nat} {base : Restriction n} {F F' : BDFormula n}
    {d : Nat} (h : F = F')
    (c : GeneratedRefinedIteratedCertificate n base F d) :
    GeneratedRefinedIteratedCertificate n base F' d := h ▸ c

open GeneratedRefinedIteratedCertificate in
theorem castFormula_stageGateCounts {n : Nat} {base : Restriction n}
    {F F' : BDFormula n} {d : Nat} (h : F = F')
    (c : GeneratedRefinedIteratedCertificate n base F d) :
    (castFormula h c).stageGateCounts = c.stageGateCounts := by
  subst h
  rfl

open GeneratedRefinedIteratedCertificate in
theorem castFormula_stageBudgets {n : Nat} {base : Restriction n}
    {F F' : BDFormula n} {d : Nat} (h : F = F')
    (c : GeneratedRefinedIteratedCertificate n base F d) :
    (castFormula h c).stageBudgets = c.stageBudgets := by
  subst h
  rfl

open GeneratedRefinedIteratedCertificate in
theorem castFormula_stageStarCounts {n : Nat} {base : Restriction n}
    {F F' : BDFormula n} {d : Nat} (h : F = F')
    (c : GeneratedRefinedIteratedCertificate n base F d) :
    (castFormula h c).stageStarCounts = c.stageStarCounts := by
  subst h
  rfl

/-! ## The schedule-driven many-round theorem -/

open GeneratedRefinedIteratedCertificate in
/-- **Schedule-driven automatic many-round iterated collapse.**  From a
width-`w` start layer and a numeric schedule whose per-stage beats hold
arithmetically, a full generated refined iterated certificate of the
schedule's length exists.  The certificate's stage gate counts are constant,
and its stage budgets and star counts are exactly the schedule's.  The PROOF
constructs the witness with every layer after the first automatically
re-viewed from the previous stage's generated trees by `nextLayer`; the
statement itself records only the bookkeeping lists (a consumer must not
cite this theorem for the re-viewing property of an arbitrary witness). -/
theorem autoIteratedCollapse {n : Nat} :
    ∀ (sched : List ScheduleStage) (base : Restriction n)
      (L : MinimalLayeredFormula n) (w : Nat),
      (∀ g ∈ L.gates, widthDNF g.theDNF ≤ w) →
      ValidFrom L.gates.length n w (stars base) sched →
      ∃ cert : GeneratedRefinedIteratedCertificate n base
          L.originalFormula sched.length,
        cert.stageGateCounts = List.replicate sched.length L.gates.length ∧
        cert.stageBudgets = sched.map (fun st => st.s) ∧
        cert.stageStarCounts = sched.map (fun st => st.ℓ)
  | [], base, L, _w, _hw, _hv =>
      ⟨.done base L.originalFormula, rfl, rfl, rfl⟩
  | st :: rest, base, L, w, hw, hv => by
      obtain ⟨hbr, hbp, hrest⟩ := hv
      obtain ⟨C, href⟩ :=
        generatedRefinedOneStep_exists (stepInput base L w st hw hbr hbp)
      have hstars' : stars (compose base C.ρ) = st.ℓ := by
        rw [compose_eq_of_refinesWith href]
        have hmem := (mem_restrictionsWithStars C.ρ).mp C.stars
        rwa [stepInput_toPlain_ℓ] at hmem
      have hw' : ∀ g ∈ (AutoReviewedIteration.nextLayer C).gates,
          widthDNF g.theDNF ≤ st.s - 1 := by
        have h := AutoReviewedIteration.nextLayer_width C
        rwa [stepInput_toPlain_s] at h
      have hv' : ValidFrom (AutoReviewedIteration.nextLayer C).gates.length n
          (st.s - 1) (stars (compose base C.ρ)) rest := by
        rw [AutoReviewedIteration.nextLayer_gateCount, stepInput_toPlain_layer,
          hstars']
        exact hrest
      obtain ⟨rc, hgc, hb, hsc⟩ :=
        autoIteratedCollapse rest (compose base C.ρ)
          (AutoReviewedIteration.nextLayer C) (st.s - 1) hw' hv'
      refine ⟨.step (stepInput base L w st hw hbr hbp) C href
        (castFormula (AutoReviewedIteration.nextLayer_originalFormula C) rc),
        ?_, ?_, ?_⟩
      · simp only [stageGateCounts, castFormula_stageGateCounts, hgc,
          AutoReviewedIteration.nextLayer_gateCount, stepInput_toPlain_layer,
          stepInput_layer, List.length_cons, List.replicate_succ]
      · simp only [stageBudgets, castFormula_stageBudgets, hb, stepInput_s,
          List.map_cons]
      · simp only [stageStarCounts, castFormula_stageStarCounts, hsc,
          stepInput_ℓ, List.map_cons]

end ScheduledAutoCollapse
end PvNP
