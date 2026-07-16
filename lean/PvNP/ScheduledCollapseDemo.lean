import PvNP.ScheduledAutoCollapse

/-!
# A concrete scheduled three-stage instance with a budget-3 stage

One concrete run of the schedule-driven automatic many-round collapse
(`ScheduledAutoCollapse.autoIteratedCollapse`): `n = 10000` variables, one
width-1 start gate, and the numeric schedule

* stage 1: budget `s = 3` — the artifact's first counting-beat-backed stage
  budget `s > 2` (the earlier `GeneratedCNFLayerStage` record in
  `GraphIndexedBridge` carries `s = 49`, but with a directly supplied good
  restriction for a constant leaf tree, not a counting beat) — star count
  `ℓ = 561`;
* stage 2: budget `s = 2` at entering width `2`, star count `ℓ = 17`;
* stage 3: budget `s = 1` at entering width `1`, star count `ℓ = 1`.

All six beat conditions are proved by pure `Nat` arithmetic (stage-1/2 beats
by symbolic `Nat.choose` ratio chains; stage-3 beats by direct small-number
evaluation and positivity; no kernel evaluation of large binomials).  The
layers of stages 2 and 3 are generated automatically by `nextLayer` inside
`autoIteratedCollapse`; nothing stage-specific is supplied beyond the numbers
above.

## HONEST SCOPE STATEMENT (read this)

* One concrete finite formula-collapse certificate; no asymptotic family.
* Realized widths of the auto re-viewed stage-2/3 gates may be smaller than
  their budgets (generated trees may be constants); width claims are BUDGET
  claims.  Only the start gate is syntactically pinned at realized width 1.
* Frozen-form B4 (single upfront depth-`d` view, product hypothesis
  `B(m, w, s, d)`, `t(d, s)` tree bound) remains OPEN.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.
  Gate A rung 4 remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace ScheduledCollapseDemo

set_option maxRecDepth 8192
set_option exponentiation.threshold 400

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
open ScheduledAutoCollapse

/-! ## The start layer: one width-1 gate -/

def demoLit : Literal 10000 := ⟨⟨0, by omega⟩, true⟩

/-- The start gate: one single-literal DNF. -/
def demoGate : GateSpec 10000 :=
  GateSpec.dnf (BDFormula.lit demoLit)
    { D := [[demoLit]]
      sem_eq := by
        intro a
        simp [dnfEval, termEval, eval_lit]
      simple := by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm] }

/-- The start layer: one width-1 gate under an `or` parent. -/
def demoLayer : MinimalLayeredFormula 10000 :=
  { parent := ParentKind.or, gates := [demoGate] }

private theorem demoLayer_width :
    ∀ g ∈ demoLayer.gates, widthDNF g.theDNF ≤ 1 := by
  intro g hg
  have hg' : g = demoGate := by
    simpa [demoLayer] using hg
  subst hg'
  show widthDNF [[demoLit]] ≤ 1
  simp [widthDNF, termWidth]

private theorem demoLayer_length : demoLayer.gates.length = 1 := rfl

/-! ## The numeric schedule -/

/-- Stage budgets `[3, 2, 1]`, star counts `[561, 17, 1]`. -/
def demoSchedule : List ScheduleStage :=
  [⟨3, 561⟩, ⟨2, 17⟩, ⟨1, 1⟩]

/-! ## Symbolic choose-ratio arithmetic

Each ratio fact is proved by chaining the fully symbolic per-step bound
`choose_step_lt` (from `Nat.choose_succ_right_eq`): if
`m * (k + 1) < n - k` then `m * C(n, k) < C(n, k + 1)`.  No `omega` on
choose systems, no large coefficients, no kernel evaluation of binomials;
the largest literal appearing anywhere is `9985`.

ELABORATION-SAFETY NOTE (no soundness impact): on any goal containing
`Nat.choose` at large literals, every tactic step is restricted to
term-mode application in which each `Nat.choose` argument matches the
target SYNTACTICALLY (the choose arguments are pre-normalized by
closed-pattern `rw [show (561 - 3 : Nat) = 558 from rfl]`-style rewrites,
which only ever defeq-compare numerals with numerals).  Anything that
makes the unifier defeq-test a non-identical pattern against
`Nat.choose 10000 k` — a bare metavariable-pattern `rw` such as
`← Nat.mul_assoc`, a multi-round `simp only [← Nat.mul_assoc]`
normalization, or an argument mismatch like `15 =?= 17 - 2` resolved the
wrong way — delta-unfolds `Nat.choose` into its unmemoized Pascal
recursion and exhausts memory or the recursion-depth limit.  All
associativity/commutativity reasoning therefore lives in fully symbolic
helper lemmas (`chain2`, `chain3`, `beat_assemble`) whose rewrites only
ever meet variables.  (`2 ^ k` literals are protected by the
`exponentiation.threshold` gate and fail fast; `Nat.choose` has no such
gate, which is why the discipline above is load-bearing.) -/

/-- One symbolic ratio step: if the column ratio `(n - k) / (k + 1)` exceeds
`m`, one step right in Pascal's row multiplies a lower bound by `m`. -/
private theorem choose_step_lt {n k m : Nat}
    (hpos : 0 < Nat.choose n k) (h : m * (k + 1) < n - k) :
    m * Nat.choose n k < Nat.choose n (k + 1) := by
  have he := Nat.choose_succ_right_eq n k
  apply Nat.lt_of_mul_lt_mul_right (a := k + 1)
  rw [he]
  calc m * Nat.choose n k * (k + 1)
      = Nat.choose n k * (m * (k + 1)) := by
        rw [Nat.mul_comm m (Nat.choose n k), Nat.mul_assoc]
    _ < Nat.choose n k * (n - k) := Nat.mul_lt_mul_of_pos_left h hpos

/-- Two chained ratio steps, fully symbolic, flat conclusion. -/
private theorem chain2 {m a b c : Nat} (hm : 0 < m)
    (s1 : m * a < b) (s2 : m * b < c) : m * m * a < c := by
  have h : m * (m * a) < c :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_left s1 hm) s2
  have e : m * m * a = m * (m * a) := Nat.mul_assoc m m a
  rw [e]
  exact h

/-- Three chained ratio steps, fully symbolic, flat conclusion. -/
private theorem chain3 {m a b c d : Nat} (hm : 0 < m)
    (s1 : m * a < b) (s2 : m * b < c) (s3 : m * c < d) :
    m * m * m * a < d := by
  have h2 : m * (m * a) < c := by
    have e : m * (m * a) = m * m * a := (Nat.mul_assoc m m a).symm
    rw [e]
    exact chain2 hm s1 s2
  have h : m * (m * (m * a)) < d :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_left h2 hm) s3
  have e : m * m * m * a = m * (m * (m * a)) := by
    calc m * m * m * a = m * m * (m * a) := Nat.mul_assoc (m * m) m a
      _ = m * (m * (m * a)) := Nat.mul_assoc m m (m * a)
  rw [e]
  exact h

private theorem choose10000_ratio_561 :
    4096 * Nat.choose 10000 558 < Nat.choose 10000 561 := by
  have s1 : 16 * Nat.choose 10000 558 < Nat.choose 10000 559 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have s2 : 16 * Nat.choose 10000 559 < Nat.choose 10000 560 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have s3 : 16 * Nat.choose 10000 560 < Nat.choose 10000 561 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have h : 16 * 16 * 16 * Nat.choose 10000 558 < Nat.choose 10000 561 :=
    chain3 (by decide) s1 s2 s3
  rw [show (4096 : Nat) = 16 * 16 * 16 from by decide]
  exact h

private theorem choose561_ratio :
    1024 * Nat.choose 561 15 < Nat.choose 561 17 := by
  have s1 : 32 * Nat.choose 561 15 < Nat.choose 561 16 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have s2 : 32 * Nat.choose 561 16 < Nat.choose 561 17 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have h : 32 * 32 * Nat.choose 561 15 < Nat.choose 561 17 :=
    chain2 (by decide) s1 s2
  rw [show (1024 : Nat) = 32 * 32 from by decide]
  exact h

private theorem choose10000_ratio_17 :
    1024 * Nat.choose 10000 15 < Nat.choose 10000 17 := by
  have s1 : 32 * Nat.choose 10000 15 < Nat.choose 10000 16 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have s2 : 32 * Nat.choose 10000 16 < Nat.choose 10000 17 :=
    choose_step_lt (Nat.choose_pos (by decide)) (by decide)
  have h : 32 * 32 * Nat.choose 10000 15 < Nat.choose 10000 17 :=
    chain2 (by decide) s1 s2
  rw [show (1024 : Nat) = 32 * 32 from by decide]
  exact h

/-- Symbolic beat assembly: rebalance the power of two and compare via the
flat ratio bound.  All rewrites here meet only variables. -/
private theorem beat_assemble {m A B K x y e c : Nat}
    (hx : x + e = c + y) (hK : 2 ^ c * m = K) (hr : K * A < B) :
    m * (A * 2 ^ x * 2 ^ e) < B * 2 ^ y := by
  have hpow : (2 : Nat) ^ x * 2 ^ e = 2 ^ c * 2 ^ y := by
    rw [← pow_add, ← pow_add, hx]
  have hL : m * (A * 2 ^ x * 2 ^ e) = K * A * 2 ^ y := by
    rw [Nat.mul_assoc A, hpow, ← hK]
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hL]
  exact Nat.mul_lt_mul_of_lt_of_le hr (Nat.le_refl _)
    (Nat.pos_pow_of_pos _ (by decide))

/-! ## The six scheduled beats -/

private theorem demo_beat1 : BeatArith 1 10000 3 561 1 := by
  unfold BeatArith
  rw [show (561 - 3 : Nat) = 558 from rfl]
  rw [show ((4 : Nat) * 1) ^ 3 = 2 ^ 6 from rfl]
  exact beat_assemble (c := 9) (K := 512) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _
      (by decide : (512 : Nat) ≤ 4096)) choose10000_ratio_561)

private theorem demo_beat2r : BeatArith 1 561 2 17 2 := by
  unfold BeatArith
  rw [show (17 - 2 : Nat) = 15 from rfl]
  rw [show ((4 : Nat) * 2) ^ 2 = 2 ^ 6 from rfl]
  exact beat_assemble (c := 8) (K := 256) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _
      (by decide : (256 : Nat) ≤ 1024)) choose561_ratio)

private theorem demo_beat2p : BeatArith 1 10000 2 17 2 := by
  unfold BeatArith
  rw [show (17 - 2 : Nat) = 15 from rfl]
  rw [show ((4 : Nat) * 2) ^ 2 = 2 ^ 6 from rfl]
  exact beat_assemble (c := 8) (K := 256) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _
      (by decide : (256 : Nat) ≤ 1024)) choose10000_ratio_17)

private theorem demo_beat3r : BeatArith 1 17 1 1 1 := by
  unfold BeatArith
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceSub]
  decide

private theorem demo_beat3p : BeatArith 1 10000 1 1 1 := by
  unfold BeatArith
  have h : (1 : Nat) * (Nat.choose 10000 (1 - 1) * 2 ^ (10000 - (1 - 1)) *
      (4 * 1) ^ 1) = 8 * 2 ^ 9999 := by
    simp only [Nat.choose_zero_right, Nat.reduceSub, Nat.one_mul, Nat.mul_one,
      pow_one]
    rw [show (10000 : Nat) = 9999 + 1 from rfl, pow_succ]
    rw [Nat.mul_assoc]
    rw [show (2 * 4 : Nat) = 8 from rfl]
    exact Nat.mul_comm (2 ^ 9999) 8
  rw [h, Nat.choose_one_right, show (10000 - 1 : Nat) = 9999 from rfl]
  have hp : 0 < (2 : Nat) ^ 9999 := Nat.pos_pow_of_pos _ (by decide)
  exact Nat.mul_lt_mul_of_lt_of_le (by decide) (Nat.le_refl _) hp

/-! ## Schedule validity -/

private theorem demoSchedule_valid :
    ValidFrom 1 10000 1 10000 demoSchedule :=
  ⟨demo_beat1, demo_beat1, demo_beat2r, demo_beat2p, demo_beat3r,
    demo_beat3p, trivial⟩

/-! ## The concrete scheduled three-stage certificate -/

open GeneratedRefinedIteratedCertificate in
/-- **A proved scheduled three-stage instance with a budget-3 stage.**  The
schedule `[(3, 561), (2, 17), (1, 1)]` over `10000` variables runs from one
width-1 gate: three restrictions refine in sequence with star counts `561`,
`17`, `1`; a common total extension exists; and the final rewritten formula
computes the fully restricted original on every agreeing assignment.  The
PROOF builds the certificate via `autoIteratedCollapse`, so in the
CONSTRUCTED WITNESS the three restrictions are counting-generated and the
layers of stages 2 and 3 are automatically re-viewed by `nextLayer`; the
pinned STATEMENT records only the bookkeeping lists (gate counts, budgets,
star counts), `RefinesSeq`, the common total extension, and the
restricted-eval agreement — a consumer must not cite this theorem for the
re-viewing (or generation) property of an arbitrary witness. -/
theorem scheduledThreeStage_budget3_nonvacuous :
    ∃ cert : GeneratedRefinedIteratedCertificate 10000 (freeRestriction 10000)
        (BDFormula.or [BDFormula.lit demoLit]) 3,
      cert.stageGateCounts = [1, 1, 1] ∧
      cert.stageBudgets = [3, 2, 1] ∧
      cert.stageStarCounts = [561, 17, 1] ∧
      RefinesSeq (freeRestriction 10000) cert.stageRestrictions ∧
      (∃ a : Assignment 10000, Agree cert.finalComposed a) ∧
      (∀ a : Assignment 10000, Agree cert.finalComposed a →
        eval a cert.finalFormula =
          eval a (restrict cert.finalComposed
            (BDFormula.or [BDFormula.lit demoLit]))) := by
  have hvalid : ValidFrom demoLayer.gates.length 10000 1
      (stars (freeRestriction 10000)) demoSchedule := by
    rw [stars_freeRestriction, demoLayer_length]
    exact demoSchedule_valid
  obtain ⟨cert, hgc, hb, hsc⟩ :=
    autoIteratedCollapse demoSchedule (freeRestriction 10000) demoLayer 1
      demoLayer_width hvalid
  refine ⟨cert, ?_, ?_, ?_, stageRestrictions_refinesSeq cert,
    finalComposed_extension cert, finalFormula_restrict_eval cert⟩
  · rw [hgc]; rfl
  · rw [hb]; rfl
  · rw [hsc]; rfl

end ScheduledCollapseDemo
end PvNP
