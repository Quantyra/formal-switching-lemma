import PvNP.FrozenProductSchedule

/-!
# Ratio-form frozen-product schedules and an asymptotic geometric family

`FrozenProductSchedule` bridges a SUPPLIED product-bound family `B(m,w,s,d)`
to the `ValidFrom` obligations of `autoIteratedCollapse`, but its single `B`
value must sit between the raw bad count and the star space over BOTH the
current refinement space `p` and the ambient space `n` at every stage; for
`p < n` and width budget `w >= 1` no such value exists past the first stage,
so all nondegenerate instances of that interface have width-0 tails.

This module replaces the absolute bound family with a RATIO-form regime
condition that is aware of the current space: `32*m*w*l <= p` (with
`1 <= s <= l`).  The per-stage `BeatArith` obligations are then PROVED, not
supplied, by fully symbolic binomial-ratio arithmetic
(`Nat.choose_succ_right_eq`), and a named schedule regime — the geometric
star schedule, all budgets `2`, star counts dividing by `64*m` each stage —
satisfies the regime at every stage.  The headline is the artifact's first
asymptotic-FAMILY scheduled statement: for EVERY round count `k + 1` and
EVERY `n >= 2 * 64^(k+1)`, a `(k+1)`-stage generated refined certificate
exists whose stages ALL have width budget `>= 1` and query budget `2`
(no width-0 tail at all).

## HONEST SCOPE STATEMENT (read this)

* The start layer is still a SUPPLIED simple family (one single-literal
  width-1 gate); no arbitrary layered decomposition of an AC0 formula is
  performed.  Frozen-form B4 remains OPEN.
* Realized widths of automatically re-viewed gates are BUDGET claims
  (generated trees may be constants); "nondegenerate" refers to the width
  BUDGET `>= 1` entering every stage, so every stage's beat carries a
  nonvanishing `(8w)^s` factor with `s = 2`.  The start layer's realized
  width IS exactly `1` (`familyGate_width_realized`).
* `autoIteratedCollapse`'s statement-vs-witness caveat applies unchanged:
  the statement records bookkeeping lists only; the automatic re-viewing
  property is a property of the constructed witness.
* The published `FrozenProductSchedule` interface is imported and reused
  (`TreeBudgetFrom`, `stageS`, `stageStars`); it is never modified.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma (Gate A rung 4 remains open), NOT an
  NP/circuit lower bound, NOT a statement about P vs NP.

ELABORATION-SAFETY NOTE (no soundness impact): every lemma in this module is
fully symbolic — no `Nat.choose` at large literals ever appears in any goal,
so the choose-literal defeq hazard documented in `ScheduledCollapseDemo`
cannot arise.  The only literals are one- and two-digit constants
(2, 8, 16, 32, 64) and, in the final corollary, the instance size `8192`,
which never occurs inside a `Nat.choose` evaluation.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FrozenProductScheduleRatio

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
open FrozenProductSchedule

/-! ## Symbolic binomial-ratio machinery -/

/-- One symbolic ratio step (public counterpart of the demo's private
helper): if the column ratio `(p - k) / (k + 1)` exceeds `M`, one step right
in Pascal's row multiplies a lower bound by `M`. -/
theorem choose_step_lt {p k M : Nat}
    (hpos : 0 < Nat.choose p k) (h : M * (k + 1) < p - k) :
    M * Nat.choose p k < Nat.choose p (k + 1) := by
  have he := Nat.choose_succ_right_eq p k
  apply Nat.lt_of_mul_lt_mul_right (a := k + 1)
  rw [he]
  calc M * Nat.choose p k * (k + 1)
      = Nat.choose p k * (M * (k + 1)) := by
        rw [Nat.mul_comm M (Nat.choose p k), Nat.mul_assoc]
    _ < Nat.choose p k * (p - k) := Nat.mul_lt_mul_of_pos_left h hpos

/-- `s + 1` chained ratio steps: if every scheduled column ratio in the
window exceeds `M`, then `M^(s+1)` times the left binomial is strictly below
the right binomial.  Fully symbolic. -/
theorem choose_ratio_pow {p M : Nat} (hM : 0 < M) :
    ∀ (s a : Nat), a + (s + 1) ≤ p →
      (∀ j, a ≤ j → j < a + (s + 1) → M * (j + 1) < p - j) →
      M ^ (s + 1) * Nat.choose p a < Nat.choose p (a + (s + 1))
  | 0, a, hp, h => by
      have hpos : 0 < Nat.choose p a := Nat.choose_pos (by omega)
      have hstep : M * Nat.choose p a < Nat.choose p (a + 1) :=
        choose_step_lt hpos (h a (Nat.le_refl a) (by omega))
      simpa using hstep
  | s + 1, a, hp, h => by
      have hpos : 0 < Nat.choose p a := Nat.choose_pos (by omega)
      have hstep : M * Nat.choose p a < Nat.choose p (a + 1) :=
        choose_step_lt hpos (h a (Nat.le_refl a) (by omega))
      have hrec : M ^ (s + 1) * Nat.choose p (a + 1) <
          Nat.choose p ((a + 1) + (s + 1)) :=
        choose_ratio_pow hM s (a + 1) (by omega)
          (fun j hj1 hj2 => h j (by omega) (by omega))
      have hMpow : 0 < M ^ (s + 1) := Nat.pos_pow_of_pos _ hM
      have h1 : M ^ (s + 1) * (M * Nat.choose p a) <
          M ^ (s + 1) * Nat.choose p (a + 1) :=
        Nat.mul_lt_mul_of_pos_left hstep hMpow
      have e : M ^ (s + 1 + 1) * Nat.choose p a =
          M ^ (s + 1) * (M * Nat.choose p a) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      have eidx : (a + 1) + (s + 1) = a + (s + 1 + 1) := by omega
      rw [eidx] at hrec
      rw [e]
      exact Nat.lt_trans h1 hrec

/-! ## From the ratio regime to the closed-form stage beat -/

private theorem sub_shift {p l s : Nat} (h1 : s ≤ l) (h2 : l ≤ p) :
    p - (l - s) = p - l + s := by omega

private theorem regime_step {a b j l p : Nat}
    (h1 : a ≤ b) (h2 : j < l) (h3 : l ≤ b) (h4 : b + b ≤ p) :
    a < p - j := by omega

/-- Pure AC reshaping of the beat's left side; every factor is a variable. -/
private theorem beat_shape {m A B c e d : Nat} (hc : 0 < c)
    (h : m * (e * d) * A < B) :
    m * (A * (c * e) * d) < B * c := by
  have hE : m * (A * (c * e) * d) = m * (e * d) * A * c := by
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hE]
  exact Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl c) hc

private theorem le_self_pow {m : Nat} : ∀ {s : Nat}, 1 ≤ s → m ≤ m ^ s
  | s + 1, _ => by
      match m with
      | 0 => exact Nat.zero_le _
      | m' + 1 =>
          have hp : 1 ≤ (m' + 1) ^ s := Nat.pos_pow_of_pos s (Nat.succ_pos m')
          calc m' + 1 = 1 * (m' + 1) := (Nat.one_mul _).symm
            _ ≤ (m' + 1) ^ s * (m' + 1) := Nat.mul_le_mul_right (m' + 1) hp
            _ = (m' + 1) ^ (s + 1) := (Nat.pow_succ _ _).symm

private theorem mul_pow_le {m w s : Nat} (hs : 1 ≤ s) :
    m * (16 * w) ^ s ≤ (16 * m * w) ^ s := by
  have h1 : m * (16 * w) ^ s ≤ m ^ s * (16 * w) ^ s :=
    Nat.mul_le_mul_right _ (le_self_pow hs)
  have h2 : m ^ s * (16 * w) ^ s = (m * (16 * w)) ^ s :=
    (Nat.mul_pow m (16 * w) s).symm
  have h3 : m * (16 * w) = 16 * m * w := by
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [h2, h3] at h1
  exact h1

private theorem le_of_regime {m w l p : Nat} (hm : 1 ≤ m) (hw : 1 ≤ w)
    (h : 32 * m * w * l ≤ p) : l ≤ p := by
  have hM32 : (1 : Nat) ≤ 32 * m * w :=
    Nat.le_trans (by decide : (1 : Nat) ≤ 1 * 1 * 1)
      (Nat.mul_le_mul (Nat.mul_le_mul (by decide : (1 : Nat) ≤ 32) hm) hw)
  have h1 : 1 * l ≤ 32 * m * w * l := Nat.mul_le_mul_right l hM32
  rw [Nat.one_mul] at h1
  exact Nat.le_trans h1 h

/-- **The ratio-form regime discharges the closed-form stage beat.**  With
`1 <= m`, `1 <= w`, `1 <= s <= l`, and the space-aware ratio condition
`32*m*w*l <= p`, the `BeatArith` obligation over `p` holds — proved by the
symbolic binomial-ratio chain, never by kernel evaluation of binomials. -/
theorem ratio_beat {m p s l w : Nat}
    (hm : 1 ≤ m) (hw : 1 ≤ w) (hs : 1 ≤ s) (hsl : s ≤ l)
    (hreg : 32 * m * w * l ≤ p) :
    BeatArith m p s l w := by
  have hM16 : (1 : Nat) ≤ 16 * m * w :=
    Nat.le_trans (by decide : (1 : Nat) ≤ 1 * 1 * 1)
      (Nat.mul_le_mul (Nat.mul_le_mul (by decide : (1 : Nat) ≤ 16) hm) hw)
  have h0M : 0 < 16 * m * w := Nat.lt_of_lt_of_le (by decide) hM16
  have hlp : l ≤ p := le_of_regime hm hw hreg
  have h32 : 32 * m * w * l = 16 * m * w * l + 16 * m * w * l := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Nat.add_mul, Nat.add_mul,
      Nat.add_mul]
  have h2 : 16 * m * w * l + 16 * m * w * l ≤ p := h32 ▸ hreg
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  unfold BeatArith
  rw [sub_shift hsl hlp, Nat.pow_add]
  have hc : 0 < 2 ^ (p - l) := Nat.pos_pow_of_pos (p - l) (by decide)
  apply beat_shape hc
  have hfold : (2 : Nat) ^ (s' + 1) * (8 * w) ^ (s' + 1) =
      (16 * w) ^ (s' + 1) := by
    rw [← Nat.mul_pow]
    have h216 : (2 : Nat) * (8 * w) = 16 * w := by omega
    rw [h216]
  rw [hfold]
  have hle : m * (16 * w) ^ (s' + 1) ≤ (16 * m * w) ^ (s' + 1) :=
    mul_pow_le (by omega)
  have hchain : (16 * m * w) ^ (s' + 1) * Nat.choose p (l - (s' + 1)) <
      Nat.choose p (l - (s' + 1) + (s' + 1)) := by
    apply choose_ratio_pow h0M s' (l - (s' + 1)) (by omega)
    intro j _hj1 hj2
    have hj3 : j < l := by omega
    have hb1 : 16 * m * w * (j + 1) ≤ 16 * m * w * l :=
      Nat.mul_le_mul_left _ (by omega)
    have hb2 : l ≤ 16 * m * w * l := by
      have h1 : 1 * l ≤ 16 * m * w * l := Nat.mul_le_mul_right l hM16
      rw [Nat.one_mul] at h1
      exact h1
    exact regime_step hb1 hj3 hb2 h2
  have hidx : l - (s' + 1) + (s' + 1) = l := by omega
  rw [hidx] at hchain
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hchain

/-! ## The ratio-form schedule hypothesis -/

/-- The ratio-form regime condition for one stage over its entering space
`p`: positive budget, budget at most the target star count, and the
space-aware ratio bound `32*m*w*l <= p`. -/
def RatioRegime (m w p : Nat) (st : ScheduleStage) : Prop :=
  1 ≤ stageS st ∧ stageS st ≤ stageStars st ∧
    32 * m * w * stageStars st ≤ p

/-- The regime is monotone in the space parameter. -/
theorem RatioRegime.mono {m w p n : Nat} {st : ScheduleStage}
    (hpn : p ≤ n) (h : RatioRegime m w p st) : RatioRegime m w n st :=
  ⟨h.1, h.2.1, Nat.le_trans h.2.2 hpn⟩

/-- A ratio-regime stage discharges its own `BeatArith` obligation. -/
theorem ratioRegime_beat {m w p : Nat} {st : ScheduleStage}
    (hm : 1 ≤ m) (hw : 1 ≤ w) (h : RatioRegime m w p st) :
    BeatArith m p (stageS st) (stageStars st) w :=
  ratio_beat hm hw h.1 h.2.1 h.2.2

/-- Ratio-regime validity of a whole schedule: every stage satisfies the
ratio regime over its entering space, with entering width `s - 1` and space
`l` threaded exactly as in `ValidFrom`.  Note the per-stage entering width
must be positive: this hypothesis has NO degenerate width-0 stages. -/
def RegimeFrom (m : Nat) : Nat → Nat → List ScheduleStage → Prop
  | _, _, [] => True
  | w, p, st :: rest =>
      1 ≤ w ∧ RatioRegime m w p st ∧
        RegimeFrom m (stageS st - 1) (stageStars st) rest

/-- **Ratio-form schedule hypothesis synthesis.**  A ratio-regime schedule
hypothesis derives the exact `ValidFrom` obligations consumed by
`autoIteratedCollapse` — with every per-stage beat PROVED from the
space-aware ratio condition, not supplied.  This is the ratio-form repair of
the `p`-independent `B(m,w,s,d)` limitation of `ProductValidFrom`, whose
single bound value cannot support nondegenerate post-first stages when
`p < n`. -/
theorem regimeFrom_validFrom {m n : Nat} (hm : 1 ≤ m) :
    ∀ (sched : List ScheduleStage) (w p : Nat), p ≤ n →
      RegimeFrom m w p sched → ValidFrom m n w p sched
  | [], _, _, _, _ => trivial
  | st :: rest, w, p, hpn, h => by
      obtain ⟨hw, hreg, hrest⟩ := h
      cases st with
      | mk s l =>
          obtain ⟨hs, hsl, hrp⟩ := hreg
          have hbp : BeatArith m p s l w := ratio_beat hm hw hs hsl hrp
          have hbn : BeatArith m n s l w :=
            ratio_beat hm hw hs hsl (Nat.le_trans hrp hpn)
          have hln : l ≤ n := Nat.le_trans (le_of_regime hm hw hrp) hpn
          exact ⟨hbp, hbn,
            regimeFrom_validFrom hm rest (s - 1) l hln hrest⟩

/-! ## Collapse theorem consuming the ratio-form hypothesis -/

open GeneratedRefinedIteratedCertificate in
/-- **Schedule collapse from the ratio-form regime.**  A width-bounded start
layer plus a ratio-regime schedule hypothesis yields the full
schedule-driven certificate, with the same bookkeeping as
`autoIteratedCollapse` and the frozen-product bridge's `t(d,s)` tree-budget
facts preserved.  The per-stage beats are PROVED from the regime; no beat is
supplied. -/
theorem autoIteratedCollapse_of_ratioRegime {n : Nat}
    (t : Nat → Nat → Nat)
    (sched : List ScheduleStage) (base : Restriction n)
    (L : MinimalLayeredFormula n) (w : Nat)
    (hm : 1 ≤ L.gates.length)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hreg : RegimeFrom L.gates.length w (stars base) sched)
    (ht : TreeBudgetFrom t L.gates.length sched.length sched) :
    ∃ cert : GeneratedRefinedIteratedCertificate n base
        L.originalFormula sched.length,
      cert.stageGateCounts = List.replicate sched.length L.gates.length ∧
      cert.stageBudgets = sched.map stageS ∧
      cert.stageStarCounts = sched.map stageStars ∧
      TreeBudgetFrom t L.gates.length sched.length sched := by
  obtain ⟨cert, hgc, hb, hsc⟩ :=
    ScheduledAutoCollapse.autoIteratedCollapse sched base L w hw
      (regimeFrom_validFrom hm sched w (stars base) (stars_le base) hreg)
  refine ⟨cert, hgc, ?_, ?_, ht⟩
  · simpa [stageS] using hb
  · simpa [stageStars] using hsc

/-! ## The named geometric star regime -/

/-- **The geometric star schedule.**  All stage budgets are `2`; star counts
divide by `64*m` at each stage.  Every stage of the resulting schedule
enters with width budget `>= 1`: the supplied start width bound for the
first stage and `2 - 1 = 1` for all later stages — no width-0 tail. -/
def geometricSchedule (m : Nat) : Nat → Nat → List ScheduleStage
  | _, 0 => []
  | l, k + 1 => ScheduleStage.mk 2 l :: geometricSchedule m (l / (64 * m)) k

theorem geometricSchedule_length (m : Nat) :
    ∀ (k l : Nat), (geometricSchedule m l k).length = k
  | 0, _ => rfl
  | k + 1, l => by
      show (ScheduleStage.mk 2 l ::
        geometricSchedule m (l / (64 * m)) k).length = k + 1
      rw [List.length_cons, geometricSchedule_length m k]

theorem geometricSchedule_budgets (m : Nat) :
    ∀ (k l : Nat),
      (geometricSchedule m l k).map stageS = List.replicate k 2
  | 0, _ => rfl
  | k + 1, l => by
      show (ScheduleStage.mk 2 l ::
          geometricSchedule m (l / (64 * m)) k).map stageS =
        List.replicate (k + 1) 2
      rw [List.map_cons, geometricSchedule_budgets m k, List.replicate_succ]
      rfl

private theorem div_step_regime {m l : Nat} :
    32 * m * 1 * (l / (64 * m)) ≤ l := by
  have h1 : 32 * m * 1 ≤ 64 * m := by omega
  have h2 : 32 * m * 1 * (l / (64 * m)) ≤ 64 * m * (l / (64 * m)) :=
    Nat.mul_le_mul_right _ h1
  have h3 : 64 * m * (l / (64 * m)) = l / (64 * m) * (64 * m) :=
    Nat.mul_comm _ _
  have h4 : l / (64 * m) * (64 * m) ≤ l := Nat.div_mul_le_self l (64 * m)
  rw [h3] at h2
  exact Nat.le_trans h2 h4

private theorem div_step_lower {m l k : Nat} (hq : 0 < 64 * m)
    (h : 2 * (64 * m) ^ (k + 1) ≤ l) :
    2 * (64 * m) ^ k ≤ l / (64 * m) := by
  rw [Nat.le_div_iff_mul_le hq]
  rw [Nat.mul_assoc, ← Nat.pow_succ]
  exact h

private theorem two_le_of_pow {m l k : Nat} (hq : 0 < 64 * m)
    (h : 2 * (64 * m) ^ k ≤ l) : 2 ≤ l := by
  have h1 : 1 ≤ (64 * m) ^ k := Nat.pos_pow_of_pos k hq
  have h2 : 2 * 1 ≤ 2 * (64 * m) ^ k := Nat.mul_le_mul_left 2 h1
  rw [Nat.mul_one] at h2
  exact Nat.le_trans h2 h

/-- **The geometric star regime satisfies the ratio regime at every
stage.**  One entry condition (`2 * (64*m)^k <= l`, so the star counts stay
at least `2` through all `k + 1` stages) and one first-stage space condition
(`32*m*w*l <= p`) validate the whole schedule; the per-stage conditions of
all later stages are self-sustained by the geometric division. -/
theorem geometricSchedule_regime {m : Nat} (hm : 1 ≤ m) :
    ∀ (k l p w : Nat), 1 ≤ w → 2 * (64 * m) ^ k ≤ l →
      32 * m * w * l ≤ p →
      RegimeFrom m w p (geometricSchedule m l (k + 1))
  | 0, l, p, w, hw, hl, hp => by
      have hq : 0 < 64 * m := Nat.mul_pos (by decide) hm
      exact ⟨hw, ⟨(by decide : (1 : Nat) ≤ 2), two_le_of_pow hq hl, hp⟩,
        trivial⟩
  | k + 1, l, p, w, hw, hl, hp => by
      have hq : 0 < 64 * m := Nat.mul_pos (by decide) hm
      refine ⟨hw, ⟨(by decide : (1 : Nat) ≤ 2), two_le_of_pow hq hl, hp⟩, ?_⟩
      exact geometricSchedule_regime hm k (l / (64 * m)) l 1
        (Nat.le_refl 1) (div_step_lower hq hl) div_step_regime

/-- The geometric schedule's tree budgets against the constant family
`t(d,s) = m`: each stage's budget is `m * (2 - 1) = m`. -/
theorem geometricSchedule_treeBudget (m q : Nat) :
    ∀ (k l depth : Nat),
      TreeBudgetFrom (fun _ _ => m) m depth (geometricSchedule q l k)
  | 0, _, _ => trivial
  | k + 1, l, depth => by
      refine ⟨?_, geometricSchedule_treeBudget m q k (l / (64 * q))
        (depth - 1)⟩
      exact Nat.le_of_eq (Nat.mul_one m)

/-! ## The supplied start-layer family (one single-literal width-1 gate) -/

/-- The family's start literal for `n + 1` variables: variable `0`,
positive polarity. -/
def familyLit (n : Nat) : Literal (n + 1) := ⟨⟨0, Nat.succ_pos n⟩, true⟩

/-- The family's start gate: a single-literal DNF for `n >= 1` (realized
width exactly `1`), and the width-0 constant-true gate at `n = 0` (never
reached by the family theorem, which requires `n >= 128`). -/
def familyGate : (n : Nat) → GateSpec n
  | 0 =>
      GateSpec.dnf BDFormula.tru
        { D := ([[]] : DNF 0)
          sem_eq := by
            intro a
            simp [BoundedDepthFrege.eval, dnfEval, termEval]
          simple := by
            intro t ht
            simp only [List.mem_singleton] at ht
            subst ht
            simp [SimpleTerm] }
  | n + 1 =>
      GateSpec.dnf (BDFormula.lit (familyLit n))
        { D := [[familyLit n]]
          sem_eq := by
            intro a
            simp [dnfEval, termEval, eval_lit]
          simple := by
            intro t ht
            simp only [List.mem_singleton] at ht
            subst ht
            simp [SimpleTerm] }

/-- The family's start layer: one gate under an `or` parent. -/
def familyLayer (n : Nat) : MinimalLayeredFormula n :=
  { parent := ParentKind.or, gates := [familyGate n] }

theorem familyLayer_length (n : Nat) : (familyLayer n).gates.length = 1 := rfl

theorem familyLayer_width (n : Nat) :
    ∀ g ∈ (familyLayer n).gates, widthDNF g.theDNF ≤ 1 := by
  intro g hg
  have hg' : g = familyGate n := by
    simpa [familyLayer] using hg
  subst hg'
  cases n with
  | zero =>
      show widthDNF ([[]] : DNF 0) ≤ 1
      simp [widthDNF, termWidth]
  | succ n' =>
      show widthDNF [[familyLit n']] ≤ 1
      simp [widthDNF, termWidth]

/-- For every `n >= 1` the family gate's realized DNF width is exactly `1`:
the width-1 start claim is realized, not merely a budget. -/
theorem familyGate_width_realized (n : Nat) :
    widthDNF (familyGate (n + 1)).theDNF = 1 := by
  show widthDNF [[familyLit n]] = 1
  simp [widthDNF, termWidth]

/-! ## The asymptotic-family headline -/

private theorem div32_le (x : Nat) : 32 * (x / 64) ≤ x := by omega

open GeneratedRefinedIteratedCertificate in
/-- **Asymptotic geometric-family scheduled collapse.**  For EVERY round
count `k + 1` and EVERY ambient size `n >= 2 * 64^(k+1)`, the geometric star
regime produces a `(k+1)`-stage generated refined iterated certificate over
the supplied one-gate width-1 start layer: constant stage gate count `1`,
ALL stage budgets `2` (every stage enters with width budget `>= 1` — no
width-0 tail), star counts `n/64, n/64^2, ...`, and the constant tree-budget
family `t(d,s) = 1` preserved.  The per-stage beats are PROVED from the
ratio regime; this is a parameterized asymptotic FAMILY of scheduled
collapses, not a single finite instance.

Still NOT frozen-form B4 closure (the start layer is a supplied simple
family), NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a
statement about P vs NP. -/
theorem geometricFamilyCollapse (k : Nat) {n : Nat}
    (hn : 2 * 64 ^ (k + 1) ≤ n) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (familyLayer n).originalFormula (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) 1 ∧
      cert.stageBudgets = List.replicate (k + 1) 2 ∧
      cert.stageStarCounts =
        (geometricSchedule 1 (n / 64) (k + 1)).map stageStars ∧
      TreeBudgetFrom (fun _ _ => 1) 1 (k + 1)
        (geometricSchedule 1 (n / 64) (k + 1)) := by
  have hq : 0 < (64 : Nat) := by decide
  have hl : 2 * (64 * 1) ^ k ≤ n / 64 := by
    rw [show ((64 : Nat) * 1) = 64 from rfl, Nat.le_div_iff_mul_le hq,
      Nat.mul_assoc, ← Nat.pow_succ]
    exact hn
  have hp : 32 * 1 * 1 * (n / 64) ≤ n := by
    rw [show ((32 : Nat) * 1 * 1) = 32 from rfl]
    exact div32_le n
  have hreg : RegimeFrom 1 1 n (geometricSchedule 1 (n / 64) (k + 1)) :=
    geometricSchedule_regime (Nat.le_refl 1) k (n / 64) n 1
      (Nat.le_refl 1) hl hp
  have hlen : (geometricSchedule 1 (n / 64) (k + 1)).length = k + 1 :=
    geometricSchedule_length 1 (k + 1) (n / 64)
  have hm1 : 1 ≤ (familyLayer n).gates.length :=
    Nat.le_of_eq (familyLayer_length n).symm
  have hreg' : RegimeFrom (familyLayer n).gates.length 1
      (stars (freeRestriction n)) (geometricSchedule 1 (n / 64) (k + 1)) := by
    rw [familyLayer_length, stars_freeRestriction]
    exact hreg
  have ht2 : TreeBudgetFrom (fun _ _ => 1) (familyLayer n).gates.length
      (geometricSchedule 1 (n / 64) (k + 1)).length
      (geometricSchedule 1 (n / 64) (k + 1)) := by
    rw [familyLayer_length, hlen]
    exact geometricSchedule_treeBudget 1 1 (k + 1) (n / 64) (k + 1)
  have hex := autoIteratedCollapse_of_ratioRegime (fun _ _ => 1)
    (geometricSchedule 1 (n / 64) (k + 1)) (freeRestriction n)
    (familyLayer n) 1 hm1 (familyLayer_width n) hreg' ht2
  rw [hlen, familyLayer_length, geometricSchedule_budgets] at hex
  exact hex

/-! ## A concrete two-genuine-stage instance of the family -/

open GeneratedRefinedIteratedCertificate in
/-- The family instantiated at `n = 8192`, two rounds: a concrete two-stage
certificate whose stages BOTH have width budget `>= 1` (budgets `[2, 2]`,
star counts `[128, 2]`) — a multi-stage scheduled instance with no width-0
tail.  This is a single finite instance of `geometricFamilyCollapse`, shown
only to witness the family bound `2 * 64^2 = 8192` exactly at its
boundary. -/
theorem geometricFamily_eightK_twoStage :
    ∃ cert : GeneratedRefinedIteratedCertificate 8192 (freeRestriction 8192)
        (familyLayer 8192).originalFormula 2,
      cert.stageGateCounts = [1, 1] ∧
      cert.stageBudgets = [2, 2] ∧
      cert.stageStarCounts = [128, 2] ∧
      TreeBudgetFrom (fun _ _ => 1) 1 2 (geometricSchedule 1 128 2) := by
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    geometricFamilyCollapse 1 (n := 8192) (by decide)
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc]
    rfl
  · rw [hb]
    rfl
  · rw [hsc]
    rfl
  · exact ht

/-! ## Universal-layer form: every bounded start layer admits the family -/

private theorem regime_space_bound {m w n : Nat} :
    32 * m * w * (n / (64 * m * w)) ≤ n := by
  have h0 : 32 * m ≤ 64 * m := Nat.mul_le_mul_right m (by decide)
  have h1 : 32 * m * w ≤ 64 * m * w := Nat.mul_le_mul_right w h0
  have h2 : 32 * m * w * (n / (64 * m * w)) ≤
      64 * m * w * (n / (64 * m * w)) :=
    Nat.mul_le_mul_right _ h1
  have h3 : 64 * m * w * (n / (64 * m * w)) =
      n / (64 * m * w) * (64 * m * w) := Nat.mul_comm _ _
  have h4 : n / (64 * m * w) * (64 * m * w) ≤ n :=
    Nat.div_mul_le_self n (64 * m * w)
  rw [h3] at h2
  exact Nat.le_trans h2 h4

private theorem regime_space_bound_tightEntry {m w n : Nat} :
    32 * m * w * (n / (32 * m * w)) ≤ n := by
  rw [Nat.mul_comm (32 * m * w) (n / (32 * m * w))]
  exact Nat.div_mul_le_self n (32 * m * w)

/-- The ratio coefficient `32` can also be used in the entry divisor; later
stages retain the geometric divisor `64*m`. -/
theorem geometric_regime_of_bound_tightEntry {m w n : Nat}
    (hm : 1 ≤ m) (hw : 1 ≤ w) (k : Nat)
    (hn : 2 * (64 * m) ^ k * (32 * m * w) ≤ n) :
    RegimeFrom m w n
      (geometricSchedule m (n / (32 * m * w)) (k + 1)) := by
  have hq : 0 < 32 * m * w :=
    Nat.mul_pos (Nat.mul_pos (by decide) hm) hw
  refine geometricSchedule_regime hm k (n / (32 * m * w)) n w hw ?_ ?_
  · rw [Nat.le_div_iff_mul_le hq]
    exact hn
  · exact regime_space_bound_tightEntry

/-- The former coefficient-`64` product is a sufficient coarse corollary of
the tighter entry condition. -/
theorem geometric_regime_of_bound_of_coarse {m w n : Nat}
    (hm : 1 ≤ m) (hw : 1 ≤ w) (k : Nat)
    (hn : 2 * (64 * m) ^ k * (64 * m * w) ≤ n) :
    RegimeFrom m w n
      (geometricSchedule m (n / (32 * m * w)) (k + 1)) := by
  apply geometric_regime_of_bound_tightEntry hm hw k
  exact Nat.le_trans (Nat.mul_le_mul_left (2 * (64 * m) ^ k)
    (Nat.mul_le_mul_right w (Nat.mul_le_mul_right m (by decide)))) hn

/-- One clean entry bound `2 * (64*m)^k * (64*m*w) <= n` puts the geometric
schedule with entry stars `n / (64*m*w)` inside the ratio regime over the
full `n`-variable space. -/
theorem geometric_regime_of_bound {m w n : Nat} (hm : 1 ≤ m) (hw : 1 ≤ w)
    (k : Nat) (hn : 2 * (64 * m) ^ k * (64 * m * w) ≤ n) :
    RegimeFrom m w n
      (geometricSchedule m (n / (64 * m * w)) (k + 1)) := by
  have hq : 0 < 64 * m * w :=
    Nat.mul_pos (Nat.mul_pos (by decide) hm) hw
  refine geometricSchedule_regime hm k (n / (64 * m * w)) n w hw ?_ ?_
  · rw [Nat.le_div_iff_mul_le hq]
    exact hn
  · exact regime_space_bound

open GeneratedRefinedIteratedCertificate in
/-- **Universal-layer asymptotic geometric family.**  EVERY supplied start
layer with `m >= 1` gates of width `<= w` (`w >= 1`) over `n` variables
admits the `(k+1)`-stage geometric-schedule certificate as soon as
`n >= 2 * (64*m)^k * (64*m*w)`: entry stars `n / (64*m*w)`, ALL stage
budgets `2`, every stage entering with width budget `>= 1` (no width-0
tail), and the constant tree-budget family `t(d,s) = m` preserved.  The
layer is universally quantified — only its gate count and width bound
enter the regime arithmetic.

Still NOT frozen-form B4 closure: the start layer is supplied (no
arbitrary layered decomposition of an AC0 formula is performed), realized
widths of re-viewed gates are budget claims, and the statement-vs-witness
caveat of `autoIteratedCollapse` applies unchanged.  NOT a Frege/PHP
proof-size bound, NOT a PHP switching lemma, NOT an NP/circuit lower
bound, NOT a statement about P vs NP. -/
theorem geometricFamilyCollapse_universal (k w : Nat) {n : Nat}
    (L : MinimalLayeredFormula n)
    (hm : 1 ≤ L.gates.length) (hw1 : 1 ≤ w)
    (hw : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w)
    (hn : 2 * (64 * L.gates.length) ^ k * (64 * L.gates.length * w) ≤ n) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        L.originalFormula (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) L.gates.length ∧
      cert.stageBudgets = List.replicate (k + 1) 2 ∧
      cert.stageStarCounts =
        (geometricSchedule L.gates.length
          (n / (64 * L.gates.length * w)) (k + 1)).map stageStars ∧
      TreeBudgetFrom (fun _ _ => L.gates.length) L.gates.length (k + 1)
        (geometricSchedule L.gates.length
          (n / (64 * L.gates.length * w)) (k + 1)) := by
  have hreg' : RegimeFrom L.gates.length w (stars (freeRestriction n))
      (geometricSchedule L.gates.length
        (n / (64 * L.gates.length * w)) (k + 1)) := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 k hn
  have hlen : (geometricSchedule L.gates.length
      (n / (64 * L.gates.length * w)) (k + 1)).length = k + 1 :=
    geometricSchedule_length L.gates.length (k + 1)
      (n / (64 * L.gates.length * w))
  have ht : TreeBudgetFrom (fun _ _ => L.gates.length) L.gates.length
      (geometricSchedule L.gates.length
        (n / (64 * L.gates.length * w)) (k + 1)).length
      (geometricSchedule L.gates.length
        (n / (64 * L.gates.length * w)) (k + 1)) :=
    geometricSchedule_treeBudget L.gates.length L.gates.length (k + 1)
      (n / (64 * L.gates.length * w))
      (geometricSchedule L.gates.length
        (n / (64 * L.gates.length * w)) (k + 1)).length
  have hex := autoIteratedCollapse_of_ratioRegime
    (fun _ _ => L.gates.length)
    (geometricSchedule L.gates.length
      (n / (64 * L.gates.length * w)) (k + 1))
    (freeRestriction n) L w hm hw hreg' ht
  rw [hlen, geometricSchedule_budgets] at hex
  exact hex

/-! ## A named two-gate witness family for the universal form -/

def pairLit0 (n : Nat) : Literal (n + 2) := ⟨⟨0, by omega⟩, true⟩
def pairLit1 (n : Nat) : Literal (n + 2) := ⟨⟨1, by omega⟩, true⟩

/-- First witness gate: single positive literal on variable `0`. -/
def pairGate0 (n : Nat) : GateSpec (n + 2) :=
  GateSpec.dnf (BDFormula.lit (pairLit0 n))
    { D := [[pairLit0 n]]
      sem_eq := by
        intro a
        simp [dnfEval, termEval, eval_lit]
      simple := by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm] }

/-- Second witness gate: single positive literal on variable `1`. -/
def pairGate1 (n : Nat) : GateSpec (n + 2) :=
  GateSpec.dnf (BDFormula.lit (pairLit1 n))
    { D := [[pairLit1 n]]
      sem_eq := by
        intro a
        simp [dnfEval, termEval, eval_lit]
      simple := by
        intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        simp [SimpleTerm] }

/-- The named two-gate start layer: two DISTINCT single-literal width-1
gates (variables `0` and `1`) under an `or` parent. -/
def pairLayer (n : Nat) : MinimalLayeredFormula (n + 2) :=
  { parent := ParentKind.or, gates := [pairGate0 n, pairGate1 n] }

theorem pairLayer_length (n : Nat) : (pairLayer n).gates.length = 2 := rfl

theorem pairLayer_width (n : Nat) :
    ∀ g ∈ (pairLayer n).gates, widthDNF g.theDNF ≤ 1 := by
  intro g hg
  have hg' : g = pairGate0 n ∨ g = pairGate1 n := by
    simpa [pairLayer] using hg
  rcases hg' with h | h
  · subst h
    show widthDNF [[pairLit0 n]] ≤ 1
    simp [widthDNF, termWidth]
  · subst h
    show widthDNF [[pairLit1 n]] ≤ 1
    simp [widthDNF, termWidth]

/-- Both witness gates have realized DNF width exactly `1`. -/
theorem pairGate0_width_realized (n : Nat) :
    widthDNF (pairGate0 n).theDNF = 1 := by
  show widthDNF [[pairLit0 n]] = 1
  simp [widthDNF, termWidth]

/-- Both witness gates have realized DNF width exactly `1`. -/
theorem pairGate1_width_realized (n : Nat) :
    widthDNF (pairGate1 n).theDNF = 1 := by
  show widthDNF [[pairLit1 n]] = 1
  simp [widthDNF, termWidth]

open GeneratedRefinedIteratedCertificate in
/-- The universal form instantiated on the two-gate layer at the exact
boundary `n = 32768 = 2 * 128 * 128`: two rounds, gate counts `[2, 2]`,
budgets `[2, 2]`, star counts `[256, 2]` — the multi-gate (`m = 2`) case
of the universal family is inhabited, with all stages entering at width
budget `>= 1` and both start gates of realized width `1`.  Single finite
instance of `geometricFamilyCollapse_universal`. -/
theorem geometricFamily_pair_twoStage :
    ∃ cert : GeneratedRefinedIteratedCertificate 32768
        (freeRestriction 32768) (pairLayer 32766).originalFormula 2,
      cert.stageGateCounts = [2, 2] ∧
      cert.stageBudgets = [2, 2] ∧
      cert.stageStarCounts = [256, 2] ∧
      TreeBudgetFrom (fun _ _ => 2) 2 2 (geometricSchedule 2 256 2) := by
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    geometricFamilyCollapse_universal 1 1 (pairLayer 32766)
      (by decide) (Nat.le_refl 1) (pairLayer_width 32766) (by decide)
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc]
    rfl
  · rw [hb]
    rfl
  · rw [hsc]
    rfl
  · exact ht

end FrozenProductScheduleRatio
end PvNP
