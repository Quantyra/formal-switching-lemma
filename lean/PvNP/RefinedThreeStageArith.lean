import PvNP.RestrictionComposition

/-!
# Counting arithmetic for the concrete three-stage instance

The symbolic choose-ratio facts and per-stage counting beats consumed by
`PvNP.RefinedThreeStageInstance`.  Splitting them into their own module keeps
each elaboration run small and checkpoints the proved arithmetic as a built
artifact.

The two-step choose-ratio lemma is proved ONCE with abstract parameters
(`choose_ratio_two_step`), so the kernel never has to re-check symbolic
manipulation of `Nat.choose` at large literals; each concrete instance only
discharges a small literal-arithmetic side condition by kernel `decide`.

These are plain finite counting inequalities over `Nat.choose` and
`restrictionsWithStars` cardinalities.  They carry no collapse, lower-bound,
or P-vs-NP content on their own.

REVISION DISCLOSURE (2026-07-04, on resuming the parked S2075 material):
the originally stashed (never-verified) proofs of `stage1_beat`,
`stage2_plain_beat`, and `stage2_refined_beat_base306` were replaced.
The stashed `stage2_refined_beat_base306` attempted kernel `decide` on a
goal containing `Nat.choose 306 15` (unmemoized Pascal recursion — not
feasible), and the stashed `stage1_beat`/`stage2_plain_beat` used
metavariable-pattern rewrites (`Nat.mul_assoc`, `← pow_add`) on goals
containing `Nat.choose 5193 304` — the choose-literal defeq hazard
documented in `ScheduledCollapseDemo`.  All three now go through the fully
symbolic `beat_from_ratio` assembly (every rewrite meets only variables)
plus closed-pattern numeral pre-normalization, instantiated by `exact`.
The migrated factor-4 inequalities are weaker than their original factor-8
forms and are discharged from the same symbolic ratio bounds.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RefinedThreeStageInstance

set_option maxRecDepth 8192
set_option exponentiation.threshold 6000

attribute [local irreducible] SwitchingLemmaStatement.restrictionsWithStars

open SwitchingLemmaStatement
open RestrictionComposition

/-! ## Symbolic choose-ratio arithmetic -/

/-- Generic two-step choose-ratio fact: if the descent products beat the
factor `256`, then `256 · C(n, k) < C(n, k + 2)`.  Proved with abstract `n`,
`k` so instances at large literals cost the kernel only a literal-arithmetic
`decide`. -/
theorem choose_ratio_two_step (n k : Nat) (hk : k + 2 ≤ n)
    (hbeat : 256 * ((k + 2) * (k + 1)) < (n - (k + 1)) * (n - k)) :
    256 * Nat.choose n k < Nat.choose n (k + 2) := by
  have h1' : Nat.choose n k * (n - k) = Nat.choose n (k + 1) * (k + 1) :=
    (Nat.choose_succ_right_eq n k).symm
  have h2' : Nat.choose n (k + 1) * (n - (k + 1)) =
      Nat.choose n (k + 2) * (k + 2) :=
    (Nat.choose_succ_right_eq n (k + 1)).symm
  have hpos : 0 < Nat.choose n k := Nat.choose_pos (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := (k + 2) * (k + 1))
  calc
    (256 * Nat.choose n k) * ((k + 2) * (k + 1))
        = Nat.choose n k * (256 * ((k + 2) * (k + 1))) := by ac_rfl
    _ < Nat.choose n k * ((n - (k + 1)) * (n - k)) :=
        Nat.mul_lt_mul_of_pos_left hbeat hpos
    _ = (Nat.choose n k * (n - k)) * (n - (k + 1)) := by ac_rfl
    _ = (Nat.choose n (k + 1) * (k + 1)) * (n - (k + 1)) := by rw [h1']
    _ = (Nat.choose n (k + 1) * (n - (k + 1))) * (k + 1) := by ac_rfl
    _ = (Nat.choose n (k + 2) * (k + 2)) * (k + 1) := by rw [h2']
    _ = Nat.choose n (k + 2) * ((k + 2) * (k + 1)) := by ac_rfl

/-- `256 · C(5193, 304) < C(5193, 306)`: the stage-1 ratio at the full
`n = 5193` star space (the beat is razor-thin: `23892480 < 23897432`). -/
theorem choose5193_ratio_306 :
    256 * Nat.choose 5193 304 < Nat.choose 5193 306 :=
  choose_ratio_two_step 5193 304 (by decide) (by decide)

/-- `256 · C(5193, 15) < C(5193, 17)`: the stage-2 plain-space ratio. -/
theorem choose5193_ratio_17 :
    256 * Nat.choose 5193 15 < Nat.choose 5193 17 :=
  choose_ratio_two_step 5193 15 (by decide) (by decide)

/-- `256 · C(306, 15) < C(306, 17)`: the stage-2 renormalized ratio over the
306-star base. -/
theorem choose306_ratio :
    256 * Nat.choose 306 15 < Nat.choose 306 17 :=
  choose_ratio_two_step 306 15 (by decide) (by decide)

/-! ## Counting beats -/

/-- Symbolic beat assembly: every rewrite in this lemma meets only
variables, so the choose-literal defeq hazard (see `ScheduledCollapseDemo`)
cannot arise when it is instantiated at large literals by `exact`. -/
private theorem beat_from_ratio {A B x y d e K : Nat}
    (hx : x = y + d) (hK : e * 2 ^ d = K) (hr : K * A < B) :
    1 * (A * 2 ^ x * e) < B * 2 ^ y := by
  subst hx
  rw [Nat.one_mul, Nat.pow_add]
  have hE : A * (2 ^ y * 2 ^ d) * e = e * 2 ^ d * A * 2 ^ y := by
    simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hE, hK]
  exact Nat.mul_lt_mul_of_lt_of_le hr (Nat.le_refl _)
    (Nat.pos_pow_of_pos _ (by decide))

theorem stage1_beat :
    1 * ((restrictionsWithStars 5193 (306 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 5193 306).card := by
  rw [restrictionsWithStars_card, restrictionsWithStars_card]
  rw [show (306 - 2 : Nat) = 304 from rfl]
  exact beat_from_ratio (d := 2) (K := 64) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : (64 : Nat) ≤ 256))
      choose5193_ratio_306)

theorem stage2_plain_beat :
    1 * ((restrictionsWithStars 5193 (17 - 2)).card * (4 * 1) ^ 2) <
      (restrictionsWithStars 5193 17).card := by
  rw [restrictionsWithStars_card, restrictionsWithStars_card]
  rw [show (17 - 2 : Nat) = 15 from rfl]
  exact beat_from_ratio (d := 2) (K := 64) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : (64 : Nat) ≤ 256))
      choose5193_ratio_17)

theorem stage2_refined_beat_base306 :
    1 * ((restrictionsWithStars 306 (17 - 2)).card * (4 * 1) ^ 2) <
      (Nat.choose 306 17 * 2 ^ (306 - 17)) := by
  rw [restrictionsWithStars_card]
  rw [show (17 - 2 : Nat) = 15 from rfl]
  exact beat_from_ratio (d := 2) (K := 64) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by decide : (64 : Nat) ≤ 256))
      choose306_ratio)

theorem stage3_refined_beat_base17 :
    1 * ((restrictionsWithStars 17 (1 - 1)).card * (4 * 1) ^ 1) <
      (Nat.choose 17 1 * 2 ^ (17 - 1)) := by
  rw [restrictionsWithStars_card]
  decide

theorem stage3_plain_beat :
    1 * ((restrictionsWithStars 5193 (1 - 1)).card * (4 * 1) ^ 1) <
      (restrictionsWithStars 5193 1).card := by
  rw [restrictionsWithStars_card, restrictionsWithStars_card]
  rw [show (1 - 1 : Nat) = 0 from rfl, Nat.choose_zero_right,
    Nat.choose_one_right]
  decide

end RefinedThreeStageInstance
end PvNP
