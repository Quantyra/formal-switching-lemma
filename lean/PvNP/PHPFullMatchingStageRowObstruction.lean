import PvNP.PHPFullMatchingStageRows

/-!
# Stage-row nonemptiness and duplicate-stage obstruction

This additive S2123 module records the safe lower bound currently available for
stage-indexed recovered rows, and a tiny duplicate-stage witness showing why a
global two-distinct-row lower bound is false for all `BadPathCode`s under the
current definition.

All statements are finite code-space/matching-space infrastructure only.  No
distinct-row theorem, no `q = t` coarsening, no geometric decay bound, and no PHP
switching lemma is proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingStageRowObstruction

open CNFModel
open RestrictedPHPFloor
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingStageRows

/-! ## Safe one-row facts -/

/-- A positive-length bad-path code recovers at least one stage row. -/
theorem codeStageRows_nonempty {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (ht : 1 <= t) (c : BadPathCode h tvs t) :
    (codeStageRows c).Nonempty := by
  have hk : 0 < t := ht
  exact ⟨codeStageRow c ⟨0, hk⟩,
    (mem_codeStageRows c (codeStageRow c ⟨0, hk⟩)).mpr ⟨⟨0, hk⟩, rfl⟩⟩

/-- Cardinal form of `codeStageRows_nonempty`. -/
theorem one_le_codeStageRows_card {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (ht : 1 <= t) (c : BadPathCode h tvs t) :
    1 <= (codeStageRows c).card := by
  exact Finset.card_pos.mpr (codeStageRows_nonempty ht c)

/-- If the stage-row map is injective, then all `t` stages recover distinct rows. -/
theorem codeStageRows_card_eq_of_injective {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t)
    (hinj : Function.Injective (codeStageRow c)) :
    (codeStageRows c).card = t := by
  classical
  unfold codeStageRows
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## Tiny duplicate-stage obstruction -/

/-- A one-row, one-literal DNF support used by the duplicate-stage witness. -/
def duplicateStageTvs_h1 : List (List (Fin 1 × Fin 1 × Bool)) :=
  [[((0 : Fin 1), (0 : Fin 1), true)]]

/-- A length-two code that records the same certified PHP variable at both stages. -/
def duplicateStageCode_h1_t2 : BadPathCode 1 duplicateStageTvs_h1 2 :=
  fun _ => (⟨phpVar 1 1 0 0, by decide⟩, true)

/-- In the `h = 1`, `t = 2` duplicate-stage code, only one row is recovered. -/
theorem duplicateStageCode_h1_t2_codeStageRows_card :
    (codeStageRows duplicateStageCode_h1_t2).card = 1 := by
  apply Nat.le_antisymm
  · calc
      (codeStageRows duplicateStageCode_h1_t2).card
          <= (Finset.univ : Finset (Fin 1)).card :=
            Finset.card_le_card (Finset.subset_univ _)
      _ = 1 := by simp
  · exact one_le_codeStageRows_card (h := 1) (t := 2) (tvs := duplicateStageTvs_h1)
      (by decide) duplicateStageCode_h1_t2

/-- The duplicate-stage witness refutes a two-row lower bound for this code. -/
theorem not_two_le_duplicateStageCode_h1_t2_codeStageRows_card :
    ¬ 2 <= (codeStageRows duplicateStageCode_h1_t2).card := by
  rw [duplicateStageCode_h1_t2_codeStageRows_card]
  decide

/-- Therefore not every code over this tiny support recovers at least two rows. -/
theorem not_forall_two_le_codeStageRows_card_duplicateStageTvs_h1_t2 :
    ¬ (∀ c : BadPathCode 1 duplicateStageTvs_h1 2, 2 <= (codeStageRows c).card) := by
  intro hforall
  exact not_two_le_duplicateStageCode_h1_t2_codeStageRows_card
    (hforall duplicateStageCode_h1_t2)

end PHPFullMatchingStageRowObstruction
end PvNP
