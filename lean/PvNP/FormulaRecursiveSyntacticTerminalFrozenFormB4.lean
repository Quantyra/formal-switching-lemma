import PvNP.FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute
import PvNP.FormulaRecursiveFrontierCountRecurrence

/-!
# Frozen-form B4 v1 class wrapper (S2181)

Class-quantified all-level uniform-9 iterated collapse for every nonempty-fanin
raw formula, with width and representative-count schedules synthesized from raw
syntax. The only free parameters are the merge parent, the round count, and a
single ambient product inequality against an explicit syntax-only Entry bound.

This is class-level iterated collapse for the restricted nonempty-fanin
normalized-view / dedup route only. It is not arbitrary AC⁰ collapse, not full
frozen-payload B4 beyond that class, not PHP switching, not Frege/PHP, not an
NP/circuit lower bound, not Gate A, and not P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalFrozenFormB4

open BoundedDepthFrege
open FormulaRecursiveDepth
open FormulaRecursiveFrontierCountRecurrence
open FormulaRecursiveLayerProfile
open FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget
open FormulaRecursiveSyntacticTerminalNormalizedViewRoute
open FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute
open FormulaTruthTableView
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-- Levelwise uniform-9 entry product from synthesized dedup count and
normalized-frontier width. -/
def levelEntryProduct9 {n : Nat} (F : BDFormula n) (level rounds : Nat) : Nat :=
  2 * (9 * (dedupRepresentativeFrontier F level).length) ^ rounds *
    (9 * (dedupRepresentativeFrontier F level).length *
      normalizedFrontierWidthSchedule F level)

/-- Coarse syntax-only ambient Entry: replaces every levelwise count/width by
`formulaSize F`, which upper-bounds dedup length and normalized width via the
S2166/S2164/S2180 chains. -/
def frozenFormEntryProduct9 {n : Nat} (F : BDFormula n) (rounds : Nat) : Nat :=
  2 * (9 * formulaSize F) ^ rounds * (9 * formulaSize F * formulaSize F)

theorem normalizedFrontierWidthSchedule_le_formulaSize {n : Nat}
    (F : BDFormula n) (level : Nat) :
    normalizedFrontierWidthSchedule F level ≤ formulaSize F :=
  Nat.le_trans (normalizedFrontierWidthSchedule_le_recurrenceWidthSchedule F level)
    (recurrenceWidthSchedule_le_formulaSize F level)

private theorem mul_le_mul_of_le_left_right {a b c d : Nat}
    (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d :=
  Nat.mul_le_mul hab hcd

theorem levelEntryProduct9_le_frozenFormEntryProduct9 {n : Nat}
    (F : BDFormula n) (level rounds : Nat) :
    levelEntryProduct9 F level rounds ≤ frozenFormEntryProduct9 F rounds := by
  let m := (dedupRepresentativeFrontier F level).length
  let W := normalizedFrontierWidthSchedule F level
  let Sz := formulaSize F
  have hm : m ≤ Sz := dedupRepresentativeFrontier_length_le_formulaSize F level
  have hw : W ≤ Sz := normalizedFrontierWidthSchedule_le_formulaSize F level
  have h9m : 9 * m ≤ 9 * Sz := Nat.mul_le_mul_left _ hm
  have hpow : (9 * m) ^ rounds ≤ (9 * Sz) ^ rounds := Nat.pow_le_pow_left h9m rounds
  have hmw : m * W ≤ Sz * Sz := mul_le_mul_of_le_left_right hm hw
  have htail : 9 * m * W ≤ 9 * Sz * Sz := by
    have : 9 * (m * W) ≤ 9 * (Sz * Sz) := Nat.mul_le_mul_left _ hmw
    simpa [Nat.mul_assoc] using this
  have hmid : (9 * m) ^ rounds * (9 * m * W) ≤ (9 * Sz) ^ rounds * (9 * Sz * Sz) :=
    mul_le_mul_of_le_left_right hpow htail
  have h2 : 2 * ((9 * m) ^ rounds * (9 * m * W)) ≤
      2 * ((9 * Sz) ^ rounds * (9 * Sz * Sz)) :=
    Nat.mul_le_mul_left 2 hmid
  change 2 * (9 * m) ^ rounds * (9 * m * W) ≤ 2 * (9 * Sz) ^ rounds * (9 * Sz * Sz)
  -- Left-associated products: 2 * a ^ r * b = (2 * a ^ r) * b.
  have hL :
      2 * (9 * m) ^ rounds * (9 * m * W) = 2 * ((9 * m) ^ rounds * (9 * m * W)) := by
    simp [Nat.mul_assoc]
  have hR :
      2 * (9 * Sz) ^ rounds * (9 * Sz * Sz) = 2 * ((9 * Sz) ^ rounds * (9 * Sz * Sz)) := by
    simp [Nat.mul_assoc]
  rw [hL, hR]
  exact h2

/-- Class-quantified all-level uniform-9 frozen-form wrapper: for every
nonempty-fanin formula, under a single ambient product against the syntax-only
Entry, every depth level carries the synthesized-dedup uniform-9 final-tree
payload. Schedules are fully synthesized; only merge parent, rounds, and ambient
remain free. -/
theorem frozenFormB4_v1_allLevels_uniform9 {n : Nat} (F : BDFormula n)
    (rounds : Nat) (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hn : frozenFormEntryProduct9 F rounds ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 F
        (fun _ => formulaSize F) (normalizedFrontierWidthSchedule F)
        (depth F) rounds parent level
        (dedupRepresentativeFrontier F level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    F (fun _ => formulaSize F) (depth F) rounds parent hNE
    (Nat.le_refl _) (Nat.le_refl _) ?_
  intro level _hk
  exact Nat.le_trans (levelEntryProduct9_le_frozenFormEntryProduct9 F level rounds) hn

/-- Packaging non-vacuity: the S2177 width-1 cube at ambient 1458 is an
instance of the class wrapper shape (S and d synthesized from the formula).
This is not switching non-vacuity and does not claim width≥2/count≥2. -/
theorem dupCubeWitness11_frozenFormB4_v1_rounds2 :
    ∀ level, level ≤ depth dupCubeWitness11 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 dupCubeWitness11
        (fun _ => formulaSize dupCubeWitness11)
        (normalizedFrontierWidthSchedule dupCubeWitness11)
        (depth dupCubeWitness11) 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness11 level) := by
  intro level hk
  have h := dupCubeWitness11_dedup_finalTree_allLevels_rounds2_uniform9 level hk
  have hSize : formulaSize dupCubeWitness11 = 15 := dupCubeWitness11_formulaSize
  have hDepth : depth dupCubeWitness11 = 3 := dupCubeWitness11_depth
  simpa [hSize, hDepth] using h

end FormulaRecursiveSyntacticTerminalFrozenFormB4
end PvNP
