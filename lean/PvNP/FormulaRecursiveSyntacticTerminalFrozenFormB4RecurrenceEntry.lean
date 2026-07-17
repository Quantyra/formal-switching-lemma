import PvNP.FormulaRecursiveSyntacticTerminalFrozenFormB4

/-!
# Frozen-form B4 recurrence Entry (S2183)

The S2181 class wrapper consumes the size-coarse Entry
`frozenFormEntryProduct9 = 2*(9*size)^r*(9*size*size)`. The S2180 count
recurrence bounds every frontier count hypothesis-free
(`frontierLayerGateCount ≤ formulaRecurrenceCount ≤ formulaSize`), so this
module threads the recurrence into the Entry's two **count** slots — the
**width** slot keeps `formulaSize`, since widths are bounded by the width
chain, not the count recurrence:

* `frozenFormEntryProduct9Rec F rounds = 2*(9*rc)^rounds*(9*rc*size)` with
  `rc = formulaRecurrenceCount F`;
* hypothesis-free pointwise chain `levelEntryProduct9 ≤
  frozenFormEntryProduct9Rec ≤ frozenFormEntryProduct9` for every raw
  formula, level, and round count;
* class wrapper `frozenFormB4_v1_allLevels_uniform9_recEntry`: same
  conclusion as the S2181 wrapper under a never-larger Entry bound — the
  ambient hypothesis is never harder to meet, and is strictly easier at the
  pinned witness;
* witness `twinCubeWitnessRec9 : BDFormula 11197440` (the S2182 twin-cube
  shape) with `formulaRecurrenceCount = 8 < 15 = formulaSize`: the
  recurrence Entry `2*(9*8)^2*(9*8*15) = 11197440` is met with equality
  through the new wrapper's hypothesis, while the size-coarse Entry
  (`73811250`) **fails** at this ambient — a same-witness strict separation.

Entry-bound bookkeeping over the existing class wrapper only: a tighter
sufficient ambient condition for the same conclusion, with no change to the
certificate payload and no new switching mathematics. This is not switching
non-vacuity, not full B4 beyond the nonempty-fanin normalized-view/dedup
class, not arbitrary AC⁰ collapse, not PHP switching, not a Frege/PHP or
NP/circuit lower bound, not Gate A, and not P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalFrozenFormB4RecurrenceEntry

open BoundedDepthFrege
open FormulaRecursiveDepth
open FormulaRecursiveFrontierCountRecurrence
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSyntacticTerminalNormalizedViewRoute
open FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute
open FormulaRecursiveSyntacticTerminalFrozenFormB4
open FormulaTruthTableView
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-- Recurrence-count ambient Entry: the count slots use the hypothesis-free
S2180 recurrence bound; the width slot keeps `formulaSize`. -/
def frozenFormEntryProduct9Rec {n : Nat} (F : BDFormula n) (rounds : Nat) : Nat :=
  2 * (9 * formulaRecurrenceCount F) ^ rounds *
    (9 * formulaRecurrenceCount F * formulaSize F)

/-- Synthesized dedup counts obey the S2180 recurrence bound with zero
hypotheses: dedup length ≤ raw frontier gate count ≤ recurrence. -/
theorem dedupRepresentativeFrontier_length_le_formulaRecurrenceCount {n : Nat}
    (F : BDFormula n) (level : Nat) :
    (dedupRepresentativeFrontier F level).length ≤ formulaRecurrenceCount F :=
  Nat.le_trans
    (dedupRepresentativeFrontier_length_le_frontierGateCount F level)
    (frontierLayerGateCount_le_formulaRecurrenceCount F level)

private theorem mul_le_mul_of_le_left_right {a b c d : Nat}
    (hab : a ≤ b) (hcd : c ≤ d) : a * c ≤ b * d :=
  Nat.mul_le_mul hab hcd

private theorem entry_product_mono {m W rc Sz : Nat} (rounds : Nat)
    (hm : m ≤ rc) (hw : W ≤ Sz) :
    2 * (9 * m) ^ rounds * (9 * m * W) ≤ 2 * (9 * rc) ^ rounds * (9 * rc * Sz) := by
  have h9m : 9 * m ≤ 9 * rc := Nat.mul_le_mul_left _ hm
  have hpow : (9 * m) ^ rounds ≤ (9 * rc) ^ rounds := Nat.pow_le_pow_left h9m rounds
  have hmw : m * W ≤ rc * Sz := mul_le_mul_of_le_left_right hm hw
  have htail : 9 * m * W ≤ 9 * rc * Sz := by
    have : 9 * (m * W) ≤ 9 * (rc * Sz) := Nat.mul_le_mul_left _ hmw
    simpa [Nat.mul_assoc] using this
  have hmid : (9 * m) ^ rounds * (9 * m * W) ≤ (9 * rc) ^ rounds * (9 * rc * Sz) :=
    mul_le_mul_of_le_left_right hpow htail
  have h2 : 2 * ((9 * m) ^ rounds * (9 * m * W)) ≤
      2 * ((9 * rc) ^ rounds * (9 * rc * Sz)) :=
    Nat.mul_le_mul_left 2 hmid
  have hL : 2 * (9 * m) ^ rounds * (9 * m * W) =
      2 * ((9 * m) ^ rounds * (9 * m * W)) := by
    simp [Nat.mul_assoc]
  have hR : 2 * (9 * rc) ^ rounds * (9 * rc * Sz) =
      2 * ((9 * rc) ^ rounds * (9 * rc * Sz)) := by
    simp [Nat.mul_assoc]
  rw [hL, hR]
  exact h2

/-- Every levelwise entry product is bounded by the recurrence Entry, with
zero hypotheses on the formula. -/
theorem levelEntryProduct9_le_frozenFormEntryProduct9Rec {n : Nat}
    (F : BDFormula n) (level rounds : Nat) :
    levelEntryProduct9 F level rounds ≤ frozenFormEntryProduct9Rec F rounds :=
  entry_product_mono rounds
    (dedupRepresentativeFrontier_length_le_formulaRecurrenceCount F level)
    (normalizedFrontierWidthSchedule_le_formulaSize F level)

/-- The recurrence Entry never exceeds the size-coarse S2181 Entry. -/
theorem frozenFormEntryProduct9Rec_le_frozenFormEntryProduct9 {n : Nat}
    (F : BDFormula n) (rounds : Nat) :
    frozenFormEntryProduct9Rec F rounds ≤ frozenFormEntryProduct9 F rounds :=
  entry_product_mono rounds (formulaRecurrenceCount_le_formulaSize F)
    (Nat.le_refl _)

/-- Class-quantified all-level uniform-9 frozen-form wrapper under the
recurrence Entry: same conclusion as the S2181 wrapper; the recurrence Entry
never exceeds the size-coarse Entry, so the ambient hypothesis is never
harder to meet (and is strictly easier at the pinned witness). -/
theorem frozenFormB4_v1_allLevels_uniform9_recEntry {n : Nat} (F : BDFormula n)
    (rounds : Nat) (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hn : frozenFormEntryProduct9Rec F rounds ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 F
        (fun _ => formulaSize F) (normalizedFrontierWidthSchedule F)
        (depth F) rounds parent level
        (dedupRepresentativeFrontier F level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    F (fun _ => formulaSize F) (depth F) rounds parent hNE
    (Nat.le_refl _) (Nat.le_refl _) ?_
  intro level _hk
  exact Nat.le_trans
    (levelEntryProduct9_le_frozenFormEntryProduct9Rec F level rounds) hn

/-! ## Same-witness strict separation at the recurrence-Entry ambient -/

private def twinCubeInnerARec9 : BDFormula 11197440 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨1, by decide⟩, sign := true }]

private def twinCubeInnerBRec9 : BDFormula 11197440 :=
  .and [.lit { var := ⟨1, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def twinCubeMidRec9 : BDFormula 11197440 :=
  .and [twinCubeInnerARec9, twinCubeInnerBRec9]

/-- The S2182 twin-cube shape at the recurrence-Entry ambient
`11197440 = 2*(9*8)^2*(9*8*15)`: the recurrence count `8` (the S2180
per-layer frontier bound, which charges leaf mass only — `max 1 (sum)`
absorbs gate nodes) is strictly smaller than the size `15` (8 leaves + 7
gates), so the recurrence Entry sits strictly below the size-coarse Entry at
this witness. The shape is retained from S2182 for schedule continuity. -/
def twinCubeWitnessRec9 : BDFormula 11197440 :=
  .and [twinCubeMidRec9, twinCubeMidRec9]

private theorem twinCubeInnerARec9_nonempty :
    NonemptyFaninFormula twinCubeInnerARec9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeInnerARec9] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem twinCubeInnerBRec9_nonempty :
    NonemptyFaninFormula twinCubeInnerBRec9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeInnerBRec9] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem twinCubeMidRec9_nonempty :
    NonemptyFaninFormula twinCubeMidRec9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeMidRec9] at hG
  rcases hG with rfl | rfl
  · exact twinCubeInnerARec9_nonempty
  · exact twinCubeInnerBRec9_nonempty

theorem twinCubeWitnessRec9_nonemptyFanin :
    NonemptyFaninFormula twinCubeWitnessRec9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeWitnessRec9] at hG
  subst hG
  exact twinCubeMidRec9_nonempty

theorem twinCubeWitnessRec9_formulaSize :
    formulaSize twinCubeWitnessRec9 = 15 := by
  simp [twinCubeWitnessRec9, twinCubeMidRec9, twinCubeInnerARec9,
    twinCubeInnerBRec9, formulaSize_and, formulaSize_lit]

theorem twinCubeWitnessRec9_depth : depth twinCubeWitnessRec9 = 3 := by
  simp [twinCubeWitnessRec9, twinCubeMidRec9, twinCubeInnerARec9,
    twinCubeInnerBRec9, depth]

/-- The duplicated-subformula witness has recurrence count `8`. -/
theorem twinCubeWitnessRec9_recurrenceCount :
    formulaRecurrenceCount twinCubeWitnessRec9 = 8 := by
  simp [twinCubeWitnessRec9, twinCubeMidRec9, twinCubeInnerARec9,
    twinCubeInnerBRec9, formulaRecurrenceCount_and, formulaRecurrenceCount_lit]

/-- The recurrence count is strictly below the size at this witness. -/
theorem twinCubeWitnessRec9_recurrenceCount_lt_formulaSize :
    formulaRecurrenceCount twinCubeWitnessRec9 <
      formulaSize twinCubeWitnessRec9 := by
  simp only [twinCubeWitnessRec9_recurrenceCount,
    twinCubeWitnessRec9_formulaSize]
  decide

/-- The recurrence Entry is met with **equality** at this ambient:
`2*(9*8)^2*(9*8*15) = 11197440`. -/
theorem twinCubeWitnessRec9_recEntry_eq :
    frozenFormEntryProduct9Rec twinCubeWitnessRec9 2 = 11197440 := by
  unfold frozenFormEntryProduct9Rec
  simp only [twinCubeWitnessRec9_recurrenceCount, twinCubeWitnessRec9_formulaSize]
  decide

/-- Same-witness strict separation: the size-coarse S2181 Entry
(`2*(9*15)^2*(9*15*15) = 73811250`) fails at the recurrence-Entry ambient.
Entry-hypothesis failure only — no claim that the certificate conclusion
fails at this ambient. -/
theorem twinCubeWitnessRec9_sizeEntry_fails :
    ¬ (frozenFormEntryProduct9 twinCubeWitnessRec9 2 ≤ 11197440) := by
  unfold frozenFormEntryProduct9
  simp only [twinCubeWitnessRec9_formulaSize]
  decide

/-- Through-the-hypothesis instantiation of the recurrence-Entry wrapper at
the exact recurrence ambient. -/
theorem twinCubeWitnessRec9_frozenFormB4_v1_via_recEntry :
    ∀ level, level ≤ depth twinCubeWitnessRec9 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9
        twinCubeWitnessRec9
        (fun _ => formulaSize twinCubeWitnessRec9)
        (normalizedFrontierWidthSchedule twinCubeWitnessRec9)
        (depth twinCubeWitnessRec9) 2 ParentKind.and level
        (dedupRepresentativeFrontier twinCubeWitnessRec9 level) :=
  frozenFormB4_v1_allLevels_uniform9_recEntry twinCubeWitnessRec9 2
    ParentKind.and twinCubeWitnessRec9_nonemptyFanin
    (Nat.le_of_eq twinCubeWitnessRec9_recEntry_eq)

end FormulaRecursiveSyntacticTerminalFrozenFormB4RecurrenceEntry
end PvNP
