import PvNP.FormulaRecursiveSyntacticTerminalFrozenFormB4

/-!
# Frozen-form B4 strong structural non-vacuity witness (S2182)

Every coefficient-lane packaging witness so far (`dupCubeWitness11/13/14`,
`dupCubeWitnessU9R3/R4`) is a duplicated width-1 cube: its synthesized dedup
representative count and normalized frontier width are both `1` at every level.
This module pins a witness whose synthesized schedules are non-degenerate at
the level that actually pins the ambient:

* `twinCubeWitness9 : BDFormula 23328` has dedup counts `1, 1, 2, 2` and
  normalized widths `2, 2, 2, 1` across its levels `0..3`;
* level `2` is the unique **binding** level: its rounds-2 uniform-9 entry
  product equals the ambient `23328 = 2*(9*2)^2*(9*2*2)`, and at ambient
  `23327` level `2` fails while levels `0`, `1`, `3` still hold;
* at that binding level both the count and the width are `≥ 2`, welded to
  the kernel-checked `levelEntryProduct9` binding facts, and
  `dupCubeWitness11` admits no such level (kernel-checked contrast);
* `twinCubeWitnessEntry9 : BDFormula 73811250` passes through the S2181
  wrapper `frozenFormB4_v1_allLevels_uniform9` **via its coarse Entry
  hypothesis** `frozenFormEntryProduct9 = 2*(9*15)^2*(9*15*15) = 73811250`,
  the first through-the-hypothesis instantiation of the wrapper.

This is structural/packaging non-vacuity of the synthesized schedules only.
It is not switching non-vacuity, not full B4 beyond the nonempty-fanin
normalized-view/dedup class, not arbitrary AC⁰ collapse, not PHP switching,
not a Frege/PHP or NP/circuit lower bound, not Gate A, and not P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalFrozenFormB4StrongWitness

open BoundedDepthFrege
open FormulaRecursiveDepth
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticTerminalNormalizedViewRoute
open FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute
open FormulaRecursiveSyntacticTerminalFrozenFormB4
open FormulaSyntacticDNF
open FormulaSyntacticDNFNormalization
open FormulaTruthTableView
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction

/-! ## The strong witness at the binding-tight ambient `23328` -/

private def twinCubeInnerA9 : BDFormula 23328 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨1, by decide⟩, sign := true }]

private def twinCubeInnerB9 : BDFormula 23328 :=
  .and [.lit { var := ⟨1, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def twinCubeMid9 : BDFormula 23328 :=
  .and [twinCubeInnerA9, twinCubeInnerB9]

/-- Two syntactically distinct width-2 cubes under a duplicated conjunction:
size 15 and depth 3, the same envelope as `dupCubeWitness11`, but with
non-degenerate synthesized schedules. The two inner cubes are semantically
equal (child-order swap): the level-2 count of 2 is a property of the
syntactic dedup schedule, which is exactly what the wrapper consumes. -/
def twinCubeWitness9 : BDFormula 23328 :=
  .and [twinCubeMid9, twinCubeMid9]

private theorem twinCubeInnerA9_nonempty : NonemptyFaninFormula twinCubeInnerA9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeInnerA9] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem twinCubeInnerB9_nonempty : NonemptyFaninFormula twinCubeInnerB9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeInnerB9] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem twinCubeMid9_nonempty : NonemptyFaninFormula twinCubeMid9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeMid9] at hG
  rcases hG with rfl | rfl
  · exact twinCubeInnerA9_nonempty
  · exact twinCubeInnerB9_nonempty

theorem twinCubeWitness9_nonemptyFanin : NonemptyFaninFormula twinCubeWitness9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeWitness9] at hG
  subst hG
  exact twinCubeMid9_nonempty

theorem twinCubeWitness9_formulaSize : formulaSize twinCubeWitness9 = 15 := by
  simp [twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9,
    formulaSize_and, formulaSize_lit]

theorem twinCubeWitness9_depth : depth twinCubeWitness9 = 3 := by
  simp [twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9, depth]

/-! ## Per-level synthesized schedule pins

Levels `0..3`: dedup representative counts `1, 1, 2, 2`; normalized frontier
widths `2, 2, 2, 1`. Every value is closed by definitional evaluation. -/

theorem twinCubeWitness9_dedupLength_zero :
    (dedupRepresentativeFrontier twinCubeWitness9 0).length = 1 := by
  simp [dedupRepresentativeFrontier, formulaDepthFrontier, depthFrontier,
    topChildren, List.dedup_cons_of_mem, List.dedup_cons_of_not_mem,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_dedupLength_one :
    (dedupRepresentativeFrontier twinCubeWitness9 1).length = 1 := by
  simp [dedupRepresentativeFrontier, formulaDepthFrontier, depthFrontier,
    topChildren, List.dedup_cons_of_mem, List.dedup_cons_of_not_mem,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_dedupLength_two :
    (dedupRepresentativeFrontier twinCubeWitness9 2).length = 2 := by
  simp [dedupRepresentativeFrontier, formulaDepthFrontier, depthFrontier,
    topChildren, List.dedup_cons_of_mem, List.dedup_cons_of_not_mem,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_dedupLength_three :
    (dedupRepresentativeFrontier twinCubeWitness9 3).length = 2 := by
  simp [dedupRepresentativeFrontier, formulaDepthFrontier, depthFrontier,
    topChildren, List.dedup_cons_of_mem, List.dedup_cons_of_not_mem,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_width_zero :
    normalizedFrontierWidthSchedule twinCubeWitness9 0 = 2 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    normalizedDNFView_D, normalizeDNF, dedupTerm, termContradictoryB,
    CNFModel.literalComplementary, List.dedup_cons_of_mem,
    List.dedup_cons_of_not_mem, syntacticDNF, syntacticAndDNF, andDNF,
    FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
    SwitchingLemmaStatement.widthDNF, SwitchingLemmaStatement.termWidth,
    formulaDepthFrontier, depthFrontier, topChildren,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_width_one :
    normalizedFrontierWidthSchedule twinCubeWitness9 1 = 2 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    normalizedDNFView_D, normalizeDNF, dedupTerm, termContradictoryB,
    CNFModel.literalComplementary, List.dedup_cons_of_mem,
    List.dedup_cons_of_not_mem, syntacticDNF, syntacticAndDNF, andDNF,
    FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
    SwitchingLemmaStatement.widthDNF, SwitchingLemmaStatement.termWidth,
    formulaDepthFrontier, depthFrontier, topChildren,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_width_two :
    normalizedFrontierWidthSchedule twinCubeWitness9 2 = 2 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    normalizedDNFView_D, normalizeDNF, dedupTerm, termContradictoryB,
    CNFModel.literalComplementary, List.dedup_cons_of_mem,
    List.dedup_cons_of_not_mem, syntacticDNF, syntacticAndDNF, andDNF,
    FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
    SwitchingLemmaStatement.widthDNF, SwitchingLemmaStatement.termWidth,
    formulaDepthFrontier, depthFrontier, topChildren,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

theorem twinCubeWitness9_width_three :
    normalizedFrontierWidthSchedule twinCubeWitness9 3 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    normalizedDNFView_D, normalizeDNF, dedupTerm, termContradictoryB,
    CNFModel.literalComplementary, List.dedup_cons_of_mem,
    List.dedup_cons_of_not_mem, syntacticDNF, syntacticAndDNF, andDNF,
    FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
    SwitchingLemmaStatement.widthDNF, SwitchingLemmaStatement.termWidth,
    formulaDepthFrontier, depthFrontier, topChildren,
    twinCubeWitness9, twinCubeMid9, twinCubeInnerA9, twinCubeInnerB9]

/-! ## Binding-level pins

The level-2 rounds-2 product equals the ambient exactly; every other level is
strictly below, and at ambient `23327` only level 2 breaks. -/

theorem twinCubeWitness9_uniform9_product_level2_eq :
    2 * (9 * 2) ^ 2 * (9 * 2 * 2) = 23328 := by decide

/-- The S2181 levelwise entry product of the witness at the strong level
equals the ambient exactly. -/
theorem twinCubeWitness9_levelEntryProduct9_level2_eq :
    levelEntryProduct9 twinCubeWitness9 2 2 = 23328 := by
  unfold levelEntryProduct9
  simp only [twinCubeWitness9_dedupLength_two, twinCubeWitness9_width_two]
  decide

/-- At ambient `23327` the witness's level-2 entry product fails. -/
theorem twinCubeWitness9_levelEntryProduct9_level2_fails_below :
    ¬ (levelEntryProduct9 twinCubeWitness9 2 2 ≤ 23327) := by
  rw [twinCubeWitness9_levelEntryProduct9_level2_eq]
  decide

/-- At ambient `23327` the witness's level-0 entry product still holds. -/
theorem twinCubeWitness9_levelEntryProduct9_level0_holds_below :
    levelEntryProduct9 twinCubeWitness9 0 2 ≤ 23327 := by
  unfold levelEntryProduct9
  simp only [twinCubeWitness9_dedupLength_zero, twinCubeWitness9_width_zero]
  decide

/-- At ambient `23327` the witness's level-1 entry product still holds. -/
theorem twinCubeWitness9_levelEntryProduct9_level1_holds_below :
    levelEntryProduct9 twinCubeWitness9 1 2 ≤ 23327 := by
  unfold levelEntryProduct9
  simp only [twinCubeWitness9_dedupLength_one, twinCubeWitness9_width_one]
  decide

/-- At ambient `23327` the witness's level-3 entry product still holds. -/
theorem twinCubeWitness9_levelEntryProduct9_level3_holds_below :
    levelEntryProduct9 twinCubeWitness9 3 2 ≤ 23327 := by
  unfold levelEntryProduct9
  simp only [twinCubeWitness9_dedupLength_three, twinCubeWitness9_width_three]
  decide

/-- Strong structural non-vacuity at the binding level, welded at the kernel:
the synthesized dedup count and the synthesized normalized width are both at
least `2` at level 2, **and** level 2's levelwise entry product equals the
ambient `23328`. This is structural/packaging non-vacuity of the synthesized
schedules only, not switching non-vacuity. -/
theorem twinCubeWitness9_strong_nonvacuity_at_binding_level :
    2 ≤ (dedupRepresentativeFrontier twinCubeWitness9 2).length ∧
      2 ≤ normalizedFrontierWidthSchedule twinCubeWitness9 2 ∧
      levelEntryProduct9 twinCubeWitness9 2 2 = 23328 := by
  refine ⟨?_, ?_, twinCubeWitness9_levelEntryProduct9_level2_eq⟩
  · simp only [twinCubeWitness9_dedupLength_two]
    decide
  · simp only [twinCubeWitness9_width_two]
    decide

/-- Positive existential mirror of the contrast lemma: the witness has a level
within its depth with both synthesized count and width at least `2`. -/
theorem twinCubeWitness9_exists_strong_level :
    ∃ level, level ≤ depth twinCubeWitness9 ∧
      2 ≤ (dedupRepresentativeFrontier twinCubeWitness9 level).length ∧
      2 ≤ normalizedFrontierWidthSchedule twinCubeWitness9 level := by
  refine ⟨2, ?_, ?_, ?_⟩
  · rw [twinCubeWitness9_depth]
    omega
  · simp only [twinCubeWitness9_dedupLength_two]
    decide
  · simp only [twinCubeWitness9_width_two]
    decide

/-- Kernel-checked contrast: the S2177 packaging witness `dupCubeWitness11`
admits **no** level with both synthesized count and width at least 2. The
same degeneracy holds for the other coefficient-lane packaging witnesses via
their per-level count/width = 1 lemmas in the frontier-route module; the
`¬∃`-form contrast is kernel-checked here for `dupCubeWitness11`. -/
theorem dupCubeWitness11_no_strong_level :
    ¬ ∃ level, level ≤ depth dupCubeWitness11 ∧
      2 ≤ (dedupRepresentativeFrontier dupCubeWitness11 level).length ∧
      2 ≤ normalizedFrontierWidthSchedule dupCubeWitness11 level := by
  rintro ⟨level, hlevel, hcount, -⟩
  rw [dupCubeWitness11_dedupFrontier_length level hlevel] at hcount
  omega

/-! ## The all-level certificate at the exact binding ambient -/

/-- All-level rounds-2 uniform-9 final-tree certificate for the strong witness
at the exact binding ambient `23328`, in the S2181 wrapper conclusion shape
(`S` and `d` synthesized from the formula). -/
theorem twinCubeWitness9_frozenFormB4_v1_rounds2 :
    ∀ level, level ≤ depth twinCubeWitness9 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 twinCubeWitness9
        (fun _ => formulaSize twinCubeWitness9)
        (normalizedFrontierWidthSchedule twinCubeWitness9)
        (depth twinCubeWitness9) 2 ParentKind.and level
        (dedupRepresentativeFrontier twinCubeWitness9 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    twinCubeWitness9 (fun _ => formulaSize twinCubeWitness9)
    (depth twinCubeWitness9) 2 ParentKind.and twinCubeWitness9_nonemptyFanin
    (Nat.le_refl _) (Nat.le_refl _) ?_
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [twinCubeWitness9_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · rw [twinCubeWitness9_dedupLength_zero, twinCubeWitness9_width_zero]
    decide
  · rw [twinCubeWitness9_dedupLength_one, twinCubeWitness9_width_one]
    decide
  · rw [twinCubeWitness9_dedupLength_two, twinCubeWitness9_width_two]
    decide
  · rw [twinCubeWitness9_dedupLength_three, twinCubeWitness9_width_three]
    decide

/-! ## Through-the-hypothesis wrapper instance at the coarse Entry ambient -/

private def twinCubeInnerAEntry9 : BDFormula 73811250 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨1, by decide⟩, sign := true }]

private def twinCubeInnerBEntry9 : BDFormula 73811250 :=
  .and [.lit { var := ⟨1, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def twinCubeMidEntry9 : BDFormula 73811250 :=
  .and [twinCubeInnerAEntry9, twinCubeInnerBEntry9]

/-- The strong witness shape at the coarse-Entry ambient
`73811250 = 2*(9*15)^2*(9*15*15) = frozenFormEntryProduct9` at size 15,
rounds 2. -/
def twinCubeWitnessEntry9 : BDFormula 73811250 :=
  .and [twinCubeMidEntry9, twinCubeMidEntry9]

private theorem twinCubeInnerAEntry9_nonempty :
    NonemptyFaninFormula twinCubeInnerAEntry9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeInnerAEntry9] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem twinCubeInnerBEntry9_nonempty :
    NonemptyFaninFormula twinCubeInnerBEntry9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeInnerBEntry9] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem twinCubeMidEntry9_nonempty :
    NonemptyFaninFormula twinCubeMidEntry9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeMidEntry9] at hG
  rcases hG with rfl | rfl
  · exact twinCubeInnerAEntry9_nonempty
  · exact twinCubeInnerBEntry9_nonempty

theorem twinCubeWitnessEntry9_nonemptyFanin :
    NonemptyFaninFormula twinCubeWitnessEntry9 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [twinCubeWitnessEntry9] at hG
  subst hG
  exact twinCubeMidEntry9_nonempty

theorem twinCubeWitnessEntry9_formulaSize :
    formulaSize twinCubeWitnessEntry9 = 15 := by
  simp [twinCubeWitnessEntry9, twinCubeMidEntry9, twinCubeInnerAEntry9,
    twinCubeInnerBEntry9, formulaSize_and, formulaSize_lit]

theorem twinCubeWitnessEntry9_depth : depth twinCubeWitnessEntry9 = 3 := by
  simp [twinCubeWitnessEntry9, twinCubeMidEntry9, twinCubeInnerAEntry9,
    twinCubeInnerBEntry9, depth]

/-- The coarse syntax-only Entry is met with **equality** at this ambient:
`frozenFormEntryProduct9 = 2*(9*15)^2*(9*15*15) = 73811250`. -/
theorem twinCubeWitnessEntry9_entryProduct_eq :
    frozenFormEntryProduct9 twinCubeWitnessEntry9 2 = 73811250 := by
  unfold frozenFormEntryProduct9
  rw [twinCubeWitnessEntry9_formulaSize]
  decide

/-- First through-the-hypothesis instantiation of the S2181 class wrapper:
the strong witness satisfies the coarse Entry obligation of
`frozenFormB4_v1_allLevels_uniform9` at ambient `73811250`, so the all-level
certificate follows from the wrapper itself rather than from the levelwise
route. -/
theorem twinCubeWitnessEntry9_frozenFormB4_v1_via_entry :
    ∀ level, level ≤ depth twinCubeWitnessEntry9 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9
        twinCubeWitnessEntry9
        (fun _ => formulaSize twinCubeWitnessEntry9)
        (normalizedFrontierWidthSchedule twinCubeWitnessEntry9)
        (depth twinCubeWitnessEntry9) 2 ParentKind.and level
        (dedupRepresentativeFrontier twinCubeWitnessEntry9 level) :=
  frozenFormB4_v1_allLevels_uniform9 twinCubeWitnessEntry9 2 ParentKind.and
    twinCubeWitnessEntry9_nonemptyFanin
    (Nat.le_of_eq twinCubeWitnessEntry9_entryProduct_eq)

end FormulaRecursiveSyntacticTerminalFrozenFormB4StrongWitness
end PvNP
