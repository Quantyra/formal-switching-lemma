import PvNP.FormulaRecursiveDecompositionTree

/-!
# Terminal full-depth frontier final trees

`FormulaRecursiveDecompositionTree` packages all recursive frontier levels with
formula-size truth-table fallback final-tree evidence.  At the terminal
full-depth frontier, however, the bottom layer is sharper: every surviving raw
formula has depth zero and is already reified as a width-one-or-less
`GateSpec.dnf`.

This module records that sharper terminal route.  It derives the terminal
geometric entry bound from the same formula-size ambient hypothesis used by the
S2111 package, then exposes an actual terminal final tree for the
width-one bottom layer.

## Honest scope

* This sharpens only the terminal full-depth frontier layer.
* Intermediate recursive layers still use the truth-table fallback width `n`.
* The formula-size ambient bound remains a hypothesis.
* Product/counting hypotheses, efficient intermediate width synthesis,
  formula-class envelopes, arbitrary normalization, and a discharged global
  asymptotic `t(d,s)` theorem remain open.
* It is not a PHP switching lemma, not a Frege/PHP lower bound, not an
  NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveTerminalTree

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveClassDefault
open FormulaRecursiveDecomposition
open FormulaRecursiveDecompositionTree
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveRatioSchedule
open FormulaRecursiveSizeBound
open FormulaRecursiveWidthSchedule
open FormulaTruthTableView
open FrozenDepthView
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open GeneratedRefinedIteratedCertificate
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Terminal formula-size bound transfer -/

/-- The formula-size ambient bound used by the truth-table fallback route also
dominates the terminal full-depth geometric entry bound, where the width budget
is the sharp terminal width `1`. -/
theorem terminalLayer_geometricBound_of_formulaSize_bound {n : Nat}
    (F : BDFormula n) (rounds : Nat)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    2 * (64 * frontierLayerGateCount F (depth F)) ^ rounds *
        (64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F) <= n := by
  have hcount : frontierLayerGateCount F (depth F) <= formulaSize F :=
    frontierLayerGateCount_le_formulaSize F (depth F)
  have hbase :
      64 * frontierLayerGateCount F (depth F) <= 64 * formulaSize F :=
    Nat.mul_le_mul_left 64 hcount
  have hpow :
      (64 * frontierLayerGateCount F (depth F)) ^ rounds <=
        (64 * formulaSize F) ^ rounds :=
    Nat.pow_le_pow_left hbase rounds
  have hwidth : terminalLayerWidthBudget F <= n := by
    simpa [terminalLayerWidthBudget] using hvars
  have htail :
      64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F <=
        64 * formulaSize F * n :=
    Nat.mul_le_mul hbase hwidth
  exact Nat.le_trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) htail) hn

/-! ## Terminal final-tree payload -/

open GeneratedRefinedIteratedCertificate in
/-- Final-tree payload for the terminal full-depth frontier under the sharp
width-one terminal bottom-layer route. -/
def TerminalFormulaSizeSharpTree {n : Nat} (F : BDFormula n)
    (rounds : Nat) (parent : ParentKind) : Prop :=
  exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (terminalLayerMinimalLayer F parent).originalFormula
      (geometricSchedule (frontierLayerGateCount F (depth F))
        (n / (64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F (depth F)) /\
    cert.stageBudgets = List.replicate (rounds + 1) 2 /\
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F (depth F))
        (n / (64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F))
        (rounds + 1)).map stageStars /\
    TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      (frontierLayerGateCount F (depth F)) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F (depth F))
        (n / (64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F))
        (rounds + 1)) /\
    TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F (depth F)) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F (depth F))
        (n / (64 * frontierLayerGateCount F (depth F) *
          terminalLayerWidthBudget F))
        (rounds + 1)) /\
    exists T : DTree n, exists s : Nat,
      cert.lastStage =
        some (T, frontierLayerGateCount F (depth F), s) /\
      (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
      dtDepth T <= recursiveFrontierSizeTreeBudget F (depth F) s /\
      (forall a : Assignment n, Agree cert.finalComposed a ->
        dtEval a T = eval a (restrict cert.finalComposed
          (terminalLayerMinimalLayer F parent).originalFormula))

open GeneratedRefinedIteratedCertificate in
/-- Terminal full-depth bottom layer, with the sharp width-one budget, exposes
an actual final decision tree under the formula-size ambient hypothesis.

This is the terminal sharpening missing from the all-level truth-table fallback
package: only the terminal layer uses width `1`; intermediate layers remain at
fallback width `n`. -/
theorem terminalLayer_geometricCollapseWithFormulaSize_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n)
    (rounds : Nat) (parent : ParentKind)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    TerminalFormulaSizeSharpTree F rounds parent := by
  have hm : 1 <= frontierLayerGateCount F (depth F) :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F (depth F) hF
      (Nat.le_refl _)
  have hnTerminal :
      2 * (64 * frontierLayerGateCount F (depth F)) ^ rounds *
          (64 * frontierLayerGateCount F (depth F) *
            terminalLayerWidthBudget F) <= n :=
    terminalLayer_geometricBound_of_formulaSize_bound F rounds hvars hn
  let sched := geometricSchedule (frontierLayerGateCount F (depth F))
    (n / (64 * frontierLayerGateCount F (depth F) *
      terminalLayerWidthBudget F)) (rounds + 1)
  obtain ⟨cert, hgc, hb, hsc, htGlobal⟩ :=
    terminalLayer_geometricCollapseWithGlobalTreeBudget
      F rounds parent hm hnTerminal
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F (depth F)) (rounds + 1)
      (n / (64 * frontierLayerGateCount F (depth F) *
        terminalLayerWidthBudget F))
  have hgcLen :
      cert.stageGateCounts =
        List.replicate sched.length
          (frontierLayerGateCount F (depth F)) := by
    rw [hgc, hlen]
  have htSize : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F (depth F)) (rounds + 1) sched :=
    recursiveFrontierSizeTreeBudgetFrom F (depth F) sched (rounds + 1)
  have hpos : 0 < sched.length := by
    rw [hlen]
    exact Nat.succ_pos rounds
  have hsome := lastStage_isSome cert hpos
  cases hlast : cert.lastStage with
  | none =>
      rw [hlast] at hsome
      simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = frontierLayerGateCount F (depth F) :=
        lastStage_gateCount_of_stageGateCounts_replicate cert
          hgcLen T m s hlast
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      have hdepthSize :
          dtDepth T <= recursiveFrontierSizeTreeBudget F (depth F) s := by
        have hcount :
            frontierLayerGateCount F (depth F) <= formulaSize F :=
          frontierLayerGateCount_le_formulaSize F (depth F)
        exact Nat.le_trans hdepth
          (by
            simpa [recursiveFrontierSizeTreeBudget] using
              Nat.mul_le_mul_right (s - 1) hcount)
      refine ⟨cert, ?_, ?_, ?_, ?_, ?_, T, s, ?_, heval, hdepthSize, ?_⟩
      · simpa [sched] using hgc
      · exact hb
      · simpa [sched] using hsc
      · simpa [sched] using htGlobal
      · exact htSize
      · exact hlast
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

/-! ## Full-depth package with terminal sharpening -/

/-- The S2111 full-depth package plus a sharp terminal final tree using the
width-one terminal bottom layer. -/
structure FullDepthFormulaSizeTruthTableSharpTerminalPackage {n : Nat}
    (F : BDFormula n) (d rounds : Nat) (parent : ParentKind) where
  basePackage : FullDepthFormulaSizeTruthTableTreePackage F d rounds parent
  terminalSharpTree : TerminalFormulaSizeSharpTree F rounds parent

open GeneratedRefinedIteratedCertificate in
/-- Construct the full-depth formula-size truth-table package and add the
terminal width-one final-tree sharpening. -/
def fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_sharpTerminalPackage
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    FullDepthFormulaSizeTruthTableSharpTerminalPackage F d rounds parent where
  basePackage :=
    fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_finalTreePackage
      F d rounds parent hDepth hF hvars hn
  terminalSharpTree :=
    terminalLayer_geometricCollapseWithFormulaSize_noEmptyFanins_finalTree
      F rounds parent hF hvars hn

open GeneratedRefinedIteratedCertificate in
/-- Existence form of the full-depth package with the terminal width-one
final-tree sharpening. -/
theorem exists_fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_sharpTerminalFinalTree
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    Nonempty
      (FullDepthFormulaSizeTruthTableSharpTerminalPackage
        F d rounds parent) := by
  exact ⟨
    fullDepthRecursiveDecomposition_geometricCollapseWithTruthTableFormulaSize_noEmptyFanins_sharpTerminalPackage
      F d rounds parent hDepth hF hvars hn⟩

end FormulaRecursiveTerminalTree
end PvNP
