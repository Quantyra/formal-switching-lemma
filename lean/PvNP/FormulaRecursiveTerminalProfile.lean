import PvNP.FormulaRecursiveTerminalTree

/-!
# Terminal-aware recursive frontier profile

`FormulaRecursiveTerminalTree` added a sharp terminal final-tree route next to
the S2111 all-level truth-table package.  This module puts that distinction
into one layer selector: intermediate recursive frontier levels keep the
truth-table fallback layer, while the full-depth terminal level uses the
width-one terminal bottom layer.

## Honest scope

* This sharpens only the terminal full-depth frontier level inside a uniform
  all-level interface.
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
namespace FormulaRecursiveTerminalProfile

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
open FormulaRecursiveSizeBound
open FormulaRecursiveTerminalTree
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

/-! ## Terminal-aware layers and widths -/

/-- Width budget for the terminal-aware recursive profile: fallback width `n`
at intermediate levels and terminal width `1` at the full-depth level. -/
def terminalAwareFrontierWidthBudget {n : Nat} (F : BDFormula n)
    (level : Nat) : Nat :=
  if level = depth F then terminalLayerWidthBudget F
  else frontierLayerWidthBudget F level

/-- Recursive frontier layer selector that uses the terminal bottom layer at
the full-depth frontier and the existing truth-table frontier layer elsewhere. -/
def terminalAwareFrontierLayer {n : Nat} (F : BDFormula n)
    (level : Nat) (parent : ParentKind) : MinimalLayeredFormula n :=
  if level = depth F then terminalLayerMinimalLayer F parent
  else frontierLayerMinimalLayer F level parent

/-- The terminal-aware layer represents the same frontier formula list as the
ordinary recursive frontier at every level. -/
theorem terminalAwareFrontierLayer_originalFormula {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind) :
    (terminalAwareFrontierLayer F level parent).originalFormula =
      parent.merge (formulaDepthFrontier level F) := by
  by_cases hlevel : level = depth F
  · subst level
    simp [terminalAwareFrontierLayer,
      terminalLayerMinimalLayer_originalFormula]
  · simp [terminalAwareFrontierLayer, hlevel,
      frontierLayerMinimalLayer_originalFormula]

/-- The terminal-aware layer keeps the recursive frontier gate count. -/
theorem terminalAwareFrontierLayer_gateCount {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind) :
    (terminalAwareFrontierLayer F level parent).gates.length =
      frontierLayerGateCount F level := by
  by_cases hlevel : level = depth F
  · subst level
    simp [terminalAwareFrontierLayer,
      terminalLayerMinimalLayer_gateCount]
  · simp [terminalAwareFrontierLayer, hlevel,
      frontierLayerMinimalLayer_gateCount]

/-- Every terminal-aware layer satisfies its terminal-aware width budget. -/
theorem terminalAwareFrontierLayer_width_le_budget {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind) :
    forall g,
      List.Mem g (terminalAwareFrontierLayer F level parent).gates ->
        widthDNF g.theDNF <= terminalAwareFrontierWidthBudget F level := by
  by_cases hlevel : level = depth F
  · subst level
    intro g hg
    have hg' : List.Mem g (terminalLayerMinimalLayer F parent).gates := by
      simpa [terminalAwareFrontierLayer] using hg
    simpa [terminalAwareFrontierLayer,
      terminalAwareFrontierWidthBudget] using
      terminalLayerMinimalLayer_width_le_budget F parent g hg'
  · intro g hg
    have hg' : List.Mem g (frontierLayerMinimalLayer F level parent).gates := by
      simpa [terminalAwareFrontierLayer, hlevel] using hg
    simpa [terminalAwareFrontierLayer,
      terminalAwareFrontierWidthBudget, hlevel] using
      frontierLayerMinimalLayer_width_le_budget F level parent g hg'

/-- The terminal-aware width budget is always at most the ambient variable
count, assuming the ambient variable count is nonzero. -/
theorem terminalAwareFrontierWidthBudget_le_vars {n : Nat}
    (F : BDFormula n) (level : Nat) (hvars : 1 <= n) :
    terminalAwareFrontierWidthBudget F level <= n := by
  by_cases hlevel : level = depth F
  · simpa [terminalAwareFrontierWidthBudget, hlevel,
      terminalLayerWidthBudget] using hvars
  · simp [terminalAwareFrontierWidthBudget, hlevel,
      frontierLayerWidthBudget]

/-- The terminal-aware width budget is positive when the ambient variable
count is nonzero. -/
theorem terminalAwareFrontierWidthBudget_pos {n : Nat}
    (F : BDFormula n) (level : Nat) (hvars : 1 <= n) :
    1 <= terminalAwareFrontierWidthBudget F level := by
  by_cases hlevel : level = depth F
  · simp [terminalAwareFrontierWidthBudget, hlevel,
      terminalLayerWidthBudget]
  · simpa [terminalAwareFrontierWidthBudget, hlevel,
      frontierLayerWidthBudget] using hvars

/-! ## Formula-size entry-bound transfer -/

/-- The same formula-size ambient bound used by the fallback route dominates
every terminal-aware level: intermediate levels have width `n`, while the
terminal level has width `1`. -/
theorem terminalAware_geometricBound_of_formulaSize_bound {n : Nat}
    (F : BDFormula n) (level rounds : Nat)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level) <= n := by
  have hcount : frontierLayerGateCount F level <= formulaSize F :=
    frontierLayerGateCount_le_formulaSize F level
  have hbase :
      64 * frontierLayerGateCount F level <= 64 * formulaSize F :=
    Nat.mul_le_mul_left 64 hcount
  have hpow :
      (64 * frontierLayerGateCount F level) ^ rounds <=
        (64 * formulaSize F) ^ rounds :=
    Nat.pow_le_pow_left hbase rounds
  have hwidth : terminalAwareFrontierWidthBudget F level <= n :=
    terminalAwareFrontierWidthBudget_le_vars F level hvars
  have htail :
      64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level <=
        64 * formulaSize F * n :=
    Nat.mul_le_mul hbase hwidth
  exact Nat.le_trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) htail) hn

/-! ## Terminal-aware final-tree payloads -/

open GeneratedRefinedIteratedCertificate in
/-- Final-tree payload for one terminal-aware recursive frontier level under
the formula-size ambient bound. -/
def TerminalAwareFormulaSizeFinalTreeAt {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind) (level : Nat) : Prop :=
  level <= d /\
  exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (terminalAwareFrontierLayer F level parent).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
    cert.stageBudgets = List.replicate (rounds + 1) 2 /\
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
        (rounds + 1)).map stageStars /\
    TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          terminalAwareFrontierWidthBudget F level))
        (rounds + 1)) /\
    exists T : DTree n, exists s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
      (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
      dtDepth T <= recursiveFrontierSizeTreeBudget F level s /\
      (forall a : Assignment n, Agree cert.finalComposed a ->
        dtEval a T = eval a (restrict cert.finalComposed
          (terminalAwareFrontierLayer F level parent).originalFormula))

open GeneratedRefinedIteratedCertificate in
/-- One terminal-aware frontier level exposes an actual final decision tree
under the formula-size ambient hypothesis.

At `level = depth F`, the generated collapse consumes the terminal width-one
bottom layer.  At all earlier levels it consumes the existing truth-table
fallback layer. -/
theorem frontierLayer_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hk : level <= depth F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    TerminalAwareFormulaSizeFinalTreeAt F d rounds parent level := by
  refine And.intro (Nat.le_trans hk hDepth) ?_
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      terminalAwareFrontierWidthBudget F level)) (rounds + 1)
  let L := terminalAwareFrontierLayer F level parent
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using terminalAwareFrontierLayer_gateCount F level parent
  have hm : 1 <= frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= terminalAwareFrontierWidthBudget F level := by
    simpa [L] using
      terminalAwareFrontierLayer_width_le_budget F level parent
  have hw1 : 1 <= terminalAwareFrontierWidthBudget F level :=
    terminalAwareFrontierWidthBudget_pos F level hvars
  have hnLayer :
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
          (64 * frontierLayerGateCount F level *
            terminalAwareFrontierWidthBudget F level) <= n :=
    terminalAware_geometricBound_of_formulaSize_bound
      F level rounds hvars hn
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hnLayer
  have hregL : RegimeFrom L.gates.length
      (terminalAwareFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F level) sched.length sched :=
    recursiveFrontierSizeTreeBudgetFrom F level sched sched.length
  have htL : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain hcert := autoIteratedCollapse_of_ratioRegime
    (recursiveFrontierSizeTreeBudget F) sched (freeRestriction n) L
    (terminalAwareFrontierWidthBudget F level) hmL hwL hregL htL
  rcases hcert with ⟨cert, hgc, hb, hsc, htree⟩
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level))
  have htree' : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F level) (rounds + 1) sched := by
    simpa [hcount, hlen] using htree
  have hbgeom :
      sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched] using geometricSchedule_budgets
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        terminalAwareFrontierWidthBudget F level))
  have hposSched : 0 < sched.length := by
    rw [hlen]
    exact Nat.succ_pos rounds
  have hsome := lastStage_isSome cert hposSched
  cases hlast : cert.lastStage with
  | none =>
      rw [hlast] at hsome
      simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLastLayer : m = L.gates.length :=
        lastStage_gateCount_of_stageGateCounts_replicate cert
          hgc T m s hlast
      have hmLast : m = frontierLayerGateCount F level := by
        rw [hcount] at hmLastLayer
        exact hmLastLayer
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      have hlastCount :
          cert.lastStage =
            some (T, frontierLayerGateCount F level, s) := by
        simpa [hcount] using hlast
      have hdepthCount :
          dtDepth T <= frontierLayerGateCount F level * (s - 1) := by
        simpa [hcount] using hdepth
      have hgcRounds :
          cert.stageGateCounts =
            List.replicate (rounds + 1) (frontierLayerGateCount F level) := by
        rw [hgc, hcount, hlen]
      have hdepthSize :
          dtDepth T <= recursiveFrontierSizeTreeBudget F level s := by
        have hcountSize :
            frontierLayerGateCount F level <= formulaSize F :=
          frontierLayerGateCount_le_formulaSize F level
        exact Nat.le_trans hdepthCount
          (by
            simpa [recursiveFrontierSizeTreeBudget] using
              Nat.mul_le_mul_right (s - 1) hcountSize)
      refine Exists.intro cert ?_
      refine And.intro hgcRounds ?_
      refine And.intro ?_ ?_
      · rw [hb, hbgeom]
      refine And.intro ?_ ?_
      · simpa [sched, hlen] using hsc
      refine And.intro ?_ ?_
      · simpa [sched] using htree'
      refine Exists.intro T ?_
      refine Exists.intro s ?_
      refine And.intro hlastCount ?_
      refine And.intro heval ?_
      refine And.intro hdepthSize ?_
      intro a ha
      rw [heval a, finalFormula_restrict_eval cert a ha]

open GeneratedRefinedIteratedCertificate in
/-- Uniform all-level terminal-aware formula-size final-tree route. -/
theorem allFrontierLayers_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    forall level, level <= depth F ->
      TerminalAwareFormulaSizeFinalTreeAt F d rounds parent level := by
  intro level hk
  exact
    frontierLayer_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTree
      F d level rounds parent hDepth hF hk hvars hn

/-! ## Full-depth package with terminal-aware all-level evidence -/

/-- Full-depth recursive decomposition with all-level terminal-aware
formula-size final-tree evidence. -/
structure FullDepthTerminalAwareFormulaSizeTreePackage {n : Nat}
    (F : BDFormula n) (d rounds : Nat) (parent : ParentKind) where
  decomposition : FullDepthRecursiveDecomposition F
  terminal_formulas :
    decomposition.terminalLayer.gates.map GateSpec.formula =
      decomposition.frontier (depth F)
  terminal_width :
    forall g, List.Mem g decomposition.terminalLayer.gates ->
      widthDNF g.theDNF <= 1
  finalTrees :
    forall level, level <= depth F ->
      TerminalAwareFormulaSizeFinalTreeAt F d rounds parent level

open GeneratedRefinedIteratedCertificate in
/-- Construct the full-depth recursive decomposition and attach all-level
terminal-aware formula-size final-tree evidence. -/
def fullDepthRecursiveDecomposition_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTreePackage
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    FullDepthTerminalAwareFormulaSizeTreePackage F d rounds parent := by
  refine
    { decomposition := fullDepthRecursiveDecomposition F
      terminal_formulas := ?_
      terminal_width := ?_
      finalTrees := ?_ }
  · exact (fullDepthRecursiveDecomposition F).terminal_formulas_eq
  · exact (fullDepthRecursiveDecomposition F).terminal_width
  · exact
      allFrontierLayers_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTree
        F d rounds parent hDepth hF hvars hn

open GeneratedRefinedIteratedCertificate in
/-- Existence form of the full-depth structural package with terminal-aware
formula-size final-tree evidence at every in-depth recursive frontier level. -/
theorem exists_fullDepthRecursiveDecomposition_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTree
    {n : Nat} (F : BDFormula n)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hF : NoEmptyFanins F)
    (hvars : 1 <= n)
    (hn : 2 * (64 * formulaSize F) ^ rounds *
        (64 * formulaSize F * n) <= n) :
    Nonempty
      (FullDepthTerminalAwareFormulaSizeTreePackage
        F d rounds parent) := by
  exact Nonempty.intro
    (fullDepthRecursiveDecomposition_geometricCollapseWithTerminalAwareFormulaSize_noEmptyFanins_finalTreePackage
      F d rounds parent hDepth hF hvars hn)

end FormulaRecursiveTerminalProfile
end PvNP
