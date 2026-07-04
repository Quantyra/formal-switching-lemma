import PvNP.FormulaSyntacticSimpleBridge

/-!
# Recursive frontier layers from structurally simple syntactic DNFs

The existing recursive frontier layer package uses the truth-table/path-DNF
fallback, so intermediate layer widths are bounded by the ambient variable
count `n`.  This module adds a parallel frontier-layer package for levels whose
frontier formulas are structurally certified by
`FormulaSyntacticSimpleBridge.syntacticFormulaSimpleDNF`.

For such a frontier, each child is packaged as a `GateSpec.dnf` using its
syntactic DNF view, every gate width is bounded by the root formula size
`formulaSize F`, and the existing ratio/geometric schedule consumers can run at
that formula-size width under the size-based tree budget.

## Honest scope

* The per-frontier structural simplicity predicate is supplied.
* This does not normalize arbitrary syntactic DNFs or prove the predicate
  complete.
* Product/counting hypotheses, ratio regimes, nonempty counts, and geometric
  entry-size inequalities remain supplied.
* This is not full frozen-form B4, not a global formula-class `t(d,s)` theorem,
  not a PHP switching lemma, not a Frege/PHP lower bound, not an NP/circuit
  lower bound, and not a P-vs-NP result.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticLayer

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveSizeBound
open FormulaSyntacticSimpleBridge
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open GeneratedIteratedCollapseFinal
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Syntactic-simple gates for raw formulas -/

/-- A raw formula packaged as a `GateSpec.dnf` through its structurally
certified syntactic DNF view. -/
def syntacticSimpleFormulaGate {n : Nat} (F : BDFormula n)
    (h : syntacticFormulaSimpleDNF F) : GateSpec n :=
  GateSpec.dnf F (syntacticDNFViewOfFormulaSimple F h)

theorem syntacticSimpleFormulaGate_formula {n : Nat} (F : BDFormula n)
    (h : syntacticFormulaSimpleDNF F) :
    (syntacticSimpleFormulaGate F h).formula = F := rfl

theorem syntacticSimpleFormulaGate_width_le_formulaSize {n : Nat}
    (F : BDFormula n) (h : syntacticFormulaSimpleDNF F) :
    widthDNF (syntacticSimpleFormulaGate F h).theDNF <= formulaSize F :=
  widthDNF_syntacticDNFViewOfFormulaSimple_le_formulaSize F h

/-! ## Frontier structural-simple predicates and gate lists -/

/-- Every raw formula at recursive frontier level `k` is structurally certified
to have a simple syntactic DNF expansion. -/
def FrontierSyntacticSimple {n : Nat} (F : BDFormula n) (k : Nat) : Prop :=
  forall G, List.Mem G (formulaDepthFrontier k F) ->
    syntacticFormulaSimpleDNF G

/-- Reify a structurally certified recursive frontier as syntactic-DNF gates. -/
def syntacticFrontierGateList {n : Nat} (F : BDFormula n) (k : Nat)
    (h : FrontierSyntacticSimple F k) : List (GateSpec n) :=
  (formulaDepthFrontier k F).attach.map
    (fun G => syntacticSimpleFormulaGate G.1 (h G.1 G.2))

theorem syntacticFrontierGateList_length {n : Nat} (F : BDFormula n) (k : Nat)
    (h : FrontierSyntacticSimple F k) :
    (syntacticFrontierGateList F k h).length =
      (formulaDepthFrontier k F).length := by
  simp [syntacticFrontierGateList]

theorem syntacticFrontierGateList_formulas {n : Nat}
    (F : BDFormula n) (k : Nat) (h : FrontierSyntacticSimple F k) :
    (syntacticFrontierGateList F k h).map GateSpec.formula =
      formulaDepthFrontier k F := by
  rw [syntacticFrontierGateList, List.map_map]
  change List.map (fun G : {x // x ∈ formulaDepthFrontier k F} =>
      (G.1 : BDFormula n)) (formulaDepthFrontier k F).attach =
    formulaDepthFrontier k F
  simpa only [List.map_id'] using
    List.attach_map_val (formulaDepthFrontier k F) (fun G : BDFormula n => G)

private theorem formulaSize_le_formulaSizeSum_of_mem {n : Nat}
    {G : BDFormula n} :
    forall xs : List (BDFormula n), List.Mem G xs ->
      formulaSize G <= formulaSizeSum xs
  | [], hmem => by
      cases hmem
  | X :: xs, hmem => by
      simp [formulaSizeSum]
      rcases List.mem_cons.mp hmem with hGX | hGxs
      · subst hGX
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (formulaSize_le_formulaSizeSum_of_mem xs hGxs)
          (Nat.le_add_left _ _)

theorem syntacticFrontierGateList_width_le_formulaSizeSum {n : Nat}
    (F : BDFormula n) (k : Nat) (h : FrontierSyntacticSimple F k) :
    forall g, List.Mem g (syntacticFrontierGateList F k h) ->
      widthDNF g.theDNF <= formulaSizeSum (formulaDepthFrontier k F) := by
  intro g hg
  rw [syntacticFrontierGateList] at hg
  rcases List.mem_map.mp hg with ⟨G, _hGmem, rfl⟩
  have hwidth :=
    syntacticSimpleFormulaGate_width_le_formulaSize G.1 (h G.1 G.2)
  have hsize :
      formulaSize G.1 <= formulaSizeSum (formulaDepthFrontier k F) :=
    formulaSize_le_formulaSizeSum_of_mem (formulaDepthFrontier k F) G.2
  exact Nat.le_trans hwidth hsize

theorem syntacticFrontierGateList_width_le_formulaSize {n : Nat}
    (F : BDFormula n) (k : Nat) (h : FrontierSyntacticSimple F k) :
    forall g, List.Mem g (syntacticFrontierGateList F k h) ->
      widthDNF g.theDNF <= formulaSize F := by
  intro g hg
  exact Nat.le_trans
    (syntacticFrontierGateList_width_le_formulaSizeSum F k h g hg)
    (formulaSizeSum_depthFrontier_le k [F])

/-! ## Packaged syntactic frontier layers -/

/-- A recursive frontier layer reified through structurally certified syntactic
DNF views, with formula-size width control. -/
structure SyntacticFrontierGateLayer {n : Nat} (F : BDFormula n) (k : Nat) where
  gates : List (GateSpec n)
  formulas_eq : gates.map GateSpec.formula = formulaDepthFrontier k F
  gate_width_formulaSize :
    forall g, List.Mem g gates -> widthDNF g.theDNF <= formulaSize F
  count_eq : gates.length = (formulaDepthFrontier k F).length

def syntacticFrontierGateLayer {n : Nat} (F : BDFormula n) (k : Nat)
    (h : FrontierSyntacticSimple F k) :
    SyntacticFrontierGateLayer F k where
  gates := syntacticFrontierGateList F k h
  formulas_eq := syntacticFrontierGateList_formulas F k h
  gate_width_formulaSize := syntacticFrontierGateList_width_le_formulaSize F k h
  count_eq := syntacticFrontierGateList_length F k h

/-- A syntactic-simple recursive frontier layer as a generated-collapse
`MinimalLayeredFormula`. -/
def syntacticFrontierMinimalLayer {n : Nat} (F : BDFormula n) (k : Nat)
    (p : ParentKind) (h : FrontierSyntacticSimple F k) :
    MinimalLayeredFormula n where
  parent := p
  gates := (syntacticFrontierGateLayer F k h).gates

theorem syntacticFrontierMinimalLayer_originalFormula {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind)
    (h : FrontierSyntacticSimple F k) :
    (syntacticFrontierMinimalLayer F k p h).originalFormula =
      p.merge (formulaDepthFrontier k F) := by
  change p.merge ((syntacticFrontierGateLayer F k h).gates.map
      GateSpec.formula) = p.merge (formulaDepthFrontier k F)
  rw [(syntacticFrontierGateLayer F k h).formulas_eq]

theorem syntacticFrontierMinimalLayer_gateCount {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind)
    (h : FrontierSyntacticSimple F k) :
    (syntacticFrontierMinimalLayer F k p h).gates.length =
      frontierLayerGateCount F k := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  exact (syntacticFrontierGateLayer F k h).count_eq

theorem syntacticFrontierMinimalLayer_width_le_formulaSize {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind)
    (h : FrontierSyntacticSimple F k) :
    forall g, List.Mem g (syntacticFrontierMinimalLayer F k p h).gates ->
      widthDNF g.theDNF <= formulaSize F := by
  simpa [syntacticFrontierMinimalLayer] using
    (syntacticFrontierGateLayer F k h).gate_width_formulaSize

/-! ## Ratio and geometric consumers at formula-size width -/

open GeneratedRefinedIteratedCertificate in
/-- A structurally certified recursive frontier layer can consume a supplied
ratio-regime schedule at width `formulaSize F` under the size-based tree
budget. -/
theorem syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hSimple : FrontierSyntacticSimple F level)
    (sched : List ScheduleStage)
    (hm : 1 <= frontierLayerGateCount F level)
    (hreg : RegimeFrom (frontierLayerGateCount F level)
      (formulaSize F) (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent hSimple).originalFormula
        sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F level) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F level) sched.length sched := by
  let L := syntacticFrontierMinimalLayer F level parent hSimple
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using
      syntacticFrontierMinimalLayer_gateCount F level parent hSimple
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= formulaSize F := by
    simpa [L] using
      syntacticFrontierMinimalLayer_width_le_formulaSize F level parent hSimple
  have hregL : RegimeFrom L.gates.length
      (formulaSize F) (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      (frontierLayerGateCount F level) sched.length sched :=
    recursiveFrontierSizeTreeBudgetFrom F level sched sched.length
  have htL : TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (recursiveFrontierSizeTreeBudget F) sched (freeRestriction n) L
      (formulaSize F) hmL hwL hregL htL
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using htree

open GeneratedRefinedIteratedCertificate in
/-- Uniform ratio-regime form for all levels whose frontiers are structurally
certified simple. -/
theorem allSyntacticFrontierLayers_ratioRegimeCollapseWithFormulaSize {n : Nat}
    (F : BDFormula n) (parent : ParentKind)
    (sched : List ScheduleStage)
    (hSimple : forall level, level <= depth F ->
      FrontierSyntacticSimple F level)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (formulaSize F) (stars (freeRestriction n)) sched) :
    forall (level : Nat) (hk : level <= depth F),
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (syntacticFrontierMinimalLayer F level parent
            (hSimple level hk)).originalFormula sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  intro level hk
  exact syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize
    F level parent (hSimple level hk) sched (hm level hk) (hreg level hk)

open GeneratedRefinedIteratedCertificate in
/-- A structurally certified recursive frontier layer can use the named
geometric schedule at width `formulaSize F` under the corresponding explicit
entry-size bound. -/
theorem syntacticFrontierLayer_geometricCollapseWithFormulaSize {n : Nat}
    (F : BDFormula n) (level rounds : Nat) (parent : ParentKind)
    (hSimple : FrontierSyntacticSimple F level)
    (hm : 1 <= frontierLayerGateCount F level)
    (hw1 : 1 <= formulaSize F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * formulaSize F) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (syntacticFrontierMinimalLayer F level parent hSimple).originalFormula
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)).length,
      cert.stageGateCounts =
        List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
      cert.stageBudgets = List.replicate (rounds + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)).map stageStars /\
      TreeBudgetFrom (recursiveFrontierSizeTreeBudget F)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level * formulaSize F))
          (rounds + 1)) := by
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level * formulaSize F)) (rounds + 1)
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (formulaSize F) (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hn
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level * formulaSize F))
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    syntacticFrontierLayer_ratioRegimeCollapseWithFormulaSize
      F level parent hSimple sched hm hreg
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc, hlen]
  · have hbgeom :
        sched.map stageS = List.replicate (rounds + 1) 2 := by
      simpa [sched] using geometricSchedule_budgets
        (frontierLayerGateCount F level) (rounds + 1)
        (n / (64 * frontierLayerGateCount F level * formulaSize F))
    simpa [hbgeom] using hb
  · simpa [sched] using hsc
  · simpa [sched, hlen] using ht

end FormulaRecursiveSyntacticLayer
end PvNP
