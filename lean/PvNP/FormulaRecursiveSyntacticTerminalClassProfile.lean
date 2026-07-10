import PvNP.FormulaRecursiveTerminalClassProfile
import PvNP.FormulaRecursiveSyntacticSimple

/-!
# Syntactic terminal class-envelope profile

This module adds a named restricted formula class combining the existing
syntactic-simple DNF predicate with the no-empty-fanin hypothesis, and packages a
terminal-aware syntactic class-envelope final-tree route for that class.

The main theorem remains deliberately bounded: it consumes the class-size
envelope and ambient geometric entry inequality, uses formula-size syntactic
width at intermediate frontiers and terminal width one at full depth, and keeps
the class budget `t(d,s)=S(d)*(s-1)`.  It does not synthesize a new counting
target, product hypothesis, arbitrary normalization, arbitrary AC0 collapse, PHP
switching lemma, Frege/PHP lower bound, NP/circuit lower bound, or P-vs-NP
conclusion.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalClassProfile

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveClassProfile
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticLayer
open FormulaRecursiveSyntacticSimple
open FormulaRecursiveTerminalClassProfile
open FormulaRecursiveTerminalProfile
open FormulaRecursiveTerminalTree
open FormulaRecursiveWidthSchedule
open FormulaSyntacticClassGlobalTree
open FormulaSyntacticSimpleBridge
open FormulaTruthTableView
open FrozenDepthView
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedRefinedCollapse
open GeneratedRefinedIteratedCertificate
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Restricted syntactic-terminal formula class -/

/-- Named restricted class for the S2142-style wrapper: root syntactic-simple
DNF syntax plus no empty fanins. -/
def SyntacticTerminalFormulaClass {n : Nat} (F : BDFormula n) : Prop :=
  syntacticFormulaSimpleDNF F /\ NoEmptyFanins F

/-- The terminal-aware full-depth width-one budget is covered by any class-size
envelope that covers the formula size. -/
theorem terminalAwareFrontierWidthBudget_fullDepth_le_classSize {n : Nat}
    (F : BDFormula n) (S : Nat -> Nat) (d : Nat)
    (hSize : formulaSize F <= S d) :
    terminalAwareFrontierWidthBudget F (depth F) <= S d := by
  have hpos : 1 <= S d := Nat.le_trans (formulaSize_pos F) hSize
  simpa [terminalAwareFrontierWidthBudget, terminalLayerWidthBudget] using hpos

/-- Intermediate syntactic frontier gates have width bounded by the class-size
envelope.  This is a gate-width certificate for the syntactic route; it is
separate from S2141's pre-existing `terminalAwareFrontierWidthBudget`, whose
intermediate budget is the ambient fallback. -/
theorem syntacticFrontierMinimalLayer_width_le_classSize_of_syntacticTerminal
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d level : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F)
    (hSize : formulaSize F <= S d) :
    forall g,
      List.Mem g (syntacticFrontierMinimalLayer F level parent
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
          hClass.1)).gates ->
        widthDNF g.theDNF <= S d := by
  intro g hg
  exact Nat.le_trans
    (syntacticFrontierMinimalLayer_width_le_formulaSize F level parent
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hClass.1)
      g hg)
    hSize

/-! ## Syntactic-terminal selector and width budget -/

/-- S2142-style width budget: terminal width one at full depth and formula-size
syntactic width at intermediate recursive frontiers. -/
def syntacticTerminalFrontierWidthBudget {n : Nat} (F : BDFormula n)
    (level : Nat) : Nat :=
  if level = depth F then terminalLayerWidthBudget F else formulaSize F

/-- S2142-style frontier selector: terminal layer at full depth and syntactic
frontier layer elsewhere. -/
def syntacticTerminalFrontierLayer {n : Nat} (F : BDFormula n)
    (level : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) : MinimalLayeredFormula n :=
  if level = depth F then terminalLayerMinimalLayer F parent
  else syntacticFrontierMinimalLayer F level parent
    (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level hClass.1)

/-- The syntactic-terminal layer represents the recursive frontier formula list
at every level. -/
theorem syntacticTerminalFrontierLayer_originalFormula {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) :
    (syntacticTerminalFrontierLayer F level parent hClass).originalFormula =
      parent.merge (formulaDepthFrontier level F) := by
  by_cases hlevel : level = depth F
  · subst level
    simp [syntacticTerminalFrontierLayer,
      terminalLayerMinimalLayer_originalFormula]
  · simp [syntacticTerminalFrontierLayer, hlevel,
      syntacticFrontierMinimalLayer_originalFormula]

/-- The syntactic-terminal layer keeps the recursive frontier gate count. -/
theorem syntacticTerminalFrontierLayer_gateCount {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) :
    (syntacticTerminalFrontierLayer F level parent hClass).gates.length =
      frontierLayerGateCount F level := by
  by_cases hlevel : level = depth F
  · subst level
    simp [syntacticTerminalFrontierLayer,
      terminalLayerMinimalLayer_gateCount]
  · simp [syntacticTerminalFrontierLayer, hlevel,
      syntacticFrontierMinimalLayer_gateCount]

/-- Every syntactic-terminal layer satisfies its S2142-style width budget. -/
theorem syntacticTerminalFrontierLayer_width_le_budget {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) :
    forall g,
      List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates ->
        widthDNF g.theDNF <= syntacticTerminalFrontierWidthBudget F level := by
  by_cases hlevel : level = depth F
  · subst level
    intro g hg
    have hg' : List.Mem g (terminalLayerMinimalLayer F parent).gates := by
      simpa [syntacticTerminalFrontierLayer] using hg
    simpa [syntacticTerminalFrontierWidthBudget, terminalLayerWidthBudget] using
      terminalLayerMinimalLayer_width_le_budget F parent g hg'
  · intro g hg
    have hg' : List.Mem g (syntacticFrontierMinimalLayer F level parent
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
          hClass.1)).gates := by
      simpa [syntacticTerminalFrontierLayer, hlevel] using hg
    simpa [syntacticTerminalFrontierWidthBudget, hlevel] using
      syntacticFrontierMinimalLayer_width_le_formulaSize F level parent
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
          hClass.1) g hg'

/-- The S2142 syntactic-terminal width budget is positive. -/
theorem syntacticTerminalFrontierWidthBudget_pos {n : Nat}
    (F : BDFormula n) (level : Nat) :
    1 <= syntacticTerminalFrontierWidthBudget F level := by
  by_cases hlevel : level = depth F
  · simp [syntacticTerminalFrontierWidthBudget, hlevel, terminalLayerWidthBudget]
  · simpa [syntacticTerminalFrontierWidthBudget, hlevel] using formulaSize_pos F

/-- The supplied class-size envelope bounds the S2142 syntactic-terminal width
budget at all levels. -/
theorem syntacticTerminalFrontierWidthBudget_le_classSize {n : Nat}
    (F : BDFormula n) (S : Nat -> Nat) (d level : Nat)
    (hSize : formulaSize F <= S d) :
    syntacticTerminalFrontierWidthBudget F level <= S d := by
  by_cases hlevel : level = depth F
  · have hpos : 1 <= S d := Nat.le_trans (formulaSize_pos F) hSize
    simpa [syntacticTerminalFrontierWidthBudget, hlevel,
      terminalLayerWidthBudget] using hpos
  · simpa [syntacticTerminalFrontierWidthBudget, hlevel] using hSize

/-! ## S2142 syntactic-terminal class-budget final-tree payload -/

open GeneratedRefinedIteratedCertificate in
/-- Final-tree payload for one S2142 syntactic-terminal recursive frontier level
under supplied class-size envelope. -/
def SyntacticTerminalClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S : Nat -> Nat) (d rounds : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) (level : Nat) : Prop :=
  level <= d /\
  exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (syntacticTerminalFrontierLayer F level parent hClass).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          syntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
    cert.stageBudgets = List.replicate (rounds + 1) 2 /\
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          syntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)).map stageStars /\
    TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          syntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)) /\
    exists T : DTree n, exists s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
      (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
      dtDepth T <= formulaClassDepthTreeBudget S d level s /\
      (forall a : Assignment n, Agree cert.finalComposed a ->
        dtEval a T = eval a (restrict cert.finalComposed
          (syntacticTerminalFrontierLayer F level parent hClass).originalFormula))

/-! ## True S2142 instantiation for the named class -/

/-- Single-level S2142-style wrapper for the named syntactic-terminal class.

The class budget is the existing `formulaClassDepthTreeBudget S d`, i.e.
`t(d,s) = S d * (s - 1)`.  Intermediate frontiers use syntactic formula-size
width and the terminal frontier uses width one, so no separate width-envelope
premise is required. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithClassBudget_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level <= depth F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n) :
    SyntacticTerminalClassDepthFinalTreeAt F S d rounds parent hClass level := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      syntacticTerminalFrontierWidthBudget F level)) (rounds + 1)
  let L := syntacticTerminalFrontierLayer F level parent hClass
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using syntacticTerminalFrontierLayer_gateCount F level parent hClass
  have hm : 1 <= frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level hClass.2 hk
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= syntacticTerminalFrontierWidthBudget F level := by
    simpa [L] using
      syntacticTerminalFrontierLayer_width_le_budget F level parent hClass
  have hw1 : 1 <= syntacticTerminalFrontierWidthBudget F level :=
    syntacticTerminalFrontierWidthBudget_pos F level
  have hmClass : frontierLayerGateCount F level <= S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have hwClass : syntacticTerminalFrontierWidthBudget F level <= S d :=
    syntacticTerminalFrontierWidthBudget_le_classSize F S d level hSize
  have hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        syntacticTerminalFrontierWidthBudget F level) <= n :=
    geometricEntryBound_of_class_envelopes hmClass hwClass hn
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (syntacticTerminalFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hnLayer
  have hregL : RegimeFrom L.gates.length
      (syntacticTerminalFrontierWidthBudget F level)
      (stars (freeRestriction n)) sched := by
    rw [hcount]
    exact hreg
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) sched.length sched :=
    formulaClassDepthTreeBudgetFrom F S d level hSize sched sched.length
  have htL : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hcount]
    exact ht
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (formulaClassDepthTreeBudget S d) sched (freeRestriction n) L
      (syntacticTerminalFrontierWidthBudget F level) hmL hwL hregL htL
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        syntacticTerminalFrontierWidthBudget F level))
  have htree' : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1) sched := by
    simpa [hcount, hlen] using htree
  have hbgeom :
      sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched] using geometricSchedule_budgets
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        syntacticTerminalFrontierWidthBudget F level))
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
      obtain ⟨heval, hdepthTree⟩ := lastStage_spec cert T m s hlast
      subst m
      have hlastCount :
          cert.lastStage =
            some (T, frontierLayerGateCount F level, s) := by
        simpa [hcount] using hlast
      have hgcRounds :
          cert.stageGateCounts =
            List.replicate (rounds + 1) (frontierLayerGateCount F level) := by
        rw [hgc, hcount, hlen]
      have hdepthClass :
          dtDepth T <= formulaClassDepthTreeBudget S d level s := by
        exact Nat.le_trans hdepthTree
          (by
            simpa [formulaClassDepthTreeBudget, hcount] using
              Nat.mul_le_mul_right (s - 1) hmClass)
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, hlastCount, heval, hdepthClass, ?_⟩
      · exact hgcRounds
      · rw [hb, hbgeom]
      · simpa [sched, hlen] using hsc
      · simpa [sched] using htree'
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

/-- All-level S2142-style wrapper for the named syntactic-terminal class.

This exposes the class budget `t(d,s)=S d * (s-1)` through
`SyntacticTerminalClassDepthFinalTreeAt`, with syntactic/formula-size width at
intermediate frontiers and width one at the terminal frontier. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n) :
    forall level, level <= depth F ->
      SyntacticTerminalClassDepthFinalTreeAt F S d rounds parent hClass level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithClassBudget_finalTree
      F S d level rounds parent hDepth hSize hClass hk hn

/-! ## Thin S2141 specializations retained for comparison -/

/-- Thin S2141 specialization for the named class.  Unlike the main S2142
theorem above, this uses S2141's terminal-aware selector and therefore still
requires the caller-supplied S2141 width premise at the target level. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithClassBudget_finalTree_S2141
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level <= depth F)
    (hvars : 1 <= n)
    (hwLevel : terminalAwareFrontierWidthBudget F level <= S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n) :
    TerminalAwareClassDepthFinalTreeAt F S d rounds parent level := by
  exact
    frontierLayer_geometricCollapseWithTerminalAwareClassDepthWidth_noEmptyFanins_finalTree
      F S S d level rounds parent hDepth hSize hClass.2 hk hvars hwLevel hn

/-- All-level thin S2141 specialization retained only as a comparison wrapper;
the main S2142 theorem above has no such width-envelope premise. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithClassBudget_finalTree_S2141
    {n : Nat} (F : BDFormula n) (S : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hvars : 1 <= n)
    (hwLevel : forall level, level <= depth F ->
      terminalAwareFrontierWidthBudget F level <= S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) <= n) :
    forall level, level <= depth F ->
      TerminalAwareClassDepthFinalTreeAt F S d rounds parent level := by
  exact
    allFrontierLayers_geometricCollapseWithTerminalAwareClassDepthWidth_noEmptyFanins_finalTree
      F S S d rounds parent hDepth hSize hClass.2 hvars hwLevel hn

end FormulaRecursiveSyntacticTerminalClassProfile
end PvNP
