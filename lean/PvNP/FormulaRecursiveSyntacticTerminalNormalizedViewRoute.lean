import PvNP.FormulaSyntacticDNFNormalization
import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget
import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget
import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightEntry

/-!
# Normalized-view recursive frontier route

This module replaces the syntactic-simplicity premise of the restricted
recurrence-width route by the unconditional normalized DNF view.  Its formula
class contains exactly constants, literals, and nonempty OR/AND trees.  The
recurrence width, geometric schedule, per-stage budget `2`, and final-tree
budget `S d * (s - 1)` are unchanged.

This is only a normalized-view route for that certified class.  It is not an
arbitrary bounded-depth collapse theorem, a threshold improvement, full B4,
PHP switching, Frege/PHP, a circuit lower bound, Gate A, or P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalNormalizedViewRoute

open BoundedDepthCanonicalDT BoundedDepthFrege BoundedDepthIteratedCollapse BoundedDepthLayerView
open BoundedDepthDecisionTree BoundedDepthRestriction CNFModel
open FormulaRecursiveClassProfile FormulaRecursiveDecomposition FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule FormulaRecursiveLayerProfile FormulaRecursiveNonempty
open FormulaRecursiveSizeBound FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget
open FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget
open FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget
open FormulaSyntacticDNF FormulaSyntacticDNFNormalization FormulaSyntacticSimpleBridge
open FormulaSyntacticClassGlobalTree FormulaTruthTableView FrozenDepthView
open FrozenProductSchedule FrozenProductScheduleRatio
open GeneratedGoodRestriction GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction GeneratedRefinedCollapse
open GeneratedRefinedIteratedCertificate
open SwitchingEncodeConstruct SwitchingLemmaStatement

/-- Constants/literals and nonempty OR/AND trees.  No simplicity or support
condition is imposed. -/
inductive NonemptyFaninFormula {n : Nat} : BDFormula n → Prop where
  | tru : NonemptyFaninFormula .tru
  | fls : NonemptyFaninFormula .fls
  | lit (l : Literal n) : NonemptyFaninFormula (.lit l)
  | or {children : List (BDFormula n)} (hne : children ≠ [])
      (hchildren : ∀ G, G ∈ children → NonemptyFaninFormula G) :
      NonemptyFaninFormula (.or children)
  | and {children : List (BDFormula n)} (hne : children ≠ [])
      (hchildren : ∀ G, G ∈ children → NonemptyFaninFormula G) :
      NonemptyFaninFormula (.and children)

theorem nonemptyFanin_noEmptyFanins {n : Nat} {F : BDFormula n}
    (h : NonemptyFaninFormula F) : NoEmptyFanins F := by
  induction h with
  | tru => exact NoEmptyFanins.tru
  | fls => exact NoEmptyFanins.fls
  | lit l => exact NoEmptyFanins.lit l
  | or hne _ ih => exact NoEmptyFanins.or hne ih
  | and hne _ ih => exact NoEmptyFanins.and hne ih

theorem recurrenceFanin_nonemptyFanin {n : Nat} {F : BDFormula n}
    (h : RecurrenceFaninFormula F) : NonemptyFaninFormula F := by
  induction h with
  | tru => exact .tru
  | fls => exact .fls
  | lit l => exact .lit l
  | or hne _ ih => exact .or hne ih
  | and hne _ _ ih => exact .and hne ih

theorem disjointSupportFanin_nonemptyFanin {n : Nat} {F : BDFormula n}
    (h : DisjointSupportFaninFormula F) : NonemptyFaninFormula F :=
  recurrenceFanin_nonemptyFanin (disjointSupportFanin_recurrenceFanin h)

theorem nonemptyFanin_topChildren_closed {n : Nat} {F G : BDFormula n}
    (h : NonemptyFaninFormula F) (hG : G ∈ topChildren F) :
    NonemptyFaninFormula G := by
  cases h with
  | tru => simp [topChildren] at hG
  | fls => simp [topChildren] at hG
  | lit l => simp [topChildren] at hG
  | or _ hc => simpa [topChildren] using hc G hG
  | and _ hc => simpa [topChildren] using hc G hG

theorem nonemptyFanin_frontier_closed {n : Nat} {F : BDFormula n}
    (h : NonemptyFaninFormula F) (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) : NonemptyFaninFormula G := by
  induction level generalizing G with
  | zero =>
      have : G = F := by simpa [formulaDepthFrontier, depthFrontier] using hG
      simpa [this] using h
  | succ level ih =>
      have hb : G ∈ (formulaDepthFrontier level F).bind topChildren := by
        simpa [formulaDepthFrontier_succ_eq_bind_topChildren level F] using hG
      rcases List.mem_bind.mp hb with ⟨M, hM, hGM⟩
      exact nonemptyFanin_topChildren_closed (ih hM) hGM

/-- Syntactic expansion width obeys the recurrence without any simplicity
assumption. -/
theorem nonemptyFanin_widthDNF_syntactic_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (_h : NonemptyFaninFormula F) :
    widthDNF (syntacticDNF F) ≤ formulaRecurrenceWidth F :=
  widthDNF_syntacticDNF_le_recurrenceWidth F

/-- Every normalized DNF view has width at most the formula recurrence width. -/
theorem widthDNF_normalizedDNFView_le_recurrenceWidth {n : Nat}
    (F : BDFormula n) :
    widthDNF (normalizedDNFView F).D ≤ formulaRecurrenceWidth F :=
  Nat.le_trans (widthDNF_normalizedDNFView_le F)
    (widthDNF_syntacticDNF_le_recurrenceWidth F)

theorem nonemptyFanin_widthDNF_normalized_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (_h : NonemptyFaninFormula F) :
    widthDNF (normalizedDNFView F).D ≤ formulaRecurrenceWidth F :=
  widthDNF_normalizedDNFView_le_recurrenceWidth F

/-- The normalized empty-AND view also has width at most zero. -/
theorem emptyAndOne_normalizedWidth_le_zero :
    widthDNF (normalizedDNFView emptyAndOne).D ≤ 0 := by
  simpa [emptyAndOne_recurrenceWidth] using
    widthDNF_normalizedDNFView_le_recurrenceWidth emptyAndOne

/-- The empty AND is deliberately outside the nonempty-fanin consumer class. -/
theorem emptyAndOne_not_nonemptyFanin : ¬ NonemptyFaninFormula emptyAndOne := by
  intro h
  change NonemptyFaninFormula (.and []) at h
  cases h with
  | and hne _ => exact hne rfl

theorem frontier_member_recurrenceWidth_le {n : Nat} (F : BDFormula n)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    formulaRecurrenceWidth G ≤ formulaRecurrenceWidth F := by
  induction level generalizing G with
  | zero =>
      have : G = F := by simpa [formulaDepthFrontier, depthFrontier] using hG
      simp [this]
  | succ level ih =>
      have hb : G ∈ (formulaDepthFrontier level F).bind topChildren := by
        simpa [formulaDepthFrontier_succ_eq_bind_topChildren level F] using hG
      rcases List.mem_bind.mp hb with ⟨M, hM, hGM⟩
      exact Nat.le_trans (formulaRecurrenceWidth_topChild_le M G hGM) (ih hM)

theorem nonemptyFanin_frontier_normalizedWidth_le {n : Nat}
    {F : BDFormula n} (h : NonemptyFaninFormula F) (level : Nat)
    {G : BDFormula n} (hG : G ∈ formulaDepthFrontier level F) :
    widthDNF (normalizedDNFView G).D ≤ formulaRecurrenceWidth F :=
  Nat.le_trans
    (nonemptyFanin_widthDNF_normalized_le_recurrenceWidth
      (nonemptyFanin_frontier_closed h level hG))
    (frontier_member_recurrenceWidth_le F level hG)

/-- A formula packaged through its unconditional normalized DNF view. -/
def normalizedFormulaGate {n : Nat} (F : BDFormula n) : GateSpec n :=
  GateSpec.dnf F (normalizedDNFView F)

@[simp] theorem normalizedFormulaGate_formula {n : Nat} (F : BDFormula n) :
    (normalizedFormulaGate F).formula = F := rfl

def normalizedFrontierGateList {n : Nat} (F : BDFormula n) (level : Nat) :
    List (GateSpec n) :=
  (formulaDepthFrontier level F).map normalizedFormulaGate

def normalizedFrontierMinimalLayer {n : Nat} (F : BDFormula n) (level : Nat)
    (parent : ParentKind) : MinimalLayeredFormula n where
  parent := parent
  gates := normalizedFrontierGateList F level

theorem normalizedFrontierMinimalLayer_originalFormula {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind) :
    (normalizedFrontierMinimalLayer F level parent).originalFormula =
      parent.merge (formulaDepthFrontier level F) := by
  have hm : ((formulaDepthFrontier level F).map normalizedFormulaGate).map
      GateSpec.formula = formulaDepthFrontier level F := by
    induction formulaDepthFrontier level F with
    | nil => rfl
    | cons G rest ih => simp [normalizedFormulaGate_formula, ih]
  exact congrArg (fun xs => parent.merge xs) hm

theorem normalizedFrontierMinimalLayer_gateCount {n : Nat}
    (F : BDFormula n) (level : Nat) (parent : ParentKind) :
    (normalizedFrontierMinimalLayer F level parent).gates.length =
      frontierLayerGateCount F level := by
  simp [normalizedFrontierMinimalLayer, normalizedFrontierGateList,
    frontierLayerGateCount_eq_formulaDepthFrontier_length]

/-- Maximum recurrence width among the gates on one normalized frontier. -/
def frontierMaxRecurrenceWidth {n : Nat} (F : BDFormula n) (level : Nat) : Nat :=
  ((formulaDepthFrontier level F).map formulaRecurrenceWidth).foldr Nat.max 0

/-- Positive frontier-local recurrence-width schedule. -/
def frontierRecurrenceWidthSchedule {n : Nat} (F : BDFormula n) : Nat → Nat :=
  fun level => Nat.max 1 (frontierMaxRecurrenceWidth F level)

theorem frontierRecurrenceWidthSchedule_pos {n : Nat} (F : BDFormula n)
    (level : Nat) : 1 ≤ frontierRecurrenceWidthSchedule F level :=
  Nat.le_max_left _ _

private theorem nat_le_foldr_max_of_mem (xs : List Nat) {x : Nat}
    (hx : x ∈ xs) : x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

private theorem recurrenceWidth_le_frontierMax_of_mem {n : Nat}
    (F : BDFormula n) (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    formulaRecurrenceWidth G ≤ frontierMaxRecurrenceWidth F level := by
  apply nat_le_foldr_max_of_mem
  exact List.mem_map_of_mem formulaRecurrenceWidth hG

/-- Every normalized frontier gate obeys the frontier-local recurrence-width
schedule. -/
theorem normalizedFrontierMinimalLayer_width_le_frontierRecurrenceWidthSchedule
    {n : Nat} {F : BDFormula n} (h : NonemptyFaninFormula F) (level : Nat)
    (parent : ParentKind) (g : GateSpec n)
    (hg : g ∈ (normalizedFrontierMinimalLayer F level parent).gates) :
    widthDNF g.theDNF ≤ frontierRecurrenceWidthSchedule F level := by
  simp only [normalizedFrontierMinimalLayer, normalizedFrontierGateList] at hg
  rcases List.mem_map.mp hg with ⟨G, hG, rfl⟩
  exact Nat.le_trans
    (nonemptyFanin_widthDNF_normalized_le_recurrenceWidth
      (nonemptyFanin_frontier_closed h level hG))
    (Nat.le_trans (recurrenceWidth_le_frontierMax_of_mem F level hG)
      (Nat.le_max_right _ _))

theorem normalizedFrontierMinimalLayer_width_le_schedule {n : Nat}
    {F : BDFormula n} (h : NonemptyFaninFormula F) (level : Nat)
    (parent : ParentKind) (g : GateSpec n)
    (hg : g ∈ (normalizedFrontierMinimalLayer F level parent).gates) :
    widthDNF g.theDNF ≤ recurrenceWidthSchedule F level := by
  simp only [normalizedFrontierMinimalLayer, normalizedFrontierGateList] at hg
  rcases List.mem_map.mp hg with ⟨G, hG, rfl⟩
  exact Nat.le_trans (nonemptyFanin_frontier_normalizedWidth_le h level hG)
    (Nat.le_max_right _ _)

/-- The unchanged final-tree payload, with the normalized frontier layer in
place of the simplicity-indexed layer. -/
def NormalizedViewClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S W : Nat → Nat) (d rounds : Nat) (parent : ParentKind) (level : Nat) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (normalizedFrontierMinimalLayer F level parent).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level * W level)) (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level * W level))
        (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level * W level)) (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (normalizedFrontierMinimalLayer F level parent).originalFormula))

/-- Tight-entry normalized-view consumer.  The only structural premise is the
nonempty-fanin class; width is supplied directly. -/
theorem normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hw : ∀ g ∈ (normalizedFrontierMinimalLayer F level parent).gates,
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * W level) ≤ n) :
    NormalizedViewClassDepthFinalTreeAt F S W d rounds parent level := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level * w)) (rounds + 1)
  let L := normalizedFrontierMinimalLayer F level parent
  have hc : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using normalizedFrontierMinimalLayer_gateCount F level parent
  have hm : 1 ≤ frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level
      (nonemptyFanin_noEmptyFanins hNE) hk
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have hmClass : frontierLayerGateCount F level ≤ S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact formulaClassDepthTreeBudgetFrom F S d level hSize sched sched.length
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (formulaClassDepthTreeBudget S d) sched (freeRestriction n) L
      w hmL hwL hreg ht
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
        (n / (64 * frontierLayerGateCount F level * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule_budgets
      (frontierLayerGateCount F level) (rounds + 1)
        (n / (64 * frontierLayerGateCount F level * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = frontierLayerGateCount F level := by
        have := lastStage_gateCount_of_stageGateCounts_replicate cert hgc T m s hlast
        simpa [hc] using this
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, ?_, heval, ?_, ?_⟩
      · rw [hgc, hc, hlen]
      · rw [hb, hbgeom]
      · simpa [sched, w, hlen] using hsc
      · simpa [hc, sched, w, hlen] using htree
      · simpa [hc] using hlast
      · exact Nat.le_trans hdepth (by
          simpa [formulaClassDepthTreeBudget, hc] using
            Nat.mul_le_mul_right (s - 1) hmClass)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

/-- All-level tight-entry supplied-width consumer: one frontier-local
obligation per level. -/
theorem allNormalizedFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g ∈ (normalizedFrontierMinimalLayer F level parent).gates,
        widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level * W level) ≤ n) :
    ∀ level, level ≤ depth F →
      NormalizedViewClassDepthFinalTreeAt F S W d rounds parent level := by
  intro level hk
  exact normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S W d level rounds parent hDepth hSize hNE hk (hwAll level hk)
      (hwPos level hk) (hnAll level hk)

/-- Coarse-entry replay of the same normalized-view payload. -/
theorem normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hw : ∀ g ∈ (normalizedFrontierMinimalLayer F level parent).gates,
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level) (hwS : W level ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    NormalizedViewClassDepthFinalTreeAt F S W d rounds parent level :=
  normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S W d level rounds parent hDepth hSize hNE hk hw hw1
      (geometricEntryBound_of_class_envelopes
        (frontierLayerGateCount_le_classSize F S d level hSize) hwS hn)

/-- Class-derived wrapper with `W = max 1 recurrenceWidth`. -/
theorem normalizedFrontier_geometricCollapse_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d) (hk : level ≤ depth F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * recurrenceWidthSchedule F level) ≤ n) :
    NormalizedViewClassDepthFinalTreeAt F S (recurrenceWidthSchedule F)
      d rounds parent level := by
  apply normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (recurrenceWidthSchedule F) d level rounds parent hDepth hSize hNE hk
  · exact normalizedFrontierMinimalLayer_width_le_schedule hNE level parent
  · exact recurrenceWidthSchedule_pos F level
  · exact hn

/-- All-level tight-entry route under the recurrence-width schedule. -/
theorem allNormalizedFrontiers_geometricCollapse_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          recurrenceWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      NormalizedViewClassDepthFinalTreeAt F S (recurrenceWidthSchedule F)
        d rounds parent level := by
  refine allNormalizedFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (recurrenceWidthSchedule F) d rounds parent hDepth hSize hNE ?_ ?_ hnAll
  · intro level _
    exact normalizedFrontierMinimalLayer_width_le_schedule hNE level parent
  · intro level _
    exact recurrenceWidthSchedule_pos F level

/-- Class-derived single-level tight-entry wrapper using the frontier-local
recurrence-width schedule. -/
theorem normalizedFrontier_geometricCollapse_finalTree_tightEntry_frontierWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d) (hk : level ≤ depth F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        frontierRecurrenceWidthSchedule F level) ≤ n) :
    NormalizedViewClassDepthFinalTreeAt F S (frontierRecurrenceWidthSchedule F)
      d rounds parent level := by
  apply normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (frontierRecurrenceWidthSchedule F) d level rounds parent
      hDepth hSize hNE hk
  · exact normalizedFrontierMinimalLayer_width_le_frontierRecurrenceWidthSchedule
      hNE level parent
  · exact frontierRecurrenceWidthSchedule_pos F level
  · exact hn

/-- Class-derived all-level tight-entry wrapper using the frontier-local
recurrence-width schedule. -/
theorem allNormalizedFrontiers_geometricCollapse_finalTree_tightEntry_frontierWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          frontierRecurrenceWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      NormalizedViewClassDepthFinalTreeAt F S (frontierRecurrenceWidthSchedule F)
        d rounds parent level := by
  refine allNormalizedFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (frontierRecurrenceWidthSchedule F) d rounds parent hDepth hSize hNE
      ?_ ?_ hnAll
  · intro level _
    exact normalizedFrontierMinimalLayer_width_le_frontierRecurrenceWidthSchedule
      hNE level parent
  · intro level _
    exact frontierRecurrenceWidthSchedule_pos F level

/-! ## Shared-variable witness excluded by the old simplicity route -/

/-- `(x₀ ∨ x₁) ∧ (x₀ ∨ x₂)`. -/
def andOfTwoSharedOrs : BDFormula 3 :=
  .and
    [ .or [.lit { var := ⟨0, by decide⟩, sign := true },
            .lit { var := ⟨1, by decide⟩, sign := true }]
    , .or [.lit { var := ⟨0, by decide⟩, sign := true },
            .lit { var := ⟨2, by decide⟩, sign := true }] ]

theorem andOfTwoSharedOrs_nonemptyFanin :
    NonemptyFaninFormula andOfTwoSharedOrs := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [andOfTwoSharedOrs] at hG
  rcases hG with rfl | rfl <;>
    refine .or (List.cons_ne_nil _ _) ?_ <;>
    intro H hH <;>
    simp at hH <;>
    rcases hH with rfl | rfl <;> exact .lit _

theorem andOfTwoSharedOrs_not_syntacticFormulaSimpleDNF :
    ¬ syntacticFormulaSimpleDNF andOfTwoSharedOrs := by
  intro h
  change syntacticAndListSimpleDNF _ at h
  have hc := h.2.2
  have ht : ([{ var := ⟨0, by decide⟩, sign := true }] : Term 3) ∈
      syntacticDNF
        (.or [.lit { var := ⟨0, by decide⟩, sign := true },
              .lit { var := ⟨1, by decide⟩, sign := true }]) := by
    simp [syntacticDNF, syntacticOrDNF, FormulaSyntacticDNF.literalDNF,
      FormulaSyntacticDNF.falseDNF, orDNF]
  have hu : ([{ var := ⟨0, by decide⟩, sign := true }] : Term 3) ∈
      syntacticAndDNF
        [.or [.lit { var := ⟨0, by decide⟩, sign := true },
              .lit { var := ⟨2, by decide⟩, sign := true }]] := by
    simp [syntacticAndDNF, syntacticDNF, syntacticOrDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.falseDNF,
      FormulaSyntacticDNF.trueDNF, orDNF, andDNF]
  have hs := hc _ ht _ hu
  simp [SimpleTerm] at hs

theorem andOfTwoSharedOrs_recurrenceWidth :
    formulaRecurrenceWidth andOfTwoSharedOrs = 2 := by
  simp [andOfTwoSharedOrs, formulaRecurrenceWidth_and,
    formulaRecurrenceWidth_or, formulaRecurrenceWidth_lit, Nat.max_zero,
    Nat.max_self]

theorem andOfTwoSharedOrs_normalizedWidth_le_two :
    widthDNF (normalizedDNFView andOfTwoSharedOrs).D ≤ 2 := by
  simpa [andOfTwoSharedOrs_recurrenceWidth] using
    nonemptyFanin_widthDNF_normalized_le_recurrenceWidth
      andOfTwoSharedOrs_nonemptyFanin

/-! ## Unconditional ambient `2^20` tight-entry instance -/

private def sharedOrLeft20 : BDFormula 1048576 :=
  .or [.lit { var := ⟨0, by decide⟩, sign := true },
       .lit { var := ⟨1, by decide⟩, sign := true }]

private def sharedOrRight20 : BDFormula 1048576 :=
  .or [.lit { var := ⟨0, by decide⟩, sign := true },
       .lit { var := ⟨2, by decide⟩, sign := true }]

def sharedWitness20 : BDFormula 1048576 :=
  .and [sharedOrLeft20, sharedOrRight20]

private theorem sharedOrLeft20_nonempty : NonemptyFaninFormula sharedOrLeft20 := by
  refine .or (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [sharedOrLeft20] at hG
  rcases hG with rfl | rfl <;> exact .lit _

private theorem sharedOrRight20_nonempty : NonemptyFaninFormula sharedOrRight20 := by
  refine .or (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [sharedOrRight20] at hG
  rcases hG with rfl | rfl <;> exact .lit _

theorem sharedWitness20_nonemptyFanin : NonemptyFaninFormula sharedWitness20 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [sharedWitness20] at hG
  rcases hG with rfl | rfl
  · exact sharedOrLeft20_nonempty
  · exact sharedOrRight20_nonempty

/-- The ambient-`2^20` instance formula itself fails the prior pipeline's
simplicity premise: its raw syntactic expansion contains the repeated-variable
term `[x₀, x₀]`, so the exclusion from the S2142–S2161 syntactic-terminal
simplicity pipeline is pinned for the exact formula carrying the unconditional
instance below, not only for its ambient-3 twin `andOfTwoSharedOrs`. -/
theorem sharedWitness20_not_syntacticFormulaSimpleDNF :
    ¬ syntacticFormulaSimpleDNF sharedWitness20 := by
  intro h
  change syntacticAndListSimpleDNF _ at h
  have hc := h.2.2
  have ht : ([{ var := ⟨0, by decide⟩, sign := true }] : Term 1048576) ∈
      syntacticDNF
        (.or [.lit { var := ⟨0, by decide⟩, sign := true },
              .lit { var := ⟨1, by decide⟩, sign := true }]) := by
    simp [syntacticDNF, syntacticOrDNF, FormulaSyntacticDNF.literalDNF,
      FormulaSyntacticDNF.falseDNF, orDNF]
  have hu : ([{ var := ⟨0, by decide⟩, sign := true }] : Term 1048576) ∈
      syntacticAndDNF
        [.or [.lit { var := ⟨0, by decide⟩, sign := true },
              .lit { var := ⟨2, by decide⟩, sign := true }]] := by
    simp [syntacticAndDNF, syntacticDNF, syntacticOrDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.falseDNF,
      FormulaSyntacticDNF.trueDNF, orDNF, andDNF]
  have hs := hc _ ht _ hu
  simp [SimpleTerm] at hs

theorem sharedWitness20_formulaSize : formulaSize sharedWitness20 = 7 := by
  simp [sharedWitness20, sharedOrLeft20, sharedOrRight20, formulaSize_and,
    formulaSize_or, formulaSize_lit]

theorem sharedWitness20_depth : depth sharedWitness20 = 2 := by
  simp [sharedWitness20, sharedOrLeft20, sharedOrRight20, depth]

theorem sharedWitness20_recurrenceWidth :
    formulaRecurrenceWidth sharedWitness20 = 2 := by
  simp [sharedWitness20, sharedOrLeft20, sharedOrRight20,
    formulaRecurrenceWidth_and, formulaRecurrenceWidth_or,
    formulaRecurrenceWidth_lit, Nat.max_zero, Nat.max_self]

theorem sharedWitness20_frontierGateCount_zero :
    frontierLayerGateCount sharedWitness20 0 = 1 :=
  frontierLayerGateCount_zero sharedWitness20

theorem sharedWitness20_widthSchedule_zero :
    recurrenceWidthSchedule sharedWitness20 0 = 2 := by
  simp [recurrenceWidthSchedule, sharedWitness20_recurrenceWidth]

theorem sharedWitness20_entryProduct_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 2) = 1048576 := by decide

theorem sharedWitness20_tightEntry :
    2 * (64 * frontierLayerGateCount sharedWitness20 0) ^ 2 *
      (64 * frontierLayerGateCount sharedWitness20 0 *
        recurrenceWidthSchedule sharedWitness20 0) ≤ 1048576 := by
  rw [sharedWitness20_frontierGateCount_zero, sharedWitness20_widthSchedule_zero]
  decide

/-- Zero-hypothesis normalized-view instance: frontier count `1`, width `2`,
rounds `2`, and local entry product exactly `2^20`. -/
theorem sharedWitness20_finalTree_level0 :
    NormalizedViewClassDepthFinalTreeAt sharedWitness20 (fun _ => 7)
      (recurrenceWidthSchedule sharedWitness20) 2 2 ParentKind.and 0 :=
  normalizedFrontier_geometricCollapse_finalTree_tightEntry
    sharedWitness20 (fun _ => 7) 2 0 2 ParentKind.and
    sharedWitness20_nonemptyFanin (Nat.le_of_eq sharedWitness20_depth)
    (Nat.le_of_eq sharedWitness20_formulaSize) (Nat.zero_le _)
    sharedWitness20_tightEntry

/-! ## Unconditional ambient `2^26` all-level tight-entry instance -/

private def sharedOrLeft26 : BDFormula 67108864 :=
  .or [.lit { var := ⟨0, by decide⟩, sign := true },
       .lit { var := ⟨1, by decide⟩, sign := true }]

private def sharedOrRight26 : BDFormula 67108864 :=
  .or [.lit { var := ⟨0, by decide⟩, sign := true },
       .lit { var := ⟨2, by decide⟩, sign := true }]

def sharedWitness26 : BDFormula 67108864 :=
  .and [sharedOrLeft26, sharedOrRight26]

theorem sharedWitness26_nonemptyFanin : NonemptyFaninFormula sharedWitness26 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [sharedWitness26, sharedOrLeft26, sharedOrRight26] at hG
  rcases hG with rfl | rfl <;>
    refine .or (List.cons_ne_nil _ _) ?_ <;>
    intro H hH <;> simp at hH <;>
    rcases hH with rfl | rfl <;> exact .lit _

theorem sharedWitness26_not_syntacticFormulaSimpleDNF :
    ¬ syntacticFormulaSimpleDNF sharedWitness26 := by
  intro h
  change syntacticAndListSimpleDNF _ at h
  have hc := h.2.2
  have ht : ([{ var := ⟨0, by decide⟩, sign := true }] : Term 67108864) ∈
      syntacticDNF sharedOrLeft26 := by
    simp [sharedOrLeft26, syntacticDNF, syntacticOrDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.falseDNF, orDNF]
  have hu : ([{ var := ⟨0, by decide⟩, sign := true }] : Term 67108864) ∈
      syntacticAndDNF [sharedOrRight26] := by
    simp [sharedOrRight26, syntacticAndDNF, syntacticDNF, syntacticOrDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.falseDNF,
      FormulaSyntacticDNF.trueDNF, orDNF, andDNF]
  have hs := hc _ ht _ hu
  simp [SimpleTerm] at hs

theorem sharedWitness26_formulaSize : formulaSize sharedWitness26 = 7 := by
  simp [sharedWitness26, sharedOrLeft26, sharedOrRight26, formulaSize_and,
    formulaSize_or, formulaSize_lit]

theorem sharedWitness26_depth : depth sharedWitness26 = 2 := by
  simp [sharedWitness26, sharedOrLeft26, sharedOrRight26, depth]

theorem sharedWitness26_recurrenceWidth :
    formulaRecurrenceWidth sharedWitness26 = 2 := by
  simp [sharedWitness26, sharedOrLeft26, sharedOrRight26,
    formulaRecurrenceWidth_and, formulaRecurrenceWidth_or,
    formulaRecurrenceWidth_lit, Nat.max_zero, Nat.max_self]

theorem sharedWitness26_frontierGateCount_zero :
    frontierLayerGateCount sharedWitness26 0 = 1 :=
  frontierLayerGateCount_zero sharedWitness26

theorem sharedWitness26_frontierGateCount_one :
    frontierLayerGateCount sharedWitness26 1 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem sharedWitness26_frontierGateCount_two :
    frontierLayerGateCount sharedWitness26 2 = 4 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem sharedWitness26_recurrenceWidthSchedule (level : Nat) :
    recurrenceWidthSchedule sharedWitness26 level = 2 := by
  simp [recurrenceWidthSchedule, sharedWitness26_recurrenceWidth]

/-- Exact level-0 entry product at `rounds = 2`, count 1, width 2:
`2*(64*1)^2*(64*1*2) = 1048576 = 2^20`. -/
theorem sharedWitness26_entryProduct_level0_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 2) = 1048576 := by decide

/-- Exact level-1 entry product at `rounds = 2`, count 2, width 2:
`2*(64*2)^2*(64*2*2) = 8388608 = 2^23`. -/
theorem sharedWitness26_entryProduct_level1_eq :
    2 * (64 * 2) ^ 2 * (64 * 2 * 2) = 8388608 := by decide

/-- Exact level-2 entry product at `rounds = 2`, count 4, width 2:
`2*(64*4)^2*(64*4*2) = 67108864 = 2^26`. -/
theorem sharedWitness26_entryProduct_level2_eq :
    2 * (64 * 4) ^ 2 * (64 * 4 * 2) = 67108864 := by decide

/-- Zero-hypothesis all-level normalized-view instance at ambient `2^26`,
`rounds = 2`, and parent kind `and`. -/
theorem sharedWitness26_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth sharedWitness26 →
      NormalizedViewClassDepthFinalTreeAt sharedWitness26 (fun _ => 7)
        (recurrenceWidthSchedule sharedWitness26) 2 2 ParentKind.and level := by
  refine allNormalizedFrontiers_geometricCollapse_finalTree_tightEntry
    sharedWitness26 (fun _ => 7) 2 2 ParentKind.and
      sharedWitness26_nonemptyFanin (Nat.le_of_eq sharedWitness26_depth)
      (Nat.le_of_eq sharedWitness26_formulaSize) ?_
  intro level hlevel
  have hd : depth sharedWitness26 = 2 := sharedWitness26_depth
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · rw [sharedWitness26_frontierGateCount_zero,
      sharedWitness26_recurrenceWidthSchedule 0]
    decide
  · rw [sharedWitness26_frontierGateCount_one,
      sharedWitness26_recurrenceWidthSchedule 1]
    decide
  · rw [sharedWitness26_frontierGateCount_two,
      sharedWitness26_recurrenceWidthSchedule 2]
    decide

/-! ## Frontier-local ambient `2^25` all-level instance (S2165) -/

private def sharedOrLeft25 : BDFormula 33554432 :=
  .or [.lit { var := ⟨0, by decide⟩, sign := true },
       .lit { var := ⟨1, by decide⟩, sign := true }]

private def sharedOrRight25 : BDFormula 33554432 :=
  .or [.lit { var := ⟨0, by decide⟩, sign := true },
       .lit { var := ⟨2, by decide⟩, sign := true }]

def sharedWitness25 : BDFormula 33554432 :=
  .and [sharedOrLeft25, sharedOrRight25]

theorem sharedWitness25_nonemptyFanin : NonemptyFaninFormula sharedWitness25 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [sharedWitness25, sharedOrLeft25, sharedOrRight25] at hG
  rcases hG with rfl | rfl <;>
    refine .or (List.cons_ne_nil _ _) ?_ <;>
    intro H hH <;> simp at hH <;>
    rcases hH with rfl | rfl <;> exact .lit _

theorem sharedWitness25_formulaSize : formulaSize sharedWitness25 = 7 := by
  simp [sharedWitness25, sharedOrLeft25, sharedOrRight25, formulaSize_and,
    formulaSize_or, formulaSize_lit]

theorem sharedWitness25_depth : depth sharedWitness25 = 2 := by
  simp [sharedWitness25, sharedOrLeft25, sharedOrRight25, depth]

theorem sharedWitness25_recurrenceWidth :
    formulaRecurrenceWidth sharedWitness25 = 2 := by
  simp [sharedWitness25, sharedOrLeft25, sharedOrRight25,
    formulaRecurrenceWidth_and, formulaRecurrenceWidth_or,
    formulaRecurrenceWidth_lit, Nat.max_zero, Nat.max_self]

theorem sharedWitness25_frontierGateCount_zero :
    frontierLayerGateCount sharedWitness25 0 = 1 :=
  frontierLayerGateCount_zero sharedWitness25

theorem sharedWitness25_frontierGateCount_one :
    frontierLayerGateCount sharedWitness25 1 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem sharedWitness25_frontierGateCount_two :
    frontierLayerGateCount sharedWitness25 2 = 4 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem sharedWitness25_frontierRecurrenceWidthSchedule_zero :
    frontierRecurrenceWidthSchedule sharedWitness25 0 = 2 := by
  simp [frontierRecurrenceWidthSchedule, frontierMaxRecurrenceWidth,
    sharedWitness25, sharedOrLeft25, sharedOrRight25, formulaDepthFrontier,
    depthFrontier, topChildren, formulaRecurrenceWidth]

theorem sharedWitness25_frontierRecurrenceWidthSchedule_one :
    frontierRecurrenceWidthSchedule sharedWitness25 1 = 1 := by
  simp [frontierRecurrenceWidthSchedule, frontierMaxRecurrenceWidth,
    sharedWitness25, sharedOrLeft25, sharedOrRight25, formulaDepthFrontier,
    depthFrontier, topChildren, formulaRecurrenceWidth]

theorem sharedWitness25_frontierRecurrenceWidthSchedule_two :
    frontierRecurrenceWidthSchedule sharedWitness25 2 = 1 := by
  simp [frontierRecurrenceWidthSchedule, frontierMaxRecurrenceWidth,
    sharedWitness25, sharedOrLeft25, sharedOrRight25, formulaDepthFrontier,
    depthFrontier, topChildren, formulaRecurrenceWidth]

theorem sharedWitness25_recurrenceWidthSchedule (level : Nat) :
    recurrenceWidthSchedule sharedWitness25 level = 2 := by
  simp [recurrenceWidthSchedule, sharedWitness25_recurrenceWidth]

theorem sharedWitness25_frontierSchedule_strict_level1 :
    frontierRecurrenceWidthSchedule sharedWitness25 1 <
      recurrenceWidthSchedule sharedWitness25 1 := by
  rw [sharedWitness25_frontierRecurrenceWidthSchedule_one,
    sharedWitness25_recurrenceWidthSchedule]
  decide

theorem sharedWitness25_frontierSchedule_strict_level2 :
    frontierRecurrenceWidthSchedule sharedWitness25 2 <
      recurrenceWidthSchedule sharedWitness25 2 := by
  rw [sharedWitness25_frontierRecurrenceWidthSchedule_two,
    sharedWitness25_recurrenceWidthSchedule]
  decide

theorem sharedWitness25_entryProduct_level0_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 2) = 1048576 := by decide

theorem sharedWitness25_entryProduct_level1_eq :
    2 * (64 * 2) ^ 2 * (64 * 2 * 1) = 4194304 := by decide

theorem sharedWitness25_entryProduct_level2_eq :
    2 * (64 * 4) ^ 2 * (64 * 4 * 1) = 33554432 := by decide

/-- Zero-hypothesis all-level normalized-view instance at ambient `2^25`, using
only the frontier-local recurrence-width schedule. -/
theorem sharedWitness25_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth sharedWitness25 →
      NormalizedViewClassDepthFinalTreeAt sharedWitness25 (fun _ => 7)
        (frontierRecurrenceWidthSchedule sharedWitness25)
        2 2 ParentKind.and level := by
  refine allNormalizedFrontiers_geometricCollapse_finalTree_tightEntry_frontierWidth
    sharedWitness25 (fun _ => 7) 2 2 ParentKind.and
      sharedWitness25_nonemptyFanin (Nat.le_of_eq sharedWitness25_depth)
      (Nat.le_of_eq sharedWitness25_formulaSize) ?_
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 := by
    rw [sharedWitness25_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl
  · rw [sharedWitness25_frontierGateCount_zero,
      sharedWitness25_frontierRecurrenceWidthSchedule_zero]
    decide
  · rw [sharedWitness25_frontierGateCount_one,
      sharedWitness25_frontierRecurrenceWidthSchedule_one]
    decide
  · rw [sharedWitness25_frontierGateCount_two,
      sharedWitness25_frontierRecurrenceWidthSchedule_two]
    decide

theorem sharedWitness25_ambient_domination : 33554432 < 67108864 := by decide

/-! ## Actual normalized-frontier DNF width schedule (S2166) -/

/-- Maximum actual normalized DNF width among the gates on one frontier. -/
def frontierMaxNormalizedWidth {n : Nat} (F : BDFormula n) (level : Nat) : Nat :=
  ((formulaDepthFrontier level F).map
    (fun G => widthDNF (normalizedDNFView G).D)).foldr Nat.max 0

/-- Positive frontier-local actual normalized-width schedule. -/
def normalizedFrontierWidthSchedule {n : Nat} (F : BDFormula n) : Nat → Nat :=
  fun level => Nat.max 1 (frontierMaxNormalizedWidth F level)

theorem normalizedFrontierWidthSchedule_pos {n : Nat} (F : BDFormula n)
    (level : Nat) : 1 ≤ normalizedFrontierWidthSchedule F level :=
  Nat.le_max_left _ _

/-- Every normalized frontier gate obeys the actual normalized-width schedule.
No class hypothesis is needed: the schedule is definitionally the frontier
maximum of the very widths being bounded. -/
theorem normalizedFrontierMinimalLayer_width_le_normalizedFrontierWidthSchedule
    {n : Nat} (F : BDFormula n) (level : Nat) (parent : ParentKind)
    (g : GateSpec n)
    (hg : g ∈ (normalizedFrontierMinimalLayer F level parent).gates) :
    widthDNF g.theDNF ≤ normalizedFrontierWidthSchedule F level := by
  simp only [normalizedFrontierMinimalLayer, normalizedFrontierGateList] at hg
  rcases List.mem_map.mp hg with ⟨G, hG, rfl⟩
  exact Nat.le_trans
    (nat_le_foldr_max_of_mem _
      (List.mem_map_of_mem (fun G => widthDNF (normalizedDNFView G).D) hG))
    (Nat.le_max_right _ _)

private theorem foldr_max_map_le_foldr_max_map {α : Type} (xs : List α)
    (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).foldr Nat.max 0 ≤ (xs.map g).foldr Nat.max 0 := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons y ys ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (h y (List.mem_cons_self y ys)) (Nat.le_max_left _ _),
          Nat.le_trans (ih fun x hx => h x (List.mem_cons_of_mem y hx))
            (Nat.le_max_right _ _)⟩

private theorem foldr_max_le_of_forall_le {xs : List Nat} {B : Nat}
    (h : ∀ x ∈ xs, x ≤ B) : xs.foldr Nat.max 0 ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le B
  | cons y ys ih =>
      exact Nat.max_le.mpr ⟨h y (List.mem_cons_self y ys),
        ih fun x hx => h x (List.mem_cons_of_mem y hx)⟩

/-- Pointwise, for every raw formula, the actual normalized-frontier schedule
never exceeds the S2165 frontier-local recurrence-width schedule. -/
theorem normalizedFrontierWidthSchedule_le_frontierRecurrenceWidthSchedule
    {n : Nat} (F : BDFormula n) (level : Nat) :
    normalizedFrontierWidthSchedule F level ≤
      frontierRecurrenceWidthSchedule F level :=
  Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (foldr_max_map_le_foldr_max_map _ _ _
      (fun G _ => widthDNF_normalizedDNFView_le_recurrenceWidth G))
      (Nat.le_max_right _ _)⟩

/-- Pointwise, for every raw formula, the S2165 frontier-local schedule never
exceeds the root recurrence-width schedule. -/
theorem frontierRecurrenceWidthSchedule_le_recurrenceWidthSchedule
    {n : Nat} (F : BDFormula n) (level : Nat) :
    frontierRecurrenceWidthSchedule F level ≤ recurrenceWidthSchedule F level := by
  refine Nat.max_le.mpr ⟨recurrenceWidthSchedule_pos F level, ?_⟩
  refine Nat.le_trans (foldr_max_le_of_forall_le ?_)
    (Nat.le_max_right 1 (formulaRecurrenceWidth F))
  intro x hx
  rcases List.mem_map.mp hx with ⟨G, hG, rfl⟩
  exact frontier_member_recurrenceWidth_le F level hG

/-- Pointwise schedule chain endpoint: the actual normalized-frontier schedule
never exceeds the root recurrence-width schedule, for every raw formula. -/
theorem normalizedFrontierWidthSchedule_le_recurrenceWidthSchedule
    {n : Nat} (F : BDFormula n) (level : Nat) :
    normalizedFrontierWidthSchedule F level ≤ recurrenceWidthSchedule F level :=
  Nat.le_trans (normalizedFrontierWidthSchedule_le_frontierRecurrenceWidthSchedule F level)
    (frontierRecurrenceWidthSchedule_le_recurrenceWidthSchedule F level)

/-- Class-derived single-level tight-entry wrapper using the actual
normalized-frontier DNF width schedule. -/
theorem normalizedFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d) (hk : level ≤ depth F)
    (hn : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    NormalizedViewClassDepthFinalTreeAt F S (normalizedFrontierWidthSchedule F)
      d rounds parent level := by
  apply normalizedFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (normalizedFrontierWidthSchedule F) d level rounds parent
      hDepth hSize hNE hk
  · exact fun g hg =>
      normalizedFrontierMinimalLayer_width_le_normalizedFrontierWidthSchedule
        F level parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

/-- Class-derived all-level tight-entry wrapper using the actual
normalized-frontier DNF width schedule. -/
theorem allNormalizedFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      NormalizedViewClassDepthFinalTreeAt F S (normalizedFrontierWidthSchedule F)
        d rounds parent level := by
  refine allNormalizedFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (normalizedFrontierWidthSchedule F) d rounds parent hDepth hSize hNE ?_ ?_ hnAll
  · intro level _
    exact fun g hg =>
      normalizedFrontierMinimalLayer_width_le_normalizedFrontierWidthSchedule
        F level parent g hg
  · intro level _
    exact normalizedFrontierWidthSchedule_pos F level

/-! ## Duplicated-literal nested witness at ambient `2^22` (S2166) -/

private def dupInnerAnd22 : BDFormula 4194304 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

/-- `x₀ ∧ (x₀ ∧ x₀)` at ambient `2^22`: a nested AND whose raw syntactic
expansion is the single duplicated-literal term `[x₀, x₀, x₀]`. -/
def nestedDupWitness22 : BDFormula 4194304 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true }, dupInnerAnd22]

private theorem dupInnerAnd22_nonempty : NonemptyFaninFormula dupInnerAnd22 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupInnerAnd22] at hG
  subst hG
  exact .lit _

theorem nestedDupWitness22_nonemptyFanin :
    NonemptyFaninFormula nestedDupWitness22 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [nestedDupWitness22] at hG
  rcases hG with rfl | rfl
  · exact .lit _
  · exact dupInnerAnd22_nonempty

private theorem nestedDupWitness22_syntacticDNF_eq :
    syntacticDNF nestedDupWitness22 =
      [[{ var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true }]] := by
  simp [nestedDupWitness22, dupInnerAnd22, syntacticDNF, syntacticAndDNF,
    andDNF, FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF]

/-- The raw syntactic expansion of the witness is not simple: its only term is
the repeated-variable term `[x₀, x₀, x₀]`.  Normalization does real work on
this witness. -/
theorem nestedDupWitness22_syntacticDNF_not_simple :
    ¬ SimpleDNF (syntacticDNF nestedDupWitness22) := by
  intro h
  have ht : ([{ var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true }] : Term 4194304) ∈
      syntacticDNF nestedDupWitness22 := by
    rw [nestedDupWitness22_syntacticDNF_eq]
    exact List.mem_cons_self _ _
  have hs := h _ ht
  simp [SimpleTerm] at hs

theorem nestedDupWitness22_formulaSize : formulaSize nestedDupWitness22 = 5 := by
  simp [nestedDupWitness22, dupInnerAnd22, formulaSize_and, formulaSize_lit]

theorem nestedDupWitness22_depth : depth nestedDupWitness22 = 2 := by
  simp [nestedDupWitness22, dupInnerAnd22, depth]

theorem nestedDupWitness22_recurrenceWidth :
    formulaRecurrenceWidth nestedDupWitness22 = 3 := by
  simp [nestedDupWitness22, dupInnerAnd22, formulaRecurrenceWidth_and,
    formulaRecurrenceWidth_lit]

theorem nestedDupWitness22_frontierGateCount_zero :
    frontierLayerGateCount nestedDupWitness22 0 = 1 :=
  frontierLayerGateCount_zero nestedDupWitness22

theorem nestedDupWitness22_frontierGateCount_one :
    frontierLayerGateCount nestedDupWitness22 1 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

/-- The level-1 literal has no top children, so the level-2 frontier is exactly
the inner AND's two literal children. -/
theorem nestedDupWitness22_frontierGateCount_two :
    frontierLayerGateCount nestedDupWitness22 2 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

/-- The witness's normalized DNF view has width exactly `1`: the normalized
DNF is a genuine width-`1` DNF rather than the empty DNF (whose width `0`
would make the schedule value `1` below only the `max 1 0` fallback). -/
theorem nestedDupWitness22_normalizedWidth :
    widthDNF (normalizedDNFView nestedDupWitness22).D = 1 := by
  rw [normalizedDNFView_D, nestedDupWitness22_syntacticDNF_eq]
  rfl

private theorem dupInnerAnd22_syntacticDNF_eq :
    syntacticDNF dupInnerAnd22 =
      [[{ var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true }]] := by
  simp [dupInnerAnd22, syntacticDNF, syntacticAndDNF, andDNF,
    FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF]

private theorem dupInnerAnd22_normalizedWidth :
    widthDNF (normalizedDNFView dupInnerAnd22).D = 1 := by
  rw [normalizedDNFView_D, dupInnerAnd22_syntacticDNF_eq]
  rfl

private theorem litGate22_syntacticDNF_eq :
    syntacticDNF
      (.lit { var := 0, sign := true } : BDFormula 4194304) =
      [[{ var := 0, sign := true }]] := by
  simp [syntacticDNF, FormulaSyntacticDNF.literalDNF]

private theorem litGate22_normalizedWidth :
    widthDNF (normalizedDNFView
      (.lit { var := 0, sign := true } : BDFormula 4194304)).D = 1 := by
  rw [normalizedDNFView_D, litGate22_syntacticDNF_eq]
  rfl

theorem nestedDupWitness22_normalizedFrontierWidthSchedule_zero :
    normalizedFrontierWidthSchedule nestedDupWitness22 0 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    formulaDepthFrontier, depthFrontier, nestedDupWitness22_normalizedWidth]

theorem nestedDupWitness22_normalizedFrontierWidthSchedule_one :
    normalizedFrontierWidthSchedule nestedDupWitness22 1 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    nestedDupWitness22, formulaDepthFrontier, depthFrontier, topChildren,
    litGate22_normalizedWidth, dupInnerAnd22_normalizedWidth]

theorem nestedDupWitness22_normalizedFrontierWidthSchedule_two :
    normalizedFrontierWidthSchedule nestedDupWitness22 2 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    nestedDupWitness22, dupInnerAnd22, formulaDepthFrontier, depthFrontier,
    topChildren, litGate22_normalizedWidth]

theorem nestedDupWitness22_frontierRecurrenceWidthSchedule_zero :
    frontierRecurrenceWidthSchedule nestedDupWitness22 0 = 3 := by
  simp [frontierRecurrenceWidthSchedule, frontierMaxRecurrenceWidth,
    nestedDupWitness22, dupInnerAnd22, formulaDepthFrontier, depthFrontier,
    topChildren, formulaRecurrenceWidth]

theorem nestedDupWitness22_frontierRecurrenceWidthSchedule_one :
    frontierRecurrenceWidthSchedule nestedDupWitness22 1 = 2 := by
  simp [frontierRecurrenceWidthSchedule, frontierMaxRecurrenceWidth,
    nestedDupWitness22, dupInnerAnd22, formulaDepthFrontier, depthFrontier,
    topChildren, formulaRecurrenceWidth]

/-- At level 0 the actual normalized width `1` is strictly below the S2165
frontier recurrence-width schedule value `3` on the same witness. -/
theorem nestedDupWitness22_normalizedSchedule_strict_level0 :
    normalizedFrontierWidthSchedule nestedDupWitness22 0 <
      frontierRecurrenceWidthSchedule nestedDupWitness22 0 := by
  rw [nestedDupWitness22_normalizedFrontierWidthSchedule_zero,
    nestedDupWitness22_frontierRecurrenceWidthSchedule_zero]
  decide

/-- At level 1 the actual normalized width `1` is strictly below the S2165
frontier recurrence-width schedule value `2` on the same witness. -/
theorem nestedDupWitness22_normalizedSchedule_strict_level1 :
    normalizedFrontierWidthSchedule nestedDupWitness22 1 <
      frontierRecurrenceWidthSchedule nestedDupWitness22 1 := by
  rw [nestedDupWitness22_normalizedFrontierWidthSchedule_one,
    nestedDupWitness22_frontierRecurrenceWidthSchedule_one]
  decide

/-- Exact level-0 entry product at `rounds = 2`, count 1, width 1:
`2*(64*1)^2*(64*1*1) = 524288 = 2^19`. -/
theorem nestedDupWitness22_entryProduct_level0_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 1) = 524288 := by decide

/-- Exact level-1 and level-2 entry product at `rounds = 2`, count 2, width 1:
`2*(64*2)^2*(64*2*1) = 4194304 = 2^22`. -/
theorem nestedDupWitness22_entryProduct_level12_eq :
    2 * (64 * 2) ^ 2 * (64 * 2 * 1) = 4194304 := by decide

/-- Zero-hypothesis all-level normalized-view instance at ambient `2^22`, using
the actual normalized-frontier DNF width schedule. -/
theorem nestedDupWitness22_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth nestedDupWitness22 →
      NormalizedViewClassDepthFinalTreeAt nestedDupWitness22 (fun _ => 5)
        (normalizedFrontierWidthSchedule nestedDupWitness22)
        2 2 ParentKind.and level := by
  refine allNormalizedFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    nestedDupWitness22 (fun _ => 5) 2 2 ParentKind.and
      nestedDupWitness22_nonemptyFanin (Nat.le_of_eq nestedDupWitness22_depth)
      (Nat.le_of_eq nestedDupWitness22_formulaSize) ?_
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 := by
    rw [nestedDupWitness22_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl
  · rw [nestedDupWitness22_frontierGateCount_zero,
      nestedDupWitness22_normalizedFrontierWidthSchedule_zero]
    decide
  · rw [nestedDupWitness22_frontierGateCount_one,
      nestedDupWitness22_normalizedFrontierWidthSchedule_one]
    decide
  · rw [nestedDupWitness22_frontierGateCount_two,
      nestedDupWitness22_normalizedFrontierWidthSchedule_two]
    decide

/-- Same-witness entry separation at ambient `2^22`: the S2165 frontier
recurrence-width schedule's level-1 entry product at `rounds = 2` is `2^23`,
which exceeds this ambient, so the S2165 class-derived tight-entry route's
entry hypothesis fails here at level 1 at `rounds = 2` while the actual-width
route enters. -/
theorem nestedDupWitness22_frontierSchedule_entry_fails_level1 :
    ¬ (2 * (64 * frontierLayerGateCount nestedDupWitness22 1) ^ 2 *
      (64 * frontierLayerGateCount nestedDupWitness22 1 *
        frontierRecurrenceWidthSchedule nestedDupWitness22 1) ≤ 4194304) := by
  rw [nestedDupWitness22_frontierGateCount_one,
    nestedDupWitness22_frontierRecurrenceWidthSchedule_one]
  decide

/-- Bookkeeping comparison across different witnesses: this ambient `2^22`
against the S2165 package's ambient `2^25`. -/
theorem nestedDupWitness22_ambient_lt_sharedWitness25_ambient :
    4194304 < 33554432 := by decide

end FormulaRecursiveSyntacticTerminalNormalizedViewRoute
end PvNP
