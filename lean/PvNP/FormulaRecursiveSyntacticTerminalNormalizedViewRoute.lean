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
    {F : BDFormula n} (h : NonemptyFaninFormula F) :
    widthDNF (syntacticDNF F) ≤ formulaRecurrenceWidth F := by
  induction h with
  | tru => simp [syntacticDNF, FormulaSyntacticDNF.trueDNF, widthDNF,
      termWidth, formulaRecurrenceWidth]
  | fls => simp [syntacticDNF, FormulaSyntacticDNF.falseDNF, widthDNF,
      formulaRecurrenceWidth]
  | lit l => simp [syntacticDNF, FormulaSyntacticDNF.literalDNF, widthDNF,
      termWidth, formulaRecurrenceWidth]
  | or _ _ ih =>
      change widthDNF (syntacticOrDNF _) ≤ _
      simpa [formulaRecurrenceWidth_or] using
        widthDNF_syntacticOrDNF_le_foldr_max _ ih
  | and _ _ ih =>
      change widthDNF (syntacticAndDNF _) ≤ _
      simpa [formulaRecurrenceWidth_and] using
        widthDNF_syntacticAndDNF_le_foldr_add _ ih

theorem nonemptyFanin_widthDNF_normalized_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (h : NonemptyFaninFormula F) :
    widthDNF (normalizedDNFView F).D ≤ formulaRecurrenceWidth F :=
  Nat.le_trans (widthDNF_normalizedDNFView_le F)
    (nonemptyFanin_widthDNF_syntactic_le_recurrenceWidth h)

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

end FormulaRecursiveSyntacticTerminalNormalizedViewRoute
end PvNP
