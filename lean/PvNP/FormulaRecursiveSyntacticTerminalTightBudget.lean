import PvNP.FormulaRecursiveSyntacticTerminalWidth
import PvNP.FormulaSyntacticDNF

/-!
# Depth-1 tight frontier width budget (S2153)

This module advances Gate B after S2152 by adding a *restricted* depth-1 tight
frontier width budget that replaces the coarse S2142 intermediate budget
`formulaSize` with constant width `1` whenever `depth F ≤ 1`, without changing
the global `syntacticTerminalFrontierWidthBudget` definition.

For the restricted product/counting family (`lit OR true` at positive depth),
the package discharges actual gate DNF widths against the tight budget,
packages a tight WidthEnvelope-style predicate with `W ≡ 1`, and routes a
specialized final-tree consumer under the unchanged class budget
`t(d,s)=S(d)*(s-1)`.  The geometric schedule uses width budget `1`, which is
the actual intermediate-width improvement over the coarse S2142 schedule.

This is only a restricted depth-1 tight-budget package for the product/counting
(or gated lit-OR-true) family.  It does not change the global S2142 budget, does
not synthesize arbitrary-class width profiles, improve thresholds, prove
arbitrary normalization, arbitrary AC0/bounded-depth collapse, full B4, PHP
switching, Frege/PHP, NP/circuit lower bounds, P-vs-NP, or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalTightBudget

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
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticLayer
open FormulaRecursiveSyntacticSimple
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalConcrete
open FormulaRecursiveSyntacticTerminalExact
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalProduct
open FormulaRecursiveSyntacticTerminalRegime
open FormulaRecursiveSyntacticTerminalStructural
open FormulaRecursiveSyntacticTerminalWidth
open FormulaSyntacticClassGlobalTree
open FormulaSyntacticDNF
open FormulaSyntacticSimpleBridge
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

/-! ## Restricted depth-1 tight frontier width budget -/

/-- Restricted depth-1 tight frontier width budget: width `1` at every level when
`depth F ≤ 1`; otherwise fall back to the standard S2142 budget.  This is a
*parallel* budget; it does not replace `syntacticTerminalFrontierWidthBudget`. -/
def depthOneTightSyntacticTerminalFrontierWidthBudget {n : Nat} (F : BDFormula n)
    (level : Nat) : Nat :=
  if depth F ≤ 1 then 1
  else syntacticTerminalFrontierWidthBudget F level

/-- The tight budget never exceeds the standard S2142 budget. -/
theorem depthOneTight_le_standard {n : Nat} (F : BDFormula n) (level : Nat) :
    depthOneTightSyntacticTerminalFrontierWidthBudget F level ≤
      syntacticTerminalFrontierWidthBudget F level := by
  unfold depthOneTightSyntacticTerminalFrontierWidthBudget
  split_ifs with hdepth
  · exact syntacticTerminalFrontierWidthBudget_pos F level
  · exact Nat.le_refl _

/-- The tight budget is positive. -/
theorem depthOneTight_pos {n : Nat} (F : BDFormula n) (level : Nat) :
    1 ≤ depthOneTightSyntacticTerminalFrontierWidthBudget F level := by
  unfold depthOneTightSyntacticTerminalFrontierWidthBudget
  split_ifs with hdepth
  · exact Nat.le_refl 1
  · exact syntacticTerminalFrontierWidthBudget_pos F level

/-- For depth ≤ 1, the tight budget is constantly `1`. -/
theorem depthOneTight_eq_one_of_depth_le_one {n : Nat} (F : BDFormula n)
    (level : Nat) (hdepth : depth F ≤ 1) :
    depthOneTightSyntacticTerminalFrontierWidthBudget F level = 1 := by
  simp [depthOneTightSyntacticTerminalFrontierWidthBudget, hdepth]

/-- For depth > 1, the tight budget equals the standard S2142 budget. -/
theorem depthOneTight_eq_standard_of_depth_gt_one {n : Nat} (F : BDFormula n)
    (level : Nat) (hdepth : 1 < depth F) :
    depthOneTightSyntacticTerminalFrontierWidthBudget F level =
      syntacticTerminalFrontierWidthBudget F level := by
  have hne : ¬ depth F ≤ 1 := Nat.not_le_of_gt hdepth
  simp [depthOneTightSyntacticTerminalFrontierWidthBudget, hne]

/-- The tight budget is bounded by any class-size envelope covering formula size. -/
theorem depthOneTight_le_classSize {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level : Nat) (hSize : formulaSize F ≤ S d) :
    depthOneTightSyntacticTerminalFrontierWidthBudget F level ≤ S d :=
  Nat.le_trans (depthOneTight_le_standard F level)
    (syntacticTerminalFrontierWidthBudget_le_classSize F S d level hSize)

/-- At intermediate levels of a depth-1 formula with size > 1, the tight budget
is strictly smaller than the standard S2142 intermediate budget `formulaSize`. -/
theorem depthOneTight_lt_standard_of_depth_one_intermediate {n : Nat}
    (F : BDFormula n) (level : Nat)
    (hdepth : depth F = 1) (hlevel : level ≠ depth F)
    (hsize : 1 < formulaSize F) :
    depthOneTightSyntacticTerminalFrontierWidthBudget F level <
      syntacticTerminalFrontierWidthBudget F level := by
  have hle : depth F ≤ 1 := by simp [hdepth]
  have hstd : syntacticTerminalFrontierWidthBudget F level = formulaSize F := by
    simp [syntacticTerminalFrontierWidthBudget, hlevel]
  have htight :
      depthOneTightSyntacticTerminalFrontierWidthBudget F level = 1 :=
    depthOneTight_eq_one_of_depth_le_one F level hle
  simpa [htight, hstd] using hsize

/-! ## Tight width-envelope predicate -/

/-- Tight width envelope: every in-depth tight frontier width budget is bounded
by `W d`.  Parallel to `SyntacticTerminalPackedFamilyWidthEnvelope`, which is
defined against the coarse S2142 budget. -/
def SyntacticTerminalPackedFamilyTightWidthEnvelope
    (F : SyntacticTerminalPackedFamily) (W : Nat → Nat) : Prop :=
  ∀ d level,
    level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      depthOneTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula F d) level ≤ W d

/-- For depth ≤ 1 packed formulas, the constant envelope `W ≡ 1` discharges the
tight width envelope. -/
theorem SyntacticTerminalPackedFamilyTightWidthEnvelope.of_depth_le_one_const_one
    (F : SyntacticTerminalPackedFamily)
    (hdepth : ∀ d, depth (syntacticTerminalPackedFamilyFormula F d) ≤ 1) :
    SyntacticTerminalPackedFamilyTightWidthEnvelope F (fun _ => 1) := by
  intro d level _hk
  simp [depthOneTight_eq_one_of_depth_le_one
    (syntacticTerminalPackedFamilyFormula F d) level (hdepth d)]

/-! ## Specialized final-tree payload under the tight budget -/

open GeneratedRefinedIteratedCertificate in
/-- Final-tree payload for one recursive frontier level under the depth-1 tight
width budget and the unchanged class budget `t(d,s)=S(d)*(s-1)`.  The geometric
schedule uses `depthOneTightSyntacticTerminalFrontierWidthBudget` rather than
the coarse S2142 `syntacticTerminalFrontierWidthBudget`. -/
def DepthOneTightClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S : Nat → Nat) (d rounds : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) (level : Nat) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (syntacticTerminalFrontierLayer F level parent hClass).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          depthOneTightSyntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          depthOneTightSyntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          depthOneTightSyntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (syntacticTerminalFrontierLayer F level parent hClass).originalFormula))

/-- Single-level specialized final-tree consumer under the depth-1 tight width
budget.  Requires an explicit gate-width discharge against the tight budget
(supplied by the restricted family).  Entry ambient still uses the class-size
envelope `S` via `2*(64*S)^rounds*(64*S*S) ≤ n`; the schedule itself uses the
tight width.  The class budget remains `t(d,s)=S(d)*(s-1)`. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithDepthOneTightBudget_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level ≤ depth F)
    (hwL : ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
      widthDNF g.theDNF ≤ depthOneTightSyntacticTerminalFrontierWidthBudget F level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    DepthOneTightClassDepthFinalTreeAt F S d rounds parent hClass level := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  let wBudget := depthOneTightSyntacticTerminalFrontierWidthBudget F level
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level * wBudget)) (rounds + 1)
  let L := syntacticTerminalFrontierLayer F level parent hClass
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using syntacticTerminalFrontierLayer_gateCount F level parent hClass
  have hm : 1 ≤ frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level hClass.2 hk
  have hmL : 1 ≤ L.gates.length := by
    rw [hcount]
    exact hm
  have hwL' : ∀ g, List.Mem g L.gates → widthDNF g.theDNF ≤ wBudget := by
    simpa [L, wBudget] using hwL
  have hw1 : 1 ≤ wBudget := depthOneTight_pos F level
  have hmClass : frontierLayerGateCount F level ≤ S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have hwClass : wBudget ≤ S d :=
    depthOneTight_le_classSize F S d level hSize
  have hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * wBudget) ≤ n :=
    geometricEntryBound_of_class_envelopes hmClass hwClass hn
  have hreg : RegimeFrom (frontierLayerGateCount F level) wBudget
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hnLayer
  have hregL : RegimeFrom L.gates.length wBudget
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
      wBudget hmL hwL' hregL htL
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, wBudget] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level * wBudget))
  have htree' : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1) sched := by
    simpa [hcount, hlen] using htree
  have hbgeom :
      sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, wBudget] using geometricSchedule_budgets
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level * wBudget))
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
          dtDepth T ≤ formulaClassDepthTreeBudget S d level s := by
        exact Nat.le_trans hdepthTree
          (by
            simpa [formulaClassDepthTreeBudget, hcount] using
              Nat.mul_le_mul_right (s - 1) hmClass)
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, hlastCount, heval, hdepthClass, ?_⟩
      · exact hgcRounds
      · rw [hb, hbgeom]
      · simpa [sched, wBudget, hlen] using hsc
      · simpa [sched, wBudget] using htree'
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

/-- All-level specialized final-tree consumer under the depth-1 tight budget. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithDepthOneTightBudget_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
        widthDNF g.theDNF ≤ depthOneTightSyntacticTerminalFrontierWidthBudget F level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      DepthOneTightClassDepthFinalTreeAt F S d rounds parent hClass level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithDepthOneTightBudget_finalTree
      F S d level rounds parent hDepth hSize hClass hk (hwAll level hk) hn

/-! ## Product/counting gate-width discharge against the tight budget -/

/-- Intermediate-level (non-terminal) gates of the depth-1 product formula are
the root itself, whose syntactic DNF has width ≤ 1. -/
private theorem productCounting_succ_intermediate_gate_width_le_one
    (roundsOf : Nat → Nat) (d : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1)))
    (level : Nat)
    (hk : level ≤ depth (productCountingGatedLiteralTrueFormula roundsOf (d + 1)))
    (hlevel : level ≠ depth
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1)))
    (g : GateSpec (productCountingGatedLiteralTrueArity roundsOf (d + 1)))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1))
      level parent hClass).gates) :
    widthDNF g.theDNF ≤ 1 := by
  set F := productCountingGatedLiteralTrueFormula roundsOf (d + 1)
  have hdepthF : depth F = 1 := by
    have h := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
    simp at h
    simpa [F, productCountingGatedLiteralTruePackedFamily,
      syntacticTerminalPackedFamilyFormula] using h
  -- For depth-1 formulas, non-terminal in-depth levels are exactly level 0.
  have hlevel0 : level = 0 := by
    have hk' : level ≤ 1 := by simpa [hdepthF] using hk
    have hne : level ≠ 1 := by simpa [hdepthF] using hlevel
    cases level with
    | zero => rfl
    | succ n =>
        have hn0 : n = 0 := by omega
        subst hn0
        exact absurd rfl hne
  subst hlevel0
  -- At non-terminal levels the selector uses the syntactic frontier layer.
  have hg' : List.Mem g (syntacticFrontierMinimalLayer F 0 parent
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F 0
        hClass.1)).gates := by
    simpa [syntacticTerminalFrontierLayer, hlevel, hdepthF] using hg
  have hg'' : List.Mem g (syntacticFrontierGateList F 0
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F 0
        hClass.1)) := by
    simpa [syntacticFrontierMinimalLayer, syntacticFrontierGateLayer] using hg'
  -- At level 0 the frontier is exactly [F].
  have hfront : formulaDepthFrontier 0 F = [F] := by
    simp [formulaDepthFrontier, depthFrontier]
  -- Recover the unique gate and its DNF.
  rw [syntacticFrontierGateList] at hg''
  rcases List.mem_map.mp hg'' with ⟨G, _hGmem, rfl⟩
  have hG : G.1 = F := by
    have : G.1 ∈ formulaDepthFrontier 0 F := G.2
    simpa [hfront] using this
  -- theDNF of the syntactic-simple gate is syntacticDNF of the formula.
  have hDNF :
      (syntacticSimpleFormulaGate G.1
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F 0
          hClass.1 G.1 G.2)).theDNF =
        syntacticDNF G.1 := by
    simp [syntacticSimpleFormulaGate, syntacticDNFViewOfFormulaSimple,
      syntacticDNFView, GateSpec.theDNF]
  have hwidth : widthDNF (syntacticDNF G.1) ≤ 1 := by
    simpa [hG, F] using
      productCountingGatedLiteralTrueFormula_succ_widthDNF_syntactic_le_one
        roundsOf d
  simpa [hDNF] using hwidth

/-- Every syntactic-terminal frontier gate of the positive-depth product/counting
formula has DNF width ≤ the depth-1 tight budget (i.e. ≤ 1). -/
theorem productCountingGatedLiteralTrueFormula_succ_width_le_depthOneTight
    (roundsOf : Nat → Nat) (d : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1)))
    (level : Nat) (hk : level ≤ depth
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1)))
    (g : GateSpec (productCountingGatedLiteralTrueArity roundsOf (d + 1)))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (productCountingGatedLiteralTrueFormula roundsOf (d + 1))
      level parent hClass).gates) :
    widthDNF g.theDNF ≤
      depthOneTightSyntacticTerminalFrontierWidthBudget
        (productCountingGatedLiteralTrueFormula roundsOf (d + 1)) level := by
  set F := productCountingGatedLiteralTrueFormula roundsOf (d + 1)
  have hdepthF : depth F = 1 := by
    have h := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
    simp at h
    simpa [F, productCountingGatedLiteralTruePackedFamily,
      syntacticTerminalPackedFamilyFormula] using h
  have hle : depth F ≤ 1 := by simp [hdepthF]
  have htight :
      depthOneTightSyntacticTerminalFrontierWidthBudget F level = 1 :=
    depthOneTight_eq_one_of_depth_le_one F level hle
  have hwidth : widthDNF g.theDNF ≤ 1 := by
    by_cases hlevel : level = depth F
    · subst hlevel
      have hg' : List.Mem g (terminalLayerMinimalLayer F parent).gates := by
        simpa [syntacticTerminalFrontierLayer] using hg
      simpa [terminalLayerWidthBudget] using
        terminalLayerMinimalLayer_width_le_budget F parent g hg'
    · exact productCounting_succ_intermediate_gate_width_le_one
        roundsOf d parent hClass level hk hlevel g hg
  simpa [htight] using hwidth

/-- Packed-family form of the gate-width discharge. -/
theorem productCountingGatedLiteralTruePackedFamily_width_le_depthOneTight
    (roundsOf : Nat → Nat) (d : Nat) (hd : 0 < d) (parent : ParentKind)
    (level : Nat)
    (hk : level ≤ depth (syntacticTerminalPackedFamilyFormula
      (productCountingGatedLiteralTruePackedFamily roundsOf) d))
    (g : GateSpec (syntacticTerminalPackedFamilyArity
      (productCountingGatedLiteralTruePackedFamily roundsOf) d))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) d)
      level parent
      (productCountingGatedLiteralTruePackedFamily_class roundsOf d)).gates) :
    widthDNF g.theDNF ≤
      depthOneTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (productCountingGatedLiteralTruePackedFamily roundsOf) d) level := by
  cases d with
  | zero => exact absurd hd (Nat.lt_irrefl 0)
  | succ d =>
      simpa [syntacticTerminalPackedFamilyFormula,
        productCountingGatedLiteralTruePackedFamily,
        syntacticTerminalPackedFamilyArity] using
        productCountingGatedLiteralTrueFormula_succ_width_le_depthOneTight
          roundsOf d parent
          (productCountingGatedLiteralTruePackedFamily_class roundsOf (d + 1))
          level hk g hg

/-! ## Product/counting tight envelope and final-tree route -/

/-- Every positive-depth product/counting formula has depth exactly one, so the
whole family (including depth-zero index) has depth ≤ 1. -/
theorem productCountingGatedLiteralTruePackedFamily_depth_le_one
    (roundsOf : Nat → Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (productCountingGatedLiteralTruePackedFamily roundsOf) d) ≤ 1 := by
  have h := productCountingGatedLiteralTrueDepth roundsOf d
  cases d with
  | zero =>
      simp at h
      simp [h]
  | succ d =>
      simp at h
      simp [h]

/-- Tight budget is constantly `1` on the product/counting family. -/
theorem productCountingGatedLiteralTruePackedFamily_depthOneTight_eq_one
    (roundsOf : Nat → Nat) (d level : Nat) :
    depthOneTightSyntacticTerminalFrontierWidthBudget
      (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) d) level = 1 :=
  depthOneTight_eq_one_of_depth_le_one _
    level (productCountingGatedLiteralTruePackedFamily_depth_le_one roundsOf d)

/-- Tight WidthEnvelope discharge with `W ≡ 1` for the product/counting family. -/
theorem productCountingGatedLiteralTruePackedFamily_tightWidthEnvelope_one
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyTightWidthEnvelope
      (productCountingGatedLiteralTruePackedFamily roundsOf) (fun _ => 1) :=
  SyntacticTerminalPackedFamilyTightWidthEnvelope.of_depth_le_one_const_one _
    (productCountingGatedLiteralTruePackedFamily_depth_le_one roundsOf)

/-- At positive depth, intermediate level 0: tight budget `1` is strictly below
standard intermediate budget `formulaSize = 3`. -/
theorem productCountingGatedLiteralTruePackedFamily_depthOneTight_lt_standard_intermediate_succ
    (roundsOf : Nat → Nat) (d : Nat) :
    depthOneTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1)) 0 <
      syntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1)) 0 := by
  set F := syntacticTerminalPackedFamilyFormula
    (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1)
  have hdepth : depth F = 1 := by
    have h := productCountingGatedLiteralTrueDepth roundsOf (d + 1)
    simp at h
    simpa [F] using h
  have hlevel : (0 : Nat) ≠ depth F := by simp [hdepth]
  have hsize : 1 < formulaSize F := by
    have h3 : formulaSize F = 3 := by
      change formulaSize (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) (d + 1)) = 3
      have hcap := productCountingGatedLiteralTrueSizeCap roundsOf (d + 1)
      simp [syntacticTerminalPackedFamilySizeCap,
        productCountingGatedLiteralTrueSizeCap,
        gatedLiteralTrueThresholdSizeCapIndex] at hcap ⊢
      exact hcap
    simp [h3]
  exact depthOneTight_lt_standard_of_depth_one_intermediate F 0 hdepth hlevel hsize

/-- Ambient entry inequality from structural ambient adequacy. -/
private theorem productCounting_structural_entry
    (roundsOf : Nat → Nat) (d : Nat) :
    2 * (64 * productCountingGatedLiteralTrueClassSize roundsOf d) ^ roundsOf d *
      (64 * productCountingGatedLiteralTrueClassSize roundsOf d *
        productCountingGatedLiteralTrueClassSize roundsOf d) ≤
      syntacticTerminalPackedFamilyArity
        (productCountingGatedLiteralTruePackedFamily roundsOf) d := by
  have hAmb :=
    productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate roundsOf d
  simpa [SyntacticTerminalPackedFamilyStructuralAmbientAdequate,
    syntacticTerminalClassCoarseEntryThreshold] using hAmb

/-- Specialized all-level final-tree route for the product/counting family under
the depth-1 tight width budget and unchanged `t(d,s)=S(d)*(s-1)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithDepthOneTightBudget_finalTree_of_productCounting
    (roundsOf : Nat → Nat) {d : Nat} (hd : 0 < d) (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) d) →
      DepthOneTightClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula
          (productCountingGatedLiteralTruePackedFamily roundsOf) d)
        (productCountingGatedLiteralTrueClassSize roundsOf) d (roundsOf d) parent
        (productCountingGatedLiteralTruePackedFamily_class roundsOf d) level := by
  intro level hk
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithDepthOneTightBudget_finalTree
      (syntacticTerminalPackedFamilyFormula
        (productCountingGatedLiteralTruePackedFamily roundsOf) d)
      (productCountingGatedLiteralTrueClassSize roundsOf)
      d level (roundsOf d) parent ?hDepth ?hSize
      (productCountingGatedLiteralTruePackedFamily_class roundsOf d) hk ?hwL ?hn
  · exact productCountingGatedLiteralTruePackedFamily_depthBound roundsOf d
  · simp [productCountingGatedLiteralTrueClassSize,
      syntacticTerminalPackedFamilySizeCap]
  · intro g hg
    exact productCountingGatedLiteralTruePackedFamily_width_le_depthOneTight
      roundsOf d hd parent level hk g hg
  · exact productCounting_structural_entry roundsOf d

/-- Non-vacuity package: depth-1 tight budget discharges a WidthEnvelope-style
predicate with `W=1` and is strictly below the standard intermediate budget on
a positive-depth restricted family.  The specialized final-tree route is the
named theorem
`allSyntacticTerminalFrontierLayers_geometricCollapseWithDepthOneTightBudget_finalTree_of_productCounting`
under unchanged `t(d,s)=S(d)*(s-1)`. -/
theorem exists_depthOneTightWidthBudget_dischargesEnvelope_finalTreeRoute
    (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ S : Nat → Nat,
        SyntacticTerminalPackedFamilyPosFormulaDepth F ∧
        SyntacticTerminalPackedFamilyClass F ∧
        SyntacticTerminalPackedFamilyDepthBound F ∧
        SyntacticTerminalPackedFamilyClassSizeEnvelope F S ∧
        SyntacticTerminalPackedFamilyTightWidthEnvelope F (fun _ => 1) ∧
        SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
        (∀ d, 0 < d →
          depth (syntacticTerminalPackedFamilyFormula F d) = 1) ∧
        (∀ d level, depthOneTightSyntacticTerminalFrontierWidthBudget
          (syntacticTerminalPackedFamilyFormula F d) level = 1) ∧
        (∀ d, 0 < d →
          depthOneTightSyntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 0 <
            syntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 0) := by
  refine ⟨productCountingGatedLiteralTruePackedFamily roundsOf,
    productCountingGatedLiteralTrueClassSize roundsOf, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact productCountingGatedLiteralTruePackedFamily_posFormulaDepth roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_class roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_depthBound roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_classSizeEnvelope roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_tightWidthEnvelope_one roundsOf
  · exact productCountingGatedLiteralTruePackedFamily_structuralAmbientAdequate roundsOf
  · intro d hd
    exact productCountingGatedLiteralTruePackedFamily_depth_eq_one_of_pos
      roundsOf d hd
  · intro d level
    exact productCountingGatedLiteralTruePackedFamily_depthOneTight_eq_one
      roundsOf d level
  · intro d hd
    cases d with
    | zero => exact absurd hd (Nat.lt_irrefl 0)
    | succ d =>
        exact productCountingGatedLiteralTruePackedFamily_depthOneTight_lt_standard_intermediate_succ
          roundsOf d

end FormulaRecursiveSyntacticTerminalTightBudget
end PvNP
