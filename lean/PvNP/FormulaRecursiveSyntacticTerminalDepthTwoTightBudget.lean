import PvNP.FormulaRecursiveSyntacticTerminalTightBudget

/-!
# Depth-2 tight frontier width budget (S2154)

This module adds a restricted depth-2 tight frontier width budget parallel to the
global S2142 budget.  It is witnessed only by a concrete nested-OR family
`(lit OR true) OR true` at indices `d ≥ 2`, whose actual syntactic frontier DNF
width is bounded by `1` at every in-depth level.  The final-tree consumers keep
the unchanged class budget `formulaClassDepthTreeBudget S d`.

This does not change `syntacticTerminalFrontierWidthBudget`, does not prove an
efficient width profile for arbitrary formulas, and states no threshold, PHP,
Frege, lower-bound, AC0, or P-vs-NP consequence.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalDepthTwoTightBudget

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
open FormulaRecursiveSyntacticTerminalTightBudget
open FormulaRecursiveSyntacticTerminalWidth
open FormulaSyntacticClassGlobalTree
open FormulaSyntacticDNF
open FormulaSyntacticSimpleBridge
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

/-! ## Restricted depth-2 tight frontier width budget -/

/-- Restricted depth-2 tight frontier width budget: width `1` at every level when
`depth F ≤ 2`; otherwise fall back to the depth-1 restricted budget.  This is a
parallel budget and does not replace `syntacticTerminalFrontierWidthBudget`. -/
def depthTwoTightSyntacticTerminalFrontierWidthBudget {n : Nat} (F : BDFormula n)
    (level : Nat) : Nat :=
  if depth F ≤ 2 then 1
  else depthOneTightSyntacticTerminalFrontierWidthBudget F level

/-- The depth-2 tight budget is positive. -/
theorem depthTwoTight_pos {n : Nat} (F : BDFormula n) (level : Nat) :
    1 ≤ depthTwoTightSyntacticTerminalFrontierWidthBudget F level := by
  unfold depthTwoTightSyntacticTerminalFrontierWidthBudget
  split_ifs with hdepth
  · exact Nat.le_refl 1
  · exact depthOneTight_pos F level

/-- The depth-2 tight budget never exceeds the standard S2142 budget. -/
theorem depthTwoTight_le_standard {n : Nat} (F : BDFormula n) (level : Nat) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget F level ≤
      syntacticTerminalFrontierWidthBudget F level := by
  unfold depthTwoTightSyntacticTerminalFrontierWidthBudget
  split_ifs with hdepth
  · exact syntacticTerminalFrontierWidthBudget_pos F level
  · exact depthOneTight_le_standard F level

/-- For depth ≤ 2, the tight budget is constantly `1`. -/
theorem depthTwoTight_eq_one_of_depth_le_two {n : Nat} (F : BDFormula n)
    (level : Nat) (hdepth : depth F ≤ 2) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget F level = 1 := by
  simp [depthTwoTightSyntacticTerminalFrontierWidthBudget, hdepth]

/-- For depth > 2, the depth-2 tight budget agrees with the standard S2142
frontier budget. -/
theorem depthTwoTight_eq_standard_of_depth_gt_two {n : Nat} (F : BDFormula n)
    (level : Nat) (hdepth : 2 < depth F) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget F level =
      syntacticTerminalFrontierWidthBudget F level := by
  have hnot2 : ¬ depth F ≤ 2 := Nat.not_le_of_gt hdepth
  have hgt1 : 1 < depth F := Nat.lt_trans (by decide : 1 < 2) hdepth
  simp [depthTwoTightSyntacticTerminalFrontierWidthBudget, hnot2,
    depthOneTight_eq_standard_of_depth_gt_one F level hgt1]

/-- At nonterminal levels of a depth-at-most-two formula with size > 1, the
depth-2 tight budget is strictly smaller than the standard S2142 intermediate
budget `formulaSize`. -/
theorem depthTwoTight_lt_standard_of_depth_le_two_intermediate {n : Nat}
    (F : BDFormula n) (level : Nat) (hdepth : depth F ≤ 2)
    (hlevel : level ≠ depth F) (hsize : 1 < formulaSize F) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget F level <
      syntacticTerminalFrontierWidthBudget F level := by
  have htight : depthTwoTightSyntacticTerminalFrontierWidthBudget F level = 1 :=
    depthTwoTight_eq_one_of_depth_le_two F level hdepth
  have hstd : syntacticTerminalFrontierWidthBudget F level = formulaSize F := by
    simp [syntacticTerminalFrontierWidthBudget, hlevel]
  simpa [htight, hstd] using hsize

/-- The depth-2 tight budget is bounded by any class-size envelope covering
formula size. -/
theorem depthTwoTight_le_classSize {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level : Nat) (hSize : formulaSize F ≤ S d) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget F level ≤ S d :=
  Nat.le_trans (depthTwoTight_le_standard F level)
    (syntacticTerminalFrontierWidthBudget_le_classSize F S d level hSize)

/-! ## Tight width-envelope predicate -/

/-- Depth-2 tight width envelope: every in-depth restricted depth-2 budget is
bounded by `W d`. -/
def SyntacticTerminalPackedFamilyDepthTwoTightWidthEnvelope
    (F : SyntacticTerminalPackedFamily) (W : Nat → Nat) : Prop :=
  ∀ d level,
    level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      depthTwoTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula F d) level ≤ W d

/-- For depth ≤ 2 packed formulas, the constant envelope `W ≡ 1` discharges the
depth-2 tight width envelope. -/
theorem SyntacticTerminalPackedFamilyDepthTwoTightWidthEnvelope.of_depth_le_two_const_one
    (F : SyntacticTerminalPackedFamily)
    (hdepth : ∀ d, depth (syntacticTerminalPackedFamilyFormula F d) ≤ 2) :
    SyntacticTerminalPackedFamilyDepthTwoTightWidthEnvelope F (fun _ => 1) := by
  intro d level _hk
  simp [depthTwoTight_eq_one_of_depth_le_two
    (syntacticTerminalPackedFamilyFormula F d) level (hdepth d)]

/-! ## Specialized final-tree payload under the depth-2 budget -/

/-- Final-tree payload for one recursive frontier level under the depth-2 tight
width budget and the unchanged class budget `t(d,s)=S(d)*(s-1)`. -/
def DepthTwoTightClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S : Nat → Nat) (d rounds : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) (level : Nat) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (syntacticTerminalFrontierLayer F level parent hClass).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          depthTwoTightSyntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)).length,
    cert.stageGateCounts =
      List.replicate (rounds + 1) (frontierLayerGateCount F level) ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts =
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          depthTwoTightSyntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1)
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level *
          depthTwoTightSyntacticTerminalFrontierWidthBudget F level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (syntacticTerminalFrontierLayer F level parent hClass).originalFormula))

/-- Single-level specialized final-tree consumer under the depth-2 tight budget. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithDepthTwoTightBudget_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level ≤ depth F)
    (hwL : ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
      widthDNF g.theDNF ≤ depthTwoTightSyntacticTerminalFrontierWidthBudget F level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    DepthTwoTightClassDepthFinalTreeAt F S d rounds parent hClass level := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  let wBudget := depthTwoTightSyntacticTerminalFrontierWidthBudget F level
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
  have hw1 : 1 ≤ wBudget := depthTwoTight_pos F level
  have hmClass : frontierLayerGateCount F level ≤ S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have hwClass : wBudget ≤ S d :=
    depthTwoTight_le_classSize F S d level hSize
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

/-- All-level specialized final-tree consumer under the depth-2 tight budget. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithDepthTwoTightBudget_finalTree
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
        widthDNF g.theDNF ≤ depthTwoTightSyntacticTerminalFrontierWidthBudget F level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      DepthTwoTightClassDepthFinalTreeAt F S d rounds parent hClass level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithDepthTwoTightBudget_finalTree
      F S d level rounds parent hDepth hSize hClass hk (hwAll level hk) hn

/-! ## Concrete nested-OR family -/

/-- Size-cap profile for the depth-2 nested-OR witness. -/
def depthTwoTightSizeCapIndex (d : Nat) : Nat :=
  if d < 2 then 1 else 5

/-- Ambient arity for the nested-OR family, using the S2144 product threshold and
the same harmless multiplicity `2` as S2148/S2153. -/
def depthTwoTightArity (roundsOf : Nat → Nat) (d : Nat) : Nat :=
  syntacticTerminalCoarseEntryProduct
    (depthTwoTightSizeCapIndex d) (roundsOf d) * 2

theorem depthTwoTightSizeCapIndex_pos (d : Nat) :
    0 < depthTwoTightSizeCapIndex d := by
  unfold depthTwoTightSizeCapIndex
  split_ifs <;> decide

/-- The nested-OR ambient arity is positive. -/
theorem depthTwoTightArity_pos (roundsOf : Nat → Nat) (d : Nat) :
    0 < depthTwoTightArity roundsOf d := by
  have hprod :
      0 < syntacticTerminalCoarseEntryProduct
        (depthTwoTightSizeCapIndex d) (roundsOf d) := by
    simpa [syntacticTerminalCoarseEntryProduct_eq_threshold] using
      syntacticTerminalClassCoarseEntryThreshold_pos_of_pos
        (depthTwoTightSizeCapIndex_pos d)
  exact Nat.mul_pos hprod (by decide : 0 < 2)

/-- Variable `0` as a positive literal over the nested-OR arity. -/
def depthTwoTightLit0 (roundsOf : Nat → Nat) (d : Nat) :
    BDFormula (depthTwoTightArity roundsOf d) :=
  BDFormula.lit { var := ⟨0, depthTwoTightArity_pos roundsOf d⟩, sign := true }

/-- The inner depth-1 gate `lit OR true`. -/
def depthTwoTightInner (roundsOf : Nat → Nat) (d : Nat) :
    BDFormula (depthTwoTightArity roundsOf d) :=
  BDFormula.or [depthTwoTightLit0 roundsOf d, BDFormula.tru]

/-- The restricted nested-OR formula: a literal at indices `< 2`, and
`(lit OR true) OR true` at every index `d ≥ 2`. -/
def depthTwoTightFormula (roundsOf : Nat → Nat) (d : Nat) :
    BDFormula (depthTwoTightArity roundsOf d) :=
  if d < 2 then depthTwoTightLit0 roundsOf d
  else BDFormula.or [depthTwoTightInner roundsOf d, BDFormula.tru]

/-- The concrete depth-2 tight packed family. -/
def depthTwoTightPackedFamily (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamily :=
  fun d => ⟨depthTwoTightArity roundsOf d, depthTwoTightFormula roundsOf d⟩

/-- Size cap is `1` below index `2` and `5` from index `2` onward. -/
theorem depthTwoTightPackedFamily_sizeCap
    (roundsOf : Nat → Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap
      (depthTwoTightPackedFamily roundsOf) d = depthTwoTightSizeCapIndex d := by
  by_cases hd : d < 2
  · simp [syntacticTerminalPackedFamilySizeCap, syntacticTerminalPackedFamilyFormula,
      depthTwoTightPackedFamily, depthTwoTightFormula, depthTwoTightSizeCapIndex,
      hd, depthTwoTightLit0, formulaSize_lit]
  · simp [syntacticTerminalPackedFamilySizeCap, syntacticTerminalPackedFamilyFormula,
      depthTwoTightPackedFamily, depthTwoTightFormula, depthTwoTightSizeCapIndex,
      hd, depthTwoTightInner, depthTwoTightLit0, formulaSize_or, formulaSize_lit,
      formulaSize]

/-- Depth is `0` below index `2` and exactly `2` from index `2` onward. -/
theorem depthTwoTightPackedFamily_depth
    (roundsOf : Nat → Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (depthTwoTightPackedFamily roundsOf) d) = if d < 2 then 0 else 2 := by
  by_cases hd : d < 2
  · simp [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
      depthTwoTightFormula, hd, depthTwoTightLit0, depth]
  · simp [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
      depthTwoTightFormula, hd, depthTwoTightInner, depthTwoTightLit0, depth]

/-- At indices `d ≥ 2`, the concrete formula has exact depth `2`. -/
theorem depthTwoTightPackedFamily_depth_eq_two_of_two_le
    (roundsOf : Nat → Nat) (d : Nat) (hd : 2 ≤ d) :
    depth (syntacticTerminalPackedFamilyFormula
      (depthTwoTightPackedFamily roundsOf) d) = 2 := by
  have hnot : ¬ d < 2 := Nat.not_lt.mpr hd
  simp [depthTwoTightPackedFamily_depth, hnot]

/-- The nested-OR family is in the syntactic-terminal class. -/
theorem depthTwoTightPackedFamily_class (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClass (depthTwoTightPackedFamily roundsOf) := by
  intro d
  constructor
  · by_cases hd : d < 2
    · simp [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
        depthTwoTightFormula, hd, depthTwoTightLit0, syntacticFormulaSimpleDNF,
        syntacticOrListSimpleDNF]
    · simp [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
        depthTwoTightFormula, hd, depthTwoTightInner, depthTwoTightLit0,
        syntacticFormulaSimpleDNF, syntacticOrListSimpleDNF]
  · by_cases hd : d < 2
    · simp [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
        depthTwoTightFormula, hd, depthTwoTightLit0]
      exact NoEmptyFanins.lit _
    · simp [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
        depthTwoTightFormula, hd, depthTwoTightInner, depthTwoTightLit0]
      refine NoEmptyFanins.or (by simp) ?_
      intro child hchild
      simp at hchild
      rcases hchild with hchild | hchild
      · subst child
        refine NoEmptyFanins.or (by simp) ?_
        intro child hchild
        simp at hchild
        rcases hchild with hchild | hchild
        · subst child
          exact NoEmptyFanins.lit _
        · subst child
          exact NoEmptyFanins.tru
      · subst child
        exact NoEmptyFanins.tru

/-- The nested-OR family satisfies the depth-index bound. -/
theorem depthTwoTightPackedFamily_depthBound (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyDepthBound (depthTwoTightPackedFamily roundsOf) := by
  intro d
  have h := depthTwoTightPackedFamily_depth roundsOf d
  by_cases hd : d < 2
  · simp [h, hd]
  · have h2 : 2 ≤ d := Nat.le_of_not_gt hd
    simpa [h, hd] using h2

/-- Class-size envelope by the concrete size cap. -/
theorem depthTwoTightPackedFamily_classSizeEnvelope (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClassSizeEnvelope
      (depthTwoTightPackedFamily roundsOf) (depthTwoTightSizeCapIndex) := by
  intro d
  simp [depthTwoTightPackedFamily_sizeCap]

/-- The family is a product/counting source with constant multiplicity `2`. -/
theorem depthTwoTightPackedFamily_productCountingSource (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyProductCountingSource
      (depthTwoTightPackedFamily roundsOf) roundsOf productCountingMultiplicityTwo := by
  intro d
  refine ⟨Nat.zero_lt_two, ?_⟩
  simp [productCountingMultiplicityTwo, syntacticTerminalPackedFamilyArity,
    depthTwoTightPackedFamily, depthTwoTightArity,
    depthTwoTightPackedFamily_sizeCap]

/-- Structural ambient adequacy for the concrete size cap. -/
theorem depthTwoTightPackedFamily_structuralAmbientAdequate
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralAmbientAdequate
      (depthTwoTightPackedFamily roundsOf) depthTwoTightSizeCapIndex roundsOf := by
  intro d
  have hAmb := SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource
    (depthTwoTightPackedFamily_productCountingSource roundsOf) d
  simpa [depthTwoTightPackedFamily_sizeCap] using hAmb

/-- All formulas in the family have depth at most two. -/
theorem depthTwoTightPackedFamily_depth_le_two (roundsOf : Nat → Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (depthTwoTightPackedFamily roundsOf) d) ≤ 2 := by
  have h := depthTwoTightPackedFamily_depth roundsOf d
  by_cases hd : d < 2 <;> simp [h, hd]

/-- The depth-2 tight budget is constantly `1` on the nested-OR family. -/
theorem depthTwoTightPackedFamily_budget_eq_one
    (roundsOf : Nat → Nat) (d level : Nat) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget
      (syntacticTerminalPackedFamilyFormula
        (depthTwoTightPackedFamily roundsOf) d) level = 1 :=
  depthTwoTight_eq_one_of_depth_le_two _ level
    (depthTwoTightPackedFamily_depth_le_two roundsOf d)

/-- At depth-two indices, level `0` sees a strict improvement over the standard
intermediate budget. -/
theorem depthTwoTightPackedFamily_depthTwoTight_lt_standard_intermediate_zero
    (roundsOf : Nat → Nat) (d : Nat) (hd : 2 ≤ d) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (depthTwoTightPackedFamily roundsOf) d) 0 <
      syntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (depthTwoTightPackedFamily roundsOf) d) 0 := by
  set F := syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d
  have hdepthEq : depth F = 2 := by
    simpa [F] using depthTwoTightPackedFamily_depth_eq_two_of_two_le roundsOf d hd
  have hdepth : depth F ≤ 2 := by simp [hdepthEq]
  have hlevel : (0 : Nat) ≠ depth F := by simp [hdepthEq]
  have hsize : 1 < formulaSize F := by
    have hcap := depthTwoTightPackedFamily_sizeCap roundsOf d
    have hnot : ¬ d < 2 := Nat.not_lt.mpr hd
    simp [F, syntacticTerminalPackedFamilySizeCap, depthTwoTightSizeCapIndex,
      hnot] at hcap
    simp [hcap]
  exact depthTwoTight_lt_standard_of_depth_le_two_intermediate F 0 hdepth hlevel hsize

/-- At depth-two indices, level `1` also sees a strict improvement over the
standard intermediate budget. -/
theorem depthTwoTightPackedFamily_depthTwoTight_lt_standard_intermediate_one
    (roundsOf : Nat → Nat) (d : Nat) (hd : 2 ≤ d) :
    depthTwoTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (depthTwoTightPackedFamily roundsOf) d) 1 <
      syntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (depthTwoTightPackedFamily roundsOf) d) 1 := by
  set F := syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d
  have hdepthEq : depth F = 2 := by
    simpa [F] using depthTwoTightPackedFamily_depth_eq_two_of_two_le roundsOf d hd
  have hdepth : depth F ≤ 2 := by simp [hdepthEq]
  have hlevel : (1 : Nat) ≠ depth F := by simp [hdepthEq]
  have hsize : 1 < formulaSize F := by
    have hcap := depthTwoTightPackedFamily_sizeCap roundsOf d
    have hnot : ¬ d < 2 := Nat.not_lt.mpr hd
    simp [F, syntacticTerminalPackedFamilySizeCap, depthTwoTightSizeCapIndex,
      hnot] at hcap
    simp [hcap]
  exact depthTwoTight_lt_standard_of_depth_le_two_intermediate F 1 hdepth hlevel hsize

/-- Depth-2 tight WidthEnvelope discharge with `W ≡ 1`. -/
theorem depthTwoTightPackedFamily_tightWidthEnvelope_one
    (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyDepthTwoTightWidthEnvelope
      (depthTwoTightPackedFamily roundsOf) (fun _ => 1) :=
  SyntacticTerminalPackedFamilyDepthTwoTightWidthEnvelope.of_depth_le_two_const_one _
    (depthTwoTightPackedFamily_depth_le_two roundsOf)

private theorem widthDNF_depthTwoTightLit0_syntactic_le_one
    (roundsOf : Nat → Nat) (d : Nat) :
    widthDNF (syntacticDNF (depthTwoTightLit0 roundsOf d)) ≤ 1 := by
  simp [depthTwoTightLit0, syntacticDNF, FormulaSyntacticDNF.literalDNF,
    widthDNF, termWidth]

private theorem widthDNF_depthTwoTightTru_syntactic_le_one
    (roundsOf : Nat → Nat) (d : Nat) :
    widthDNF (syntacticDNF (BDFormula.tru : BDFormula (depthTwoTightArity roundsOf d))) ≤ 1 := by
  have h : widthDNF (syntacticDNF
      (BDFormula.tru : BDFormula (depthTwoTightArity roundsOf d))) = 0 := by
    simp [syntacticDNF, FormulaSyntacticDNF.trueDNF, widthDNF, termWidth]
  exact Nat.le_trans (le_of_eq h) (by decide : (0 : Nat) ≤ 1)

/-- The inner `lit OR true` gate has syntactic DNF width at most one. -/
theorem depthTwoTightInner_widthDNF_syntactic_le_one
    (roundsOf : Nat → Nat) (d : Nat) :
    widthDNF (syntacticDNF (depthTwoTightInner roundsOf d)) ≤ 1 := by
  have hLit := widthDNF_depthTwoTightLit0_syntactic_le_one roundsOf d
  have hTru := widthDNF_depthTwoTightTru_syntactic_le_one roundsOf d
  have hNil : widthDNF (syntacticOrDNF
      ([] : List (BDFormula (depthTwoTightArity roundsOf d)))) ≤ 1 := by
    simp [syntacticOrDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
  have hRest : widthDNF (syntacticOrDNF
      ([BDFormula.tru] : List (BDFormula (depthTwoTightArity roundsOf d)))) ≤ 1 := by
    simp only [syntacticOrDNF]
    exact widthDNF_orDNF_le hTru hNil
  simp only [depthTwoTightInner, syntacticDNF, syntacticOrDNF]
  exact widthDNF_orDNF_le hLit hRest

/-- The full nested-OR formula has syntactic DNF width at most one at `d ≥ 2`. -/
theorem depthTwoTightFormula_widthDNF_syntactic_le_one_of_two_le
    (roundsOf : Nat → Nat) (d : Nat) (hd : 2 ≤ d) :
    widthDNF (syntacticDNF (depthTwoTightFormula roundsOf d)) ≤ 1 := by
  have hnot : ¬ d < 2 := Nat.not_lt.mpr hd
  have hInner := depthTwoTightInner_widthDNF_syntactic_le_one roundsOf d
  have hTru := widthDNF_depthTwoTightTru_syntactic_le_one roundsOf d
  have hNil : widthDNF (syntacticOrDNF
      ([] : List (BDFormula (depthTwoTightArity roundsOf d)))) ≤ 1 := by
    simp [syntacticOrDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
  have hRest : widthDNF (syntacticOrDNF
      ([BDFormula.tru] : List (BDFormula (depthTwoTightArity roundsOf d)))) ≤ 1 := by
    simp only [syntacticOrDNF]
    exact widthDNF_orDNF_le hTru hNil
  simp only [depthTwoTightFormula, hnot, syntacticDNF, syntacticOrDNF]
  exact widthDNF_orDNF_le hInner hRest

private theorem depthTwoTight_succ_intermediate_gate_width_le_one
    (roundsOf : Nat → Nat) (d : Nat) (hd : 2 ≤ d) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass (depthTwoTightFormula roundsOf d))
    (level : Nat) (hk : level ≤ depth (depthTwoTightFormula roundsOf d))
    (hlevel : level ≠ depth (depthTwoTightFormula roundsOf d))
    (g : GateSpec (depthTwoTightArity roundsOf d))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (depthTwoTightFormula roundsOf d) level parent hClass).gates) :
    widthDNF g.theDNF ≤ 1 := by
  have hnot : ¬ d < 2 := Nat.not_lt.mpr hd
  have hdepthF : depth (depthTwoTightFormula roundsOf d) = 2 := by
    simp [depthTwoTightFormula, hnot, depthTwoTightInner, depthTwoTightLit0, depth]
  have hlevel_cases : level = 0 ∨ level = 1 := by omega
  have hg' : List.Mem g (syntacticFrontierMinimalLayer
      (depthTwoTightFormula roundsOf d) level parent
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF
        (depthTwoTightFormula roundsOf d) level hClass.1)).gates := by
    simpa [syntacticTerminalFrontierLayer, hlevel] using hg
  have hg'' : List.Mem g (syntacticFrontierGateList
      (depthTwoTightFormula roundsOf d) level
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF
        (depthTwoTightFormula roundsOf d) level hClass.1)) := by
    simpa [syntacticFrontierMinimalLayer, syntacticFrontierGateLayer] using hg'
  rw [syntacticFrontierGateList] at hg''
  rcases List.mem_map.mp hg'' with ⟨G, hGmem, rfl⟩
  have hDNF :
      (syntacticSimpleFormulaGate G.1
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF
          (depthTwoTightFormula roundsOf d) level hClass.1 G.1 G.2)).theDNF =
        syntacticDNF G.1 := by
    simp [syntacticSimpleFormulaGate, syntacticDNFViewOfFormulaSimple,
      syntacticDNFView, GateSpec.theDNF]
  rcases hlevel_cases with rfl | hlevel1
  · have hG : G.1 = depthTwoTightFormula roundsOf d := by
      have : G.1 ∈ formulaDepthFrontier 0 (depthTwoTightFormula roundsOf d) := G.2
      simpa [formulaDepthFrontier, depthFrontier] using this
    have hwidth := depthTwoTightFormula_widthDNF_syntactic_le_one_of_two_le
      roundsOf d hd
    simpa [hDNF, hG] using hwidth
  · subst hlevel1
    have hGor : G.1 = depthTwoTightInner roundsOf d ∨
        G.1 = (BDFormula.tru : BDFormula (depthTwoTightArity roundsOf d)) := by
      have : G.1 ∈ formulaDepthFrontier 1 (depthTwoTightFormula roundsOf d) := G.2
      simp [formulaDepthFrontier, depthFrontier, FormulaTruthTableView.topChildren,
        depthTwoTightFormula,
        hnot] at this
      exact this
    rcases hGor with hG | hG
    · have hwidth := depthTwoTightInner_widthDNF_syntactic_le_one roundsOf d
      simpa [hDNF, hG] using hwidth
    · have hwidth := widthDNF_depthTwoTightTru_syntactic_le_one roundsOf d
      simpa [hDNF, hG] using hwidth

/-- Every syntactic-terminal frontier gate of the concrete depth-2 family at
indices `d ≥ 2` has actual DNF width at most the depth-2 tight budget (`1`). -/
theorem depthTwoTightPackedFamily_width_le_depthTwoTight
    (roundsOf : Nat → Nat) (d : Nat) (hd : 2 ≤ d) (parent : ParentKind)
    (level : Nat)
    (hk : level ≤ depth (syntacticTerminalPackedFamilyFormula
      (depthTwoTightPackedFamily roundsOf) d))
    (g : GateSpec (syntacticTerminalPackedFamilyArity
      (depthTwoTightPackedFamily roundsOf) d))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
      level parent (depthTwoTightPackedFamily_class roundsOf d)).gates) :
    widthDNF g.theDNF ≤
      depthTwoTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
        level := by
  have hnot : ¬ d < 2 := Nat.not_lt.mpr hd
  have hbudget :
      depthTwoTightSyntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
        level = 1 := depthTwoTightPackedFamily_budget_eq_one roundsOf d level
  have hwidth : widthDNF g.theDNF ≤ 1 := by
    by_cases hlevel : level = depth (syntacticTerminalPackedFamilyFormula
        (depthTwoTightPackedFamily roundsOf) d)
    · subst hlevel
      have hg' : List.Mem g (terminalLayerMinimalLayer
          (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
          parent).gates := by
        simpa [syntacticTerminalFrontierLayer] using hg
      simpa [terminalLayerWidthBudget] using
        terminalLayerMinimalLayer_width_le_budget _ parent g hg'
    · simpa [syntacticTerminalPackedFamilyFormula, syntacticTerminalPackedFamilyArity,
        depthTwoTightPackedFamily, depthTwoTightFormula, hnot] using
        depthTwoTight_succ_intermediate_gate_width_le_one roundsOf d hd parent
          (by simpa [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
            depthTwoTightFormula, hnot] using depthTwoTightPackedFamily_class roundsOf d)
          level (by simpa [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
            depthTwoTightFormula, hnot] using hk)
          (by simpa [syntacticTerminalPackedFamilyFormula, depthTwoTightPackedFamily,
            depthTwoTightFormula, hnot] using hlevel) g hg
  simpa [hbudget] using hwidth

private theorem depthTwoTight_structural_entry
    (roundsOf : Nat → Nat) (d : Nat) :
    2 * (64 * depthTwoTightSizeCapIndex d) ^ roundsOf d *
      (64 * depthTwoTightSizeCapIndex d * depthTwoTightSizeCapIndex d) ≤
      syntacticTerminalPackedFamilyArity (depthTwoTightPackedFamily roundsOf) d := by
  have hAmb := depthTwoTightPackedFamily_structuralAmbientAdequate roundsOf d
  simpa [SyntacticTerminalPackedFamilyStructuralAmbientAdequate,
    syntacticTerminalClassCoarseEntryThreshold] using hAmb

/-- Specialized all-level final-tree route for the concrete depth-2 nested-OR
family at every index `d ≥ 2`, under the unchanged class budget. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithDepthTwoTightBudget_finalTree_of_depthTwoTight
    (roundsOf : Nat → Nat) {d : Nat} (hd : 2 ≤ d) (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (depthTwoTightPackedFamily roundsOf) d) →
      DepthTwoTightClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
        depthTwoTightSizeCapIndex d (roundsOf d) parent
        (depthTwoTightPackedFamily_class roundsOf d) level := by
  intro level hk
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithDepthTwoTightBudget_finalTree
      (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
      depthTwoTightSizeCapIndex d level (roundsOf d) parent ?hDepth ?hSize
      (depthTwoTightPackedFamily_class roundsOf d) hk ?hwL ?hn
  · exact depthTwoTightPackedFamily_depthBound roundsOf d
  · exact depthTwoTightPackedFamily_classSizeEnvelope roundsOf d
  · intro g hg
    exact depthTwoTightPackedFamily_width_le_depthTwoTight
      roundsOf d hd parent level hk g hg
  · exact depthTwoTight_structural_entry roundsOf d

/-- Existence package for the restricted S2154 depth-2 tight budget route. -/
theorem exists_depthTwoTightWidthBudget_dischargesEnvelope_finalTreeRoute
    (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ S : Nat → Nat,
        SyntacticTerminalPackedFamilyClass F ∧
        SyntacticTerminalPackedFamilyDepthBound F ∧
        SyntacticTerminalPackedFamilyClassSizeEnvelope F S ∧
        SyntacticTerminalPackedFamilyDepthTwoTightWidthEnvelope F (fun _ => 1) ∧
        SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
        (∀ d, 2 ≤ d → depth (syntacticTerminalPackedFamilyFormula F d) = 2) ∧
        (∀ d level, depthTwoTightSyntacticTerminalFrontierWidthBudget
          (syntacticTerminalPackedFamilyFormula F d) level = 1) ∧
        (∀ d, 2 ≤ d →
          depthTwoTightSyntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 0 <
            syntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 0 ∧
          depthTwoTightSyntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 1 <
            syntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 1) ∧
         (∀ d, 2 ≤ d →
           ∀ parent level,
             level ≤ depth (syntacticTerminalPackedFamilyFormula
               (depthTwoTightPackedFamily roundsOf) d) →
               ∀ g, List.Mem g (syntacticTerminalFrontierLayer
                 (syntacticTerminalPackedFamilyFormula (depthTwoTightPackedFamily roundsOf) d)
                 level parent ((depthTwoTightPackedFamily_class roundsOf) d)).gates →
                 widthDNF g.theDNF ≤ 1) ∧
         (∀ d, 2 ≤ d →
           ∀ parent level,
             level ≤ depth (syntacticTerminalPackedFamilyFormula
               (depthTwoTightPackedFamily roundsOf) d) →
               DepthTwoTightClassDepthFinalTreeAt
                 (syntacticTerminalPackedFamilyFormula
                   (depthTwoTightPackedFamily roundsOf) d)
                 depthTwoTightSizeCapIndex d (roundsOf d) parent
                 ((depthTwoTightPackedFamily_class roundsOf) d) level) := by
  refine ⟨depthTwoTightPackedFamily roundsOf, depthTwoTightSizeCapIndex,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact depthTwoTightPackedFamily_class roundsOf
  · exact depthTwoTightPackedFamily_depthBound roundsOf
  · exact depthTwoTightPackedFamily_classSizeEnvelope roundsOf
  · exact depthTwoTightPackedFamily_tightWidthEnvelope_one roundsOf
  · exact depthTwoTightPackedFamily_structuralAmbientAdequate roundsOf
  · intro d hd
    exact depthTwoTightPackedFamily_depth_eq_two_of_two_le roundsOf d hd
  · intro d level
    exact depthTwoTightPackedFamily_budget_eq_one roundsOf d level
  · intro d hd
    exact ⟨depthTwoTightPackedFamily_depthTwoTight_lt_standard_intermediate_zero
        roundsOf d hd,
      depthTwoTightPackedFamily_depthTwoTight_lt_standard_intermediate_one
        roundsOf d hd⟩
  · intro d hd parent level hk g hg
    have h := depthTwoTightPackedFamily_width_le_depthTwoTight
      roundsOf d hd parent level hk g hg
    simpa [depthTwoTightPackedFamily_budget_eq_one roundsOf d level] using h
  · intro d hd parent level hk
    exact
      allSyntacticTerminalFrontierLayers_geometricCollapseWithDepthTwoTightBudget_finalTree_of_depthTwoTight
        roundsOf hd parent level hk

end FormulaRecursiveSyntacticTerminalDepthTwoTightBudget
end PvNP
