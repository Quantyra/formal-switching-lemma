import PvNP.FormulaRecursiveSyntacticTerminalDepthTwoTightBudget
import PvNP.FormulaRecursiveDecomposition

/-!
# Bounded-shallow tight frontier width budget (S2155)

This module advances Gate B after S2154 by adding a *k-indexed* parallel
frontier width budget that is constantly `1` whenever `depth F ≤ k`, falling
back to the standard S2142 budget otherwise.  It does not change the global
`syntacticTerminalFrontierWidthBudget`.

The package also introduces a generic supplied-width syntactic-terminal
final-tree consumer (schedule width taken from a caller-supplied `W level`), a
bounded-shallow specialization, and a recursive fixed-arity nested-OR family
`F₀ = lit`, `F_{r+1} = or[F_r, tru]` witnessing the tight budget for every `k`.

This is only a restricted nested-OR / bounded-shallow package.  It does not
change the global S2142 budget, does not improve thresholds, does not prove
arbitrary-class width profiles, full B4, PHP switching, Frege/PHP, NP/circuit
lower bounds, or P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveClassProfile
open FormulaRecursiveDecomposition
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveNonempty
open FormulaRecursiveSizeBound
open FormulaRecursiveSyntacticLayer
open FormulaRecursiveSyntacticSimple
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalConcrete
open FormulaRecursiveSyntacticTerminalDepthTwoTightBudget
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

/-! ## k-indexed parallel bounded-shallow tight frontier width budget -/

/-- Restricted k-indexed tight frontier width budget: width `1` at every level
when `depth F ≤ k`; otherwise fall back to the standard S2142 budget.  This is
a parallel budget and does not replace `syntacticTerminalFrontierWidthBudget`. -/
def boundedShallowTightSyntacticTerminalFrontierWidthBudget {n : Nat}
    (k : Nat) (F : BDFormula n) (level : Nat) : Nat :=
  if depth F ≤ k then 1
  else syntacticTerminalFrontierWidthBudget F level

/-- The bounded-shallow tight budget is positive. -/
theorem boundedShallowTight_pos {n : Nat} (k : Nat) (F : BDFormula n)
    (level : Nat) :
    1 ≤ boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level := by
  unfold boundedShallowTightSyntacticTerminalFrontierWidthBudget
  split_ifs with hdepth
  · exact Nat.le_refl 1
  · exact syntacticTerminalFrontierWidthBudget_pos F level

/-- The bounded-shallow tight budget never exceeds the standard S2142 budget. -/
theorem boundedShallowTight_le_standard {n : Nat} (k : Nat) (F : BDFormula n)
    (level : Nat) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level ≤
      syntacticTerminalFrontierWidthBudget F level := by
  unfold boundedShallowTightSyntacticTerminalFrontierWidthBudget
  split_ifs with hdepth
  · exact syntacticTerminalFrontierWidthBudget_pos F level
  · exact Nat.le_refl _

/-- For depth ≤ k, the tight budget is constantly `1`. -/
theorem boundedShallowTight_eq_one_of_depth_le {n : Nat} (k : Nat)
    (F : BDFormula n) (level : Nat) (hdepth : depth F ≤ k) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level = 1 := by
  simp [boundedShallowTightSyntacticTerminalFrontierWidthBudget, hdepth]

/-- For depth > k, the tight budget agrees with the standard S2142 frontier
budget. -/
theorem boundedShallowTight_eq_standard_of_depth_gt {n : Nat} (k : Nat)
    (F : BDFormula n) (level : Nat) (hdepth : k < depth F) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level =
      syntacticTerminalFrontierWidthBudget F level := by
  have hnot : ¬ depth F ≤ k := Nat.not_le_of_gt hdepth
  simp [boundedShallowTightSyntacticTerminalFrontierWidthBudget, hnot]

/-- The bounded-shallow tight budget is bounded by any class-size envelope
covering formula size. -/
theorem boundedShallowTight_le_classSize {n : Nat} (k : Nat) (F : BDFormula n)
    (S : Nat → Nat) (d level : Nat) (hSize : formulaSize F ≤ S d) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level ≤ S d :=
  Nat.le_trans (boundedShallowTight_le_standard k F level)
    (syntacticTerminalFrontierWidthBudget_le_classSize F S d level hSize)

/-- At nonterminal levels of a depth-at-most-k formula with size > 1, the
bounded-shallow tight budget is strictly smaller than the standard S2142
intermediate budget `formulaSize`. -/
theorem boundedShallowTight_lt_standard_of_depth_le_intermediate {n : Nat}
    (k : Nat) (F : BDFormula n) (level : Nat) (hdepth : depth F ≤ k)
    (hlevel : level ≠ depth F) (hsize : 1 < formulaSize F) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level <
      syntacticTerminalFrontierWidthBudget F level := by
  have htight :
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level = 1 :=
    boundedShallowTight_eq_one_of_depth_le k F level hdepth
  have hstd : syntacticTerminalFrontierWidthBudget F level = formulaSize F := by
    simp [syntacticTerminalFrontierWidthBudget, hlevel]
  simpa [htight, hstd] using hsize

/-- Specialization: the k=1 budget equals the S2153 depth-1 tight budget. -/
theorem boundedShallowTight_eq_depthOneTight {n : Nat} (F : BDFormula n)
    (level : Nat) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget 1 F level =
      depthOneTightSyntacticTerminalFrontierWidthBudget F level := by
  unfold boundedShallowTightSyntacticTerminalFrontierWidthBudget
    depthOneTightSyntacticTerminalFrontierWidthBudget
  rfl

/-- Specialization: the k=2 budget equals the S2154 depth-2 tight budget. -/
theorem boundedShallowTight_eq_depthTwoTight {n : Nat} (F : BDFormula n)
    (level : Nat) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget 2 F level =
      depthTwoTightSyntacticTerminalFrontierWidthBudget F level := by
  unfold boundedShallowTightSyntacticTerminalFrontierWidthBudget
    depthTwoTightSyntacticTerminalFrontierWidthBudget
  by_cases h2 : depth F ≤ 2
  · simp [h2]
  · simp [h2]
    unfold depthOneTightSyntacticTerminalFrontierWidthBudget
    have h1 : ¬ depth F ≤ 1 := by omega
    simp [h1]

/-! ## k-indexed packed-family tight envelope -/

/-- k-indexed tight width envelope: every in-depth restricted budget is bounded
by `W d`. -/
def SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope
    (k : Nat) (F : SyntacticTerminalPackedFamily) (W : Nat → Nat) : Prop :=
  ∀ d level,
    level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k
        (syntacticTerminalPackedFamilyFormula F d) level ≤ W d

/-- For depth ≤ k packed formulas, the constant envelope `W ≡ 1` discharges the
k-indexed tight width envelope. -/
theorem SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope.of_depth_le_const_one
    (k : Nat) (F : SyntacticTerminalPackedFamily)
    (hdepth : ∀ d, depth (syntacticTerminalPackedFamilyFormula F d) ≤ k) :
    SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope k F
      (fun _ => 1) := by
  intro d level _hk
  simp [boundedShallowTight_eq_one_of_depth_le k
    (syntacticTerminalPackedFamilyFormula F d) level (hdepth d)]

/-! ## Generic supplied-width syntactic-terminal final-tree payload -/

/-- Final-tree payload for one recursive frontier level under a caller-supplied
per-level width schedule `W` and the unchanged class budget
`t(d,s)=S(d)*(s-1)`. -/
def SuppliedWidthClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S : Nat → Nat) (W : Nat → Nat) (d rounds : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) (level : Nat) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (syntacticTerminalFrontierLayer F level parent hClass).originalFormula
      (geometricSchedule (frontierLayerGateCount F level)
        (n / (64 * frontierLayerGateCount F level * W level))
        (rounds + 1)).length,
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
        (n / (64 * frontierLayerGateCount F level * W level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, frontierLayerGateCount F level, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (syntacticTerminalFrontierLayer F level parent hClass).originalFormula))

/-- Single-level generic final-tree consumer under a supplied per-level width
budget `W`.  Requires gate-width discharge against `W level`, positivity of
`W level`, and `W level ≤ S d`.  The class budget remains
`t(d,s)=S(d)*(s-1)`. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level ≤ depth F)
    (hwL : ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level)
    (hwClass : W level ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    SuppliedWidthClassDepthFinalTreeAt F S W d rounds parent hClass level := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  let wBudget := W level
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
  have hmClass : frontierLayerGateCount F level ≤ S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * wBudget) ≤ n :=
    geometricEntryBound_of_class_envelopes hmClass (by simpa [wBudget] using hwClass) hn
  have hreg : RegimeFrom (frontierLayerGateCount F level) wBudget
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm (by simpa [wBudget] using hw1) rounds hnLayer
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

/-- All-level generic final-tree consumer under a supplied per-level width. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
        widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hwClassAll : ∀ level, level ≤ depth F → W level ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      SuppliedWidthClassDepthFinalTreeAt F S W d rounds parent hClass level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree
      F S W d level rounds parent hDepth hSize hClass hk (hwAll level hk)
      (hwPos level hk) (hwClassAll level hk) hn

/-! ## Bounded-shallow specialization of the supplied-width consumer -/

/-- Bounded-shallow final-tree payload: supplied width is the k-indexed tight
budget. -/
def BoundedShallowTightClassDepthFinalTreeAt {n : Nat} (k : Nat)
    (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F) (level : Nat) : Prop :=
  SuppliedWidthClassDepthFinalTreeAt F S
    (fun lvl => boundedShallowTightSyntacticTerminalFrontierWidthBudget k F lvl)
    d rounds parent hClass level

/-- Single-level bounded-shallow specialization. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree
    {n : Nat} (k : Nat) (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level ≤ depth F)
    (hwL : ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
      widthDNF g.theDNF ≤
        boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    BoundedShallowTightClassDepthFinalTreeAt k F S d rounds parent hClass level := by
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree
      F S (fun lvl => boundedShallowTightSyntacticTerminalFrontierWidthBudget k F lvl)
      d level rounds parent hDepth hSize hClass hk hwL
      (boundedShallowTight_pos k F level)
      (boundedShallowTight_le_classSize k F S d level hSize) hn

/-- All-level bounded-shallow specialization. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree
    {n : Nat} (k : Nat) (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
        widthDNF g.theDNF ≤
          boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      BoundedShallowTightClassDepthFinalTreeAt k F S d rounds parent hClass
        level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree
      k F S d level rounds parent hDepth hSize hClass hk (hwAll level hk) hn

/-! ## Recursive fixed-arity nested-OR family -/

/-- Recursive nested-OR: `F₀ = base`, `F_{r+1} = or[F_r, tru]`. -/
def nestedOrFormula {n : Nat} (base : BDFormula n) : Nat → BDFormula n
  | 0 => base
  | r + 1 => BDFormula.or [nestedOrFormula base r, BDFormula.tru]

/-- Depth of the recursive nested-OR is exactly the recursion index when the base
is a depth-zero leaf. -/
theorem nestedOrFormula_depth {n : Nat} (base : BDFormula n)
    (hbase : depth base = 0) (r : Nat) :
    depth (nestedOrFormula base r) = r := by
  induction r with
  | zero =>
      simp [nestedOrFormula, hbase]
  | succ r ih =>
      simp only [nestedOrFormula, depth, List.attach_cons, List.attach_nil,
        List.map_cons, List.map_nil, List.foldr]
      -- Goal shape: `1 + depth(Fr).max (0.max 0) = r + 1`
      simp [ih, depth]
      omega

/-- Size of the recursive nested-OR is `formulaSize base + 2r`.  For a size-1
base this is `2r + 1`. -/
theorem nestedOrFormula_size {n : Nat} (base : BDFormula n) (r : Nat) :
    formulaSize (nestedOrFormula base r) = formulaSize base + 2 * r := by
  induction r with
  | zero =>
      simp [nestedOrFormula]
  | succ r ih =>
      simp [nestedOrFormula, formulaSize_or, formulaSize, ih]
      omega

/-- Size is exactly `2r + 1` when the base is a literal (size 1). -/
theorem nestedOrFormula_size_of_lit {n : Nat} (l : Literal n) (r : Nat) :
    formulaSize (nestedOrFormula (BDFormula.lit l) r) = 2 * r + 1 := by
  simpa [formulaSize_lit, Nat.add_comm] using
    nestedOrFormula_size (BDFormula.lit l) r

/-- Structural simplicity of the recursive nested-OR when the base is simple. -/
theorem nestedOrFormula_syntacticFormulaSimpleDNF {n : Nat} (base : BDFormula n)
    (hbase : syntacticFormulaSimpleDNF base) (r : Nat) :
    syntacticFormulaSimpleDNF (nestedOrFormula base r) := by
  induction r with
  | zero =>
      simpa [nestedOrFormula] using hbase
  | succ r ih =>
      change syntacticOrListSimpleDNF
        [nestedOrFormula base r, BDFormula.tru]
      refine And.intro ih ?_
      exact And.intro (by simp [syntacticFormulaSimpleDNF]) trivial

/-- No-empty-fanin of the recursive nested-OR when the base has no empty fanins. -/
theorem nestedOrFormula_noEmptyFanins {n : Nat} (base : BDFormula n)
    (hbase : NoEmptyFanins base) (r : Nat) :
    NoEmptyFanins (nestedOrFormula base r) := by
  induction r with
  | zero =>
      simpa [nestedOrFormula] using hbase
  | succ r ih =>
      refine NoEmptyFanins.or (by simp [nestedOrFormula]) ?_
      intro child hchild
      simp [nestedOrFormula] at hchild
      rcases hchild with hchild | hchild
      · subst child
        exact ih
      · subst child
        exact NoEmptyFanins.tru

/-- Syntactic DNF width of `tru` is at most one. -/
theorem widthDNF_tru_syntactic_le_one {n : Nat} :
    widthDNF (syntacticDNF (BDFormula.tru : BDFormula n)) ≤ 1 := by
  have h : widthDNF (syntacticDNF (BDFormula.tru : BDFormula n)) = 0 := by
    simp [syntacticDNF, FormulaSyntacticDNF.trueDNF, widthDNF, termWidth]
  exact Nat.le_trans (le_of_eq h) (by decide : (0 : Nat) ≤ 1)

/-- Syntactic DNF width of a literal is at most one. -/
theorem widthDNF_lit_syntactic_le_one {n : Nat} (l : Literal n) :
    widthDNF (syntacticDNF (BDFormula.lit l)) ≤ 1 := by
  simp [syntacticDNF, FormulaSyntacticDNF.literalDNF, widthDNF, termWidth]

/-- Syntactic DNF width of the recursive nested-OR is at most one when the base
has syntactic DNF width ≤ 1. -/
theorem nestedOrFormula_widthDNF_syntactic_le_one {n : Nat} (base : BDFormula n)
    (hbase : widthDNF (syntacticDNF base) ≤ 1) (r : Nat) :
    widthDNF (syntacticDNF (nestedOrFormula base r)) ≤ 1 := by
  induction r with
  | zero =>
      simpa [nestedOrFormula] using hbase
  | succ r ih =>
      have hTru := widthDNF_tru_syntactic_le_one (n := n)
      have hNil : widthDNF (syntacticOrDNF ([] : List (BDFormula n))) ≤ 1 := by
        simp [syntacticOrDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
      have hRest : widthDNF (syntacticOrDNF
          ([BDFormula.tru] : List (BDFormula n))) ≤ 1 := by
        simp only [syntacticOrDNF]
        exact widthDNF_orDNF_le hTru hNil
      simp only [nestedOrFormula, syntacticDNF, syntacticOrDNF]
      exact widthDNF_orDNF_le ih hRest

/-! ## Frontier membership for the recursive nested-OR family -/

/-- Top children of a positive nested-OR step are the predecessor and `tru`. -/
theorem nestedOrFormula_topChildren_succ {n : Nat} (base : BDFormula n)
    (r : Nat) :
    topChildren (nestedOrFormula base (r + 1)) =
      [nestedOrFormula base r, BDFormula.tru] := by
  simp [nestedOrFormula, topChildren]

/-- Top children of a depth-zero base leaf are empty. -/
theorem nestedOrFormula_topChildren_zero_of_leaf {n : Nat} (base : BDFormula n)
    (hleaf : topChildren base = []) :
    topChildren (nestedOrFormula base 0) = [] := by
  simpa [nestedOrFormula] using hleaf

/-- Any member of the depth-frontier of `F_r` is either some `F_s` with `s ≤ r`
or the constant `tru`, when the base is a leaf.  Proved by induction on
`level` using `formulaDepthFrontier_succ_eq_bind_topChildren`. -/
theorem nestedOrFormula_frontier_member {n : Nat} (base : BDFormula n)
    (hleaf : topChildren base = []) (r level : Nat) (G : BDFormula n)
    (hG : G ∈ formulaDepthFrontier level (nestedOrFormula base r)) :
    (∃ s, s ≤ r ∧ G = nestedOrFormula base s) ∨ G = BDFormula.tru := by
  induction level generalizing r G with
  | zero =>
      have hEq : G = nestedOrFormula base r := by
        simpa [formulaDepthFrontier, depthFrontier] using hG
      refine Or.inl ⟨r, Nat.le_refl r, hEq⟩
  | succ level ih =>
      have hbind :
          G ∈ (formulaDepthFrontier level (nestedOrFormula base r)).bind
            topChildren := by
        simpa [formulaDepthFrontier_succ_eq_bind_topChildren level
          (nestedOrFormula base r)] using hG
      rcases List.mem_bind.mp hbind with ⟨mid, hmid, hchild⟩
      have hmid' := ih r mid hmid
      rcases hmid' with ⟨s, hs, hmidEq⟩ | hmidTru
      · subst mid
        cases s with
        | zero =>
            have : G ∈ topChildren base := by
              simpa [nestedOrFormula] using hchild
            simp [hleaf] at this
        | succ s =>
            have htc :
                topChildren (nestedOrFormula base (s + 1)) =
                  [nestedOrFormula base s, BDFormula.tru] :=
              nestedOrFormula_topChildren_succ base s
            have hmem : G = nestedOrFormula base s ∨ G = BDFormula.tru := by
              simpa [htc] using hchild
            rcases hmem with hG' | hG'
            · refine Or.inl ⟨s, Nat.le_trans (Nat.le_succ s) hs, hG'⟩
            · exact Or.inr hG'
      · subst mid
        simp [topChildren] at hchild

/-- Every frontier member of the nested-OR family has syntactic DNF width ≤ 1
when the base is a literal. -/
theorem nestedOrFormula_frontier_member_widthDNF_le_one {n : Nat}
    (l : Literal n) (r level : Nat) (G : BDFormula n)
    (hG : G ∈ formulaDepthFrontier level (nestedOrFormula (BDFormula.lit l) r)) :
    widthDNF (syntacticDNF G) ≤ 1 := by
  have hleaf : topChildren (BDFormula.lit l : BDFormula n) = [] := by
    simp [topChildren]
  have hmem := nestedOrFormula_frontier_member (BDFormula.lit l) hleaf r level G hG
  rcases hmem with ⟨s, _hs, hGeq⟩ | hGtru
  · subst G
    exact nestedOrFormula_widthDNF_syntactic_le_one (BDFormula.lit l)
      (widthDNF_lit_syntactic_le_one l) s
  · subst G
    exact widthDNF_tru_syntactic_le_one (n := n)

/-- Selected GateSpec DNF width ≤ 1 at non-terminal levels of a nested-OR
formula built from a literal base. -/
theorem nestedOrFormula_intermediate_gate_width_le_one {n : Nat}
    (l : Literal n) (r : Nat) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass
      (nestedOrFormula (BDFormula.lit l) r))
    (level : Nat)
    (hk : level ≤ depth (nestedOrFormula (BDFormula.lit l) r))
    (hlevel : level ≠ depth (nestedOrFormula (BDFormula.lit l) r))
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (nestedOrFormula (BDFormula.lit l) r) level parent hClass).gates) :
    widthDNF g.theDNF ≤ 1 := by
  set F := nestedOrFormula (BDFormula.lit l) r
  have hg' : List.Mem g (syntacticFrontierMinimalLayer F level parent
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
        hClass.1)).gates := by
    simpa [syntacticTerminalFrontierLayer, hlevel] using hg
  have hg'' : List.Mem g (syntacticFrontierGateList F level
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
        hClass.1)) := by
    simpa [syntacticFrontierMinimalLayer, syntacticFrontierGateLayer] using hg'
  rw [syntacticFrontierGateList] at hg''
  rcases List.mem_map.mp hg'' with ⟨G, _hGmem, rfl⟩
  have hDNF :
      (syntacticSimpleFormulaGate G.1
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
          hClass.1 G.1 G.2)).theDNF =
        syntacticDNF G.1 := by
    simp [syntacticSimpleFormulaGate, syntacticDNFViewOfFormulaSimple,
      syntacticDNFView, GateSpec.theDNF]
  have hwidth : widthDNF (syntacticDNF G.1) ≤ 1 :=
    nestedOrFormula_frontier_member_widthDNF_le_one l r level G.1 G.2
  simpa [hDNF] using hwidth

/-- Every syntactic-terminal frontier gate of a nested-OR formula has DNF width
at most the k-indexed tight budget when depth equals the recursion index and
that index is ≤ k. -/
theorem nestedOrFormula_width_le_boundedShallowTight {n : Nat}
    (l : Literal n) (k r : Nat) (hrk : r ≤ k) (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass
      (nestedOrFormula (BDFormula.lit l) r))
    (level : Nat)
    (hk : level ≤ depth (nestedOrFormula (BDFormula.lit l) r))
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (nestedOrFormula (BDFormula.lit l) r) level parent hClass).gates) :
    widthDNF g.theDNF ≤
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k
        (nestedOrFormula (BDFormula.lit l) r) level := by
  set F := nestedOrFormula (BDFormula.lit l) r
  have hdepthEq : depth F = r :=
    nestedOrFormula_depth (BDFormula.lit l) (by simp [depth]) r
  have hdepth : depth F ≤ k := by simpa [hdepthEq] using hrk
  have hbudget :
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level = 1 :=
    boundedShallowTight_eq_one_of_depth_le k F level hdepth
  have hwidth : widthDNF g.theDNF ≤ 1 := by
    by_cases hlevel : level = depth F
    · subst hlevel
      have hg' : List.Mem g (terminalLayerMinimalLayer F parent).gates := by
        simpa [syntacticTerminalFrontierLayer] using hg
      simpa [terminalLayerWidthBudget] using
        terminalLayerMinimalLayer_width_le_budget F parent g hg'
    · exact nestedOrFormula_intermediate_gate_width_le_one l r parent hClass
        level hk hlevel g hg
  simpa [hbudget] using hwidth

/-! ## Packed family at depth index d with shallow cap k -/

/-- Size-cap profile for the k-indexed nested-OR witness: size `2 * min(d,k) + 1`. -/
def boundedShallowTightSizeCapIndex (k d : Nat) : Nat :=
  2 * min d k + 1

/-- Ambient arity for the nested-OR family, using the S2144 product threshold and
harmless multiplicity `2`. -/
def boundedShallowTightArity (k : Nat) (roundsOf : Nat → Nat) (d : Nat) : Nat :=
  syntacticTerminalCoarseEntryProduct
    (boundedShallowTightSizeCapIndex k d) (roundsOf d) * 2

theorem boundedShallowTightSizeCapIndex_pos (k d : Nat) :
    0 < boundedShallowTightSizeCapIndex k d := by
  unfold boundedShallowTightSizeCapIndex
  omega

/-- The nested-OR ambient arity is positive. -/
theorem boundedShallowTightArity_pos (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    0 < boundedShallowTightArity k roundsOf d := by
  have hprod :
      0 < syntacticTerminalCoarseEntryProduct
        (boundedShallowTightSizeCapIndex k d) (roundsOf d) := by
    simpa [syntacticTerminalCoarseEntryProduct_eq_threshold] using
      syntacticTerminalClassCoarseEntryThreshold_pos_of_pos
        (boundedShallowTightSizeCapIndex_pos k d)
  exact Nat.mul_pos hprod (by decide : 0 < 2)

/-- Variable `0` as a positive literal over the nested-OR arity. -/
def boundedShallowTightLit0 (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    BDFormula (boundedShallowTightArity k roundsOf d) :=
  BDFormula.lit
    { var := ⟨0, boundedShallowTightArity_pos k roundsOf d⟩, sign := true }

/-- The restricted nested-OR formula of recursion depth `min d k`. -/
def boundedShallowTightFormula (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    BDFormula (boundedShallowTightArity k roundsOf d) :=
  nestedOrFormula (boundedShallowTightLit0 k roundsOf d) (min d k)

/-- The concrete k-indexed nested-OR packed family. -/
def boundedShallowTightPackedFamily (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamily :=
  fun d => ⟨boundedShallowTightArity k roundsOf d,
    boundedShallowTightFormula k roundsOf d⟩

/-- Exact size profile: `2 * min d k + 1`. -/
theorem boundedShallowTightPackedFamily_sizeCap
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap
      (boundedShallowTightPackedFamily k roundsOf) d =
        boundedShallowTightSizeCapIndex k d := by
  simp [syntacticTerminalPackedFamilySizeCap, syntacticTerminalPackedFamilyFormula,
    boundedShallowTightPackedFamily, boundedShallowTightFormula,
    boundedShallowTightSizeCapIndex, boundedShallowTightLit0,
    nestedOrFormula_size_of_lit]

/-- Exact depth profile: `min d k`. -/
theorem boundedShallowTightPackedFamily_depth
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (boundedShallowTightPackedFamily k roundsOf) d) = min d k := by
  simp only [syntacticTerminalPackedFamilyFormula, boundedShallowTightPackedFamily,
    boundedShallowTightFormula]
  exact nestedOrFormula_depth (boundedShallowTightLit0 k roundsOf d)
    (by simp [boundedShallowTightLit0, depth]) (min d k)

/-- Once `d` reaches the fixed shallow bound `k`, the packed formula has exact
depth `k`. -/
theorem boundedShallowTightPackedFamily_depth_eq_k_of_k_le_d
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) (hk : k ≤ d) :
    depth (syntacticTerminalPackedFamilyFormula
      (boundedShallowTightPackedFamily k roundsOf) d) = k := by
  rw [boundedShallowTightPackedFamily_depth k roundsOf d,
    Nat.min_eq_right hk]

/-- Once `d` reaches `k`, the packed formula has size cap `2*k + 1`. -/
theorem boundedShallowTightPackedFamily_sizeCap_eq_two_mul_k_add_one_of_k_le_d
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) (hk : k ≤ d) :
    syntacticTerminalPackedFamilySizeCap
      (boundedShallowTightPackedFamily k roundsOf) d =
        2 * k + 1 := by
  rw [boundedShallowTightPackedFamily_sizeCap k roundsOf d]
  simp [boundedShallowTightSizeCapIndex, Nat.min_eq_right hk]

/-- The nested-OR family is in the syntactic-terminal class. -/
theorem boundedShallowTightPackedFamily_class
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClass
      (boundedShallowTightPackedFamily k roundsOf) := by
  intro d
  constructor
  · exact nestedOrFormula_syntacticFormulaSimpleDNF
      (boundedShallowTightLit0 k roundsOf d)
      (by simp [boundedShallowTightLit0, syntacticFormulaSimpleDNF,
        syntacticOrListSimpleDNF])
      (min d k)
  · exact nestedOrFormula_noEmptyFanins
      (boundedShallowTightLit0 k roundsOf d)
      (NoEmptyFanins.lit _)
      (min d k)

/-- The nested-OR family satisfies the depth-index bound. -/
theorem boundedShallowTightPackedFamily_depthBound
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyDepthBound
      (boundedShallowTightPackedFamily k roundsOf) := by
  intro d
  have h := boundedShallowTightPackedFamily_depth k roundsOf d
  have hmin : min d k ≤ d := Nat.min_le_left d k
  rw [h]
  exact hmin

/-- Class-size envelope by the concrete size cap. -/
theorem boundedShallowTightPackedFamily_classSizeEnvelope
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClassSizeEnvelope
      (boundedShallowTightPackedFamily k roundsOf)
      (boundedShallowTightSizeCapIndex k) := by
  intro d
  simp [boundedShallowTightPackedFamily_sizeCap]

/-- The family is a product/counting source with constant multiplicity `2`. -/
theorem boundedShallowTightPackedFamily_productCountingSource
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyProductCountingSource
      (boundedShallowTightPackedFamily k roundsOf) roundsOf
      productCountingMultiplicityTwo := by
  intro d
  refine ⟨Nat.zero_lt_two, ?_⟩
  simp [productCountingMultiplicityTwo, syntacticTerminalPackedFamilyArity,
    boundedShallowTightPackedFamily, boundedShallowTightArity,
    boundedShallowTightPackedFamily_sizeCap]

/-- Structural ambient adequacy for the concrete size cap. -/
theorem boundedShallowTightPackedFamily_structuralAmbientAdequate
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyStructuralAmbientAdequate
      (boundedShallowTightPackedFamily k roundsOf)
      (boundedShallowTightSizeCapIndex k) roundsOf := by
  intro d
  have hAmb := SyntacticTerminalPackedFamilyAmbientAdequate.of_productCountingSource
    (boundedShallowTightPackedFamily_productCountingSource k roundsOf) d
  simpa [boundedShallowTightPackedFamily_sizeCap] using hAmb

/-- All formulas in the family have depth at most k. -/
theorem boundedShallowTightPackedFamily_depth_le_k
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula
      (boundedShallowTightPackedFamily k roundsOf) d) ≤ k := by
  have h := boundedShallowTightPackedFamily_depth k roundsOf d
  have hmin : min d k ≤ k := Nat.min_le_right d k
  rw [h]
  exact hmin

/-- The k-indexed tight budget is constantly `1` on the nested-OR family. -/
theorem boundedShallowTightPackedFamily_budget_eq_one
    (k : Nat) (roundsOf : Nat → Nat) (d level : Nat) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k
      (syntacticTerminalPackedFamilyFormula
        (boundedShallowTightPackedFamily k roundsOf) d) level = 1 :=
  boundedShallowTight_eq_one_of_depth_le k _ level
    (boundedShallowTightPackedFamily_depth_le_k k roundsOf d)

/-- Tight WidthEnvelope discharge with `W ≡ 1`. -/
theorem boundedShallowTightPackedFamily_tightWidthEnvelope_one
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope k
      (boundedShallowTightPackedFamily k roundsOf) (fun _ => 1) :=
  SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope.of_depth_le_const_one
    k _ (boundedShallowTightPackedFamily_depth_le_k k roundsOf)

/-- When `min d k ≥ 1`, intermediate level 0 is a strict improvement over the
standard intermediate budget. -/
theorem boundedShallowTightPackedFamily_lt_standard_intermediate_zero
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) (hd : 1 ≤ min d k) :
    boundedShallowTightSyntacticTerminalFrontierWidthBudget k
        (syntacticTerminalPackedFamilyFormula
          (boundedShallowTightPackedFamily k roundsOf) d) 0 <
      syntacticTerminalFrontierWidthBudget
        (syntacticTerminalPackedFamilyFormula
          (boundedShallowTightPackedFamily k roundsOf) d) 0 := by
  set F := syntacticTerminalPackedFamilyFormula
    (boundedShallowTightPackedFamily k roundsOf) d
  have hdepthEq : depth F = min d k := by
    simpa [F] using boundedShallowTightPackedFamily_depth k roundsOf d
  have hdepth : depth F ≤ k := by
    have : min d k ≤ k := Nat.min_le_right d k
    simp [hdepthEq, this]
  have hlevel : (0 : Nat) ≠ depth F := by
    intro h
    have : depth F = 0 := h.symm
    omega
  have hsize : 1 < formulaSize F := by
    have hcap := boundedShallowTightPackedFamily_sizeCap k roundsOf d
    have hsz : formulaSize F = 2 * min d k + 1 := by
      simpa [F, syntacticTerminalPackedFamilySizeCap,
        boundedShallowTightSizeCapIndex] using hcap
    omega
  exact boundedShallowTight_lt_standard_of_depth_le_intermediate k F 0
    hdepth hlevel hsize

/-- Actual all-level gate width ≤ 1 (hence ≤ the tight budget) for the packed
family. -/
theorem boundedShallowTightPackedFamily_width_le_boundedShallowTight
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) (parent : ParentKind)
    (level : Nat)
    (hk : level ≤ depth (syntacticTerminalPackedFamilyFormula
      (boundedShallowTightPackedFamily k roundsOf) d))
    (g : GateSpec (syntacticTerminalPackedFamilyArity
      (boundedShallowTightPackedFamily k roundsOf) d))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (syntacticTerminalPackedFamilyFormula
        (boundedShallowTightPackedFamily k roundsOf) d)
      level parent
      (boundedShallowTightPackedFamily_class k roundsOf d)).gates) :
    widthDNF g.theDNF ≤
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k
        (syntacticTerminalPackedFamilyFormula
          (boundedShallowTightPackedFamily k roundsOf) d) level := by
  have hrk : min d k ≤ k := Nat.min_le_right d k
  simpa [syntacticTerminalPackedFamilyFormula, syntacticTerminalPackedFamilyArity,
    boundedShallowTightPackedFamily, boundedShallowTightFormula] using
    nestedOrFormula_width_le_boundedShallowTight
      { var := ⟨0, boundedShallowTightArity_pos k roundsOf d⟩, sign := true }
      k (min d k) hrk parent
      (by simpa [syntacticTerminalPackedFamilyFormula, boundedShallowTightPackedFamily,
        boundedShallowTightFormula] using
        boundedShallowTightPackedFamily_class k roundsOf d)
      level
      (by simpa [syntacticTerminalPackedFamilyFormula, boundedShallowTightPackedFamily,
        boundedShallowTightFormula] using hk)
      g
      (by simpa [syntacticTerminalPackedFamilyFormula, syntacticTerminalPackedFamilyArity,
        boundedShallowTightPackedFamily, boundedShallowTightFormula] using hg)

private theorem boundedShallowTight_structural_entry
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) :
    2 * (64 * boundedShallowTightSizeCapIndex k d) ^ roundsOf d *
      (64 * boundedShallowTightSizeCapIndex k d *
        boundedShallowTightSizeCapIndex k d) ≤
      syntacticTerminalPackedFamilyArity
        (boundedShallowTightPackedFamily k roundsOf) d := by
  have hAmb := boundedShallowTightPackedFamily_structuralAmbientAdequate k roundsOf d
  simpa [SyntacticTerminalPackedFamilyStructuralAmbientAdequate,
    syntacticTerminalClassCoarseEntryThreshold] using hAmb

/-- Specialized all-level final-tree route for the concrete k-indexed nested-OR
family at every index `d` and every parent, under the unchanged class budget. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_boundedShallow
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (boundedShallowTightPackedFamily k roundsOf) d) →
      BoundedShallowTightClassDepthFinalTreeAt k
        (syntacticTerminalPackedFamilyFormula
          (boundedShallowTightPackedFamily k roundsOf) d)
        (boundedShallowTightSizeCapIndex k) d (roundsOf d) parent
        (boundedShallowTightPackedFamily_class k roundsOf d) level := by
  intro level hk
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree
      k
      (syntacticTerminalPackedFamilyFormula
        (boundedShallowTightPackedFamily k roundsOf) d)
      (boundedShallowTightSizeCapIndex k) d level (roundsOf d) parent
      ?hDepth ?hSize (boundedShallowTightPackedFamily_class k roundsOf d) hk
      ?hwL ?hn
  · exact boundedShallowTightPackedFamily_depthBound k roundsOf d
  · exact boundedShallowTightPackedFamily_classSizeEnvelope k roundsOf d
  · intro g hg
    exact boundedShallowTightPackedFamily_width_le_boundedShallowTight
      k roundsOf d parent level hk g hg
  · exact boundedShallowTight_structural_entry k roundsOf d

/-- Existence package for the restricted S2155 k-indexed bounded-shallow tight
budget route, including the final-tree consumer for every `k`, `d`, and parent. -/
theorem exists_boundedShallowTightWidthBudget_dischargesEnvelope_finalTreeRoute
    (k : Nat) (roundsOf : Nat → Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      ∃ S : Nat → Nat,
        SyntacticTerminalPackedFamilyClass F ∧
        SyntacticTerminalPackedFamilyDepthBound F ∧
        SyntacticTerminalPackedFamilyClassSizeEnvelope F S ∧
        SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope k F
          (fun _ => 1) ∧
        SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
        (∀ d, depth (syntacticTerminalPackedFamilyFormula F d) = min d k) ∧
        (∀ d, syntacticTerminalPackedFamilySizeCap F d =
          2 * min d k + 1) ∧
        (∀ d level, boundedShallowTightSyntacticTerminalFrontierWidthBudget k
          (syntacticTerminalPackedFamilyFormula F d) level = 1) ∧
        (∀ d, 1 ≤ min d k →
          boundedShallowTightSyntacticTerminalFrontierWidthBudget k
              (syntacticTerminalPackedFamilyFormula F d) 0 <
            syntacticTerminalFrontierWidthBudget
              (syntacticTerminalPackedFamilyFormula F d) 0) ∧
        (∀ d parent level,
          level ≤ depth (syntacticTerminalPackedFamilyFormula
            (boundedShallowTightPackedFamily k roundsOf) d) →
            ∀ g, List.Mem g (syntacticTerminalFrontierLayer
              (syntacticTerminalPackedFamilyFormula
                (boundedShallowTightPackedFamily k roundsOf) d)
              level parent
              (boundedShallowTightPackedFamily_class k roundsOf d)).gates →
              widthDNF g.theDNF ≤ 1) ∧
        (∀ d parent level,
          level ≤ depth (syntacticTerminalPackedFamilyFormula
            (boundedShallowTightPackedFamily k roundsOf) d) →
            BoundedShallowTightClassDepthFinalTreeAt k
              (syntacticTerminalPackedFamilyFormula
                (boundedShallowTightPackedFamily k roundsOf) d)
              (boundedShallowTightSizeCapIndex k) d (roundsOf d) parent
              (boundedShallowTightPackedFamily_class k roundsOf d) level) := by
  refine ⟨boundedShallowTightPackedFamily k roundsOf,
    boundedShallowTightSizeCapIndex k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact boundedShallowTightPackedFamily_class k roundsOf
  · exact boundedShallowTightPackedFamily_depthBound k roundsOf
  · exact boundedShallowTightPackedFamily_classSizeEnvelope k roundsOf
  · exact boundedShallowTightPackedFamily_tightWidthEnvelope_one k roundsOf
  · exact boundedShallowTightPackedFamily_structuralAmbientAdequate k roundsOf
  · intro d
    exact boundedShallowTightPackedFamily_depth k roundsOf d
  · intro d
    simpa [boundedShallowTightSizeCapIndex] using
      boundedShallowTightPackedFamily_sizeCap k roundsOf d
  · intro d level
    exact boundedShallowTightPackedFamily_budget_eq_one k roundsOf d level
  · intro d hd
    exact boundedShallowTightPackedFamily_lt_standard_intermediate_zero
      k roundsOf d hd
  · intro d parent level hk g hg
    have h := boundedShallowTightPackedFamily_width_le_boundedShallowTight
      k roundsOf d parent level hk g hg
    simpa [boundedShallowTightPackedFamily_budget_eq_one k roundsOf d level] using h
  · intro d parent level hk
    exact
      allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_boundedShallow
        k roundsOf d parent level hk

end FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget
end PvNP
