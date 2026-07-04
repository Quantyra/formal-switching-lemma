import PvNP.FormulaRecursiveWidthSchedule

/-!
# Nonempty recursive frontiers from no-empty-fanin syntax

The recursive frontier schedule consumers require explicit nonempty gate-count
hypotheses because raw unbounded fan-in syntax admits empty `and`/`or` gates.
This module isolates the structural condition that removes that obligation:
every `and`/`or` gate in the formula has at least one child.

Under that condition, every recursive frontier level `k <= depth F` is
nonempty.  The supplied-width ratio/geometric schedule consumers can therefore
discharge their `hm` hypotheses directly from raw syntax.

## HONEST SCOPE STATEMENT (read this)

* This does not synthesize efficient width profiles, product/counting
  hypotheses, or a formula-independent asymptotic `t(d,s)`.
* It does not replace the truth-table fallback for intermediate frontier
  widths and does not close full frozen-form B4.
* It is not a PHP switching lemma, not a Frege/PHP lower bound, not an
  NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveNonempty

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveDecomposition
open FormulaRecursiveLayerProfile
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveWidthSchedule
open FrozenProductSchedule
open FrozenProductScheduleRatio
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## No-empty-fanin formulas -/

/-- Structural predicate excluding empty unbounded fan-in gates. -/
inductive NoEmptyFanins {n : Nat} : BDFormula n -> Prop where
  | tru : NoEmptyFanins BDFormula.tru
  | fls : NoEmptyFanins BDFormula.fls
  | lit (l : CNFModel.Literal n) : NoEmptyFanins (BDFormula.lit l)
  | and {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : forall child, child ∈ children -> NoEmptyFanins child) :
      NoEmptyFanins (BDFormula.and children)
  | or {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : forall child, child ∈ children -> NoEmptyFanins child) :
      NoEmptyFanins (BDFormula.or children)

/-! ## List max-depth witnesses -/

/-- If a nonempty child list has max depth at least `k`, some child has depth at
least `k`. -/
theorem exists_child_depth_ge_of_le_depthMax {n : Nat}
    (children : List (BDFormula n)) (k : Nat)
    (hne : children ≠ [])
    (hmax : k <= (children.map depth).foldr Nat.max 0) :
    exists child, child ∈ children /\ k <= depth child := by
  induction children generalizing k with
  | nil =>
      exact False.elim (hne rfl)
  | cons child rest ih =>
      by_cases hchild : k <= depth child
      · exact ⟨child, List.mem_cons_self child rest, hchild⟩
      · have hmax' : k <= Nat.max (depth child)
            ((rest.map depth).foldr Nat.max 0) := by
          simpa using hmax
        by_cases hrest : k <= (rest.map depth).foldr Nat.max 0
        · rcases ih k (by
              intro hnil
              subst hnil
              have hchild_lt : depth child < k := Nat.lt_of_not_ge hchild
              have hzero_lt : 0 < k := by omega
              have hmax_lt : Nat.max (depth child) 0 < k :=
                Nat.max_lt.2 ⟨hchild_lt, hzero_lt⟩
              exact (Nat.not_le_of_gt hmax_lt) hmax') hrest with
            ⟨witness, hwitness, hdepth⟩
          exact ⟨witness, List.mem_cons_of_mem child hwitness, hdepth⟩
        · have hchild_lt : depth child < k := Nat.lt_of_not_ge hchild
          have hrest_lt : (rest.map depth).foldr Nat.max 0 < k :=
            Nat.lt_of_not_ge hrest
          have hmax_lt : Nat.max (depth child)
              ((rest.map depth).foldr Nat.max 0) < k :=
            Nat.max_lt.2 ⟨hchild_lt, hrest_lt⟩
          exact False.elim ((Nat.not_le_of_gt hmax_lt) hmax')

/-- A no-empty-fanin formula with remaining depth `k + 1` has a top child with
remaining depth at least `k`, and that child is also no-empty-fanin. -/
theorem exists_topChild_depth_ge_of_noEmptyFanins {n : Nat}
    (F : BDFormula n) (k : Nat) (hF : NoEmptyFanins F)
    (hk : k + 1 <= depth F) :
    exists child, child ∈ FormulaTruthTableView.topChildren F /\
      NoEmptyFanins child /\ k <= depth child := by
  cases hF with
  | tru =>
      simp [depth] at hk
  | fls =>
      simp [depth] at hk
  | lit l =>
      simp [depth] at hk
  | and hne hchildren =>
      rename_i children
      have hdepth :
          depth (BDFormula.and children) =
            1 + (children.map depth).foldr Nat.max 0 := by
        rw [depth]
        rw [List.attach_map_val children (fun child => depth child)]
      have hmax : k <= (children.map depth).foldr Nat.max 0 := by
        rw [hdepth] at hk
        omega
      rcases exists_child_depth_ge_of_le_depthMax children k hne hmax with
        ⟨child, hchild, hdepthChild⟩
      exact ⟨child, by simpa [FormulaTruthTableView.topChildren] using hchild,
        hchildren child hchild, hdepthChild⟩
  | or hne hchildren =>
      rename_i children
      have hdepth :
          depth (BDFormula.or children) =
            1 + (children.map depth).foldr Nat.max 0 := by
        rw [depth]
        rw [List.attach_map_val children (fun child => depth child)]
      have hmax : k <= (children.map depth).foldr Nat.max 0 := by
        rw [hdepth] at hk
        omega
      rcases exists_child_depth_ge_of_le_depthMax children k hne hmax with
        ⟨child, hchild, hdepthChild⟩
      exact ⟨child, by simpa [FormulaTruthTableView.topChildren] using hchild,
        hchildren child hchild, hdepthChild⟩

/-! ## Nonempty recursive frontiers -/

/-- If some root in a root list is no-empty-fanin and has depth at least `k`,
then the `k`-step recursive frontier of that root list is nonempty. -/
theorem depthFrontier_nonempty_of_noEmptyFanins {n : Nat} :
    forall (k : Nat) (roots : List (BDFormula n)),
      (exists root, root ∈ roots /\ NoEmptyFanins root /\ k <= depth root) ->
        1 <= (depthFrontier k roots).length
  | 0, roots, hexists => by
      rcases hexists with ⟨root, hroot, _hrootReg, _hdepth⟩
      exact Nat.succ_le_of_lt (List.length_pos_of_mem hroot)
  | k + 1, roots, hexists => by
      rcases hexists with ⟨root, hroot, hrootReg, hdepth⟩
      rcases exists_topChild_depth_ge_of_noEmptyFanins root k hrootReg hdepth with
        ⟨child, hchild, hchildReg, hchildDepth⟩
      have hnext :
          exists nextRoot, nextRoot ∈ roots.bind FormulaTruthTableView.topChildren /\
            NoEmptyFanins nextRoot /\ k <= depth nextRoot := by
        exact ⟨child, List.mem_bind.mpr ⟨root, hroot, hchild⟩,
          hchildReg, hchildDepth⟩
      simpa [depthFrontier] using
        depthFrontier_nonempty_of_noEmptyFanins k
          (roots.bind FormulaTruthTableView.topChildren) hnext

/-- Single-formula recursive frontiers are nonempty at every level within the
raw depth when the formula has no empty fan-ins. -/
theorem formulaDepthFrontier_nonempty_of_noEmptyFanins {n : Nat}
    (F : BDFormula n) (k : Nat) (hF : NoEmptyFanins F)
    (hk : k <= depth F) :
    1 <= (formulaDepthFrontier k F).length := by
  exact depthFrontier_nonempty_of_noEmptyFanins k [F]
    ⟨F, List.mem_singleton_self F, hF, hk⟩

/-- Gate-count form of the nonempty frontier theorem. -/
theorem frontierLayerGateCount_nonempty_of_noEmptyFanins {n : Nat}
    (F : BDFormula n) (k : Nat) (hF : NoEmptyFanins F)
    (hk : k <= depth F) :
    1 <= frontierLayerGateCount F k := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  exact formulaDepthFrontier_nonempty_of_noEmptyFanins F k hF hk

/-! ## Schedule consumers with synthesized nonempty counts -/

open GeneratedRefinedIteratedCertificate in
/-- Uniform supplied-width ratio-regime frontier collapse where the nonempty
gate-count hypothesis is synthesized from no-empty-fanin raw syntax. -/
theorem allFrontierLayers_ratioRegimeCollapseWithWidthProfile_noEmptyFanins
    {n : Nat} (F : BDFormula n) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (sched : List ScheduleStage)
    (hF : NoEmptyFanins F)
    (hreg : forall level, level <= depth F ->
      RegimeFrom (frontierLayerGateCount F level)
        (profile.widthBudget level) (stars (freeRestriction n)) sched) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (frontierLayerMinimalLayer F level parent).originalFormula sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F level) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) sched.length sched := by
  exact allFrontierLayers_ratioRegimeCollapseWithWidthProfile
    F parent profile sched
    (fun level hk => frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk)
    hreg

open GeneratedRefinedIteratedCertificate in
/-- Uniform supplied-width geometric frontier collapse where the nonempty
gate-count hypothesis is synthesized from no-empty-fanin raw syntax. -/
theorem allFrontierLayers_geometricCollapseWithWidthProfile_noEmptyFanins
    {n : Nat} (F : BDFormula n) (rounds : Nat) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (hF : NoEmptyFanins F)
    (hw1 : forall level, level <= depth F ->
      1 <= profile.widthBudget level)
    (hn : forall level, level <= depth F ->
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          profile.widthBudget level) <= n) :
    forall level, level <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (frontierLayerMinimalLayer F level parent).originalFormula
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)).length,
        cert.stageGateCounts =
          List.replicate (rounds + 1) (frontierLayerGateCount F level) /\
        cert.stageBudgets = List.replicate (rounds + 1) 2 /\
        cert.stageStarCounts =
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)).map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)) := by
  exact allFrontierLayers_geometricCollapseWithWidthProfile
    F rounds parent profile
    (fun level hk => frontierLayerGateCount_nonempty_of_noEmptyFanins F level hF hk)
    hw1 hn

end FormulaRecursiveNonempty
end PvNP
