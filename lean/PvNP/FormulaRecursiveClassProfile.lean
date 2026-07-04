import PvNP.FormulaRecursiveWidthSchedule
import PvNP.FormulaSyntacticClassGlobalTree

/-!
# Class-envelope recursive frontier profiles

`FormulaSyntacticClassGlobalTree` gives a supplied depth-indexed class budget
for the root-simple syntactic-DNF frontier route.  This module moves the same
class-budget surface to the already-synthesized raw recursive frontier layers:
given a supplied class-size envelope `S(d)` and a supplied class-width envelope
`W(d)` for a recursive width profile, every in-depth recursive frontier layer
can consume the geometric schedule and expose the final decision tree under

  `t(d,s) = S(d) * (s - 1)`.

## Honest scope

* The class-size envelope `S(d)` is supplied.
* The width profile and class-width envelope `W(d)` are supplied.
* Nonempty frontier counts and positive width facts are supplied.
* This does not synthesize efficient width profiles, product/counting
  hypotheses, ratio regimes, arbitrary normalization, full frozen-form B4, a
  PHP switching lemma, Frege/PHP lower bounds, NP/circuit lower bounds, or
  P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveClassProfile

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open CNFModel
open FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile
open FormulaRecursiveSizeBound
open FormulaRecursiveWidthSchedule
open FormulaSyntacticClassGlobalTree
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

/-! ## Class-envelope arithmetic -/

/-- A recursive frontier count is bounded by a supplied class-size envelope
whenever the raw formula size is. -/
theorem frontierLayerGateCount_le_classSize {n : Nat}
    (F : BDFormula n) (S : Nat -> Nat) (d level : Nat)
    (hSize : formulaSize F <= S d) :
    frontierLayerGateCount F level <= S d :=
  Nat.le_trans (frontierLayerGateCount_le_formulaSize F level) hSize

/-- Monotonicity of the geometric entry-size expression in the gate-count and
width envelopes. -/
theorem geometricEntryBound_of_class_envelopes
    {m M w W rounds n : Nat}
    (hm : m <= M) (hw : w <= W)
    (hn : 2 * (64 * M) ^ rounds * (64 * M * W) <= n) :
    2 * (64 * m) ^ rounds * (64 * m * w) <= n := by
  have h64 : 64 * m <= 64 * M := Nat.mul_le_mul_left 64 hm
  have hpow : (64 * m) ^ rounds <= (64 * M) ^ rounds :=
    Nat.pow_le_pow_left h64 rounds
  have htail : 64 * m * w <= 64 * M * W :=
    Nat.mul_le_mul h64 hw
  have hmain :
      2 * (64 * m) ^ rounds * (64 * m * w) <=
        2 * (64 * M) ^ rounds * (64 * M * W) := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left 2 hpow) htail
  exact Nat.le_trans hmain hn

/-! ## Class-budget geometric consumers for recursive frontier layers -/

open GeneratedRefinedIteratedCertificate in
/-- Single recursive frontier layer under supplied class size/width envelopes,
with the actual final decision tree exposed and bounded by
`t(d,s)=S(d)*(s-1)`.

This is a class-envelope consumer for the raw recursive frontier layer
interface.  It still relies on supplied width-profile and nonempty hypotheses;
it does not synthesize full B4. -/
theorem frontierLayer_geometricCollapseWithClassDepthWidthProfile_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat -> Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hk : level <= depth F)
    (hm : 1 <= frontierLayerGateCount F level)
    (hwLevel : profile.widthBudget level <= W d)
    (hw1 : 1 <= profile.widthBudget level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * W d) <= n) :
    level <= d /\
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
      TreeBudgetFrom (formulaClassDepthTreeBudget S d)
        (frontierLayerGateCount F level) (rounds + 1)
        (geometricSchedule (frontierLayerGateCount F level)
          (n / (64 * frontierLayerGateCount F level *
            profile.widthBudget level)) (rounds + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= formulaClassDepthTreeBudget S d level s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (frontierLayerMinimalLayer F level parent).originalFormula)) := by
  refine And.intro (frontierLevel_le_classDepth F hDepth hk) ?_
  let sched := geometricSchedule (frontierLayerGateCount F level)
    (n / (64 * frontierLayerGateCount F level *
      profile.widthBudget level)) (rounds + 1)
  let L := frontierLayerMinimalLayer F level parent
  have hcount : L.gates.length = frontierLayerGateCount F level := by
    simpa [L] using frontierLayerMinimalLayer_gateCount F level parent
  have hmL : 1 <= L.gates.length := by
    rw [hcount]
    exact hm
  have hwL : forall g, List.Mem g L.gates ->
      widthDNF g.theDNF <= profile.widthBudget level := by
    simpa [L] using profile.gate_width level parent
  have hmClass : frontierLayerGateCount F level <= S d :=
    frontierLayerGateCount_le_classSize F S d level hSize
  have hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        profile.widthBudget level) <= n :=
    geometricEntryBound_of_class_envelopes hmClass hwLevel hn
  have hreg : RegimeFrom (frontierLayerGateCount F level)
      (profile.widthBudget level) (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm hw1 rounds hnLayer
  have hregL : RegimeFrom L.gates.length
      (profile.widthBudget level) (stars (freeRestriction n)) sched := by
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
      (profile.widthBudget level) hmL hwL hregL htL
  have hlen : sched.length = rounds + 1 := by
    simpa [sched] using geometricSchedule_length
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        profile.widthBudget level))
  have htree' : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      (frontierLayerGateCount F level) (rounds + 1) sched := by
    simpa [hcount, hlen] using htree
  have hbgeom :
      sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched] using geometricSchedule_budgets
      (frontierLayerGateCount F level) (rounds + 1)
      (n / (64 * frontierLayerGateCount F level *
        profile.widthBudget level))
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
      subst hmLast
      have hgcRounds :
          cert.stageGateCounts =
            List.replicate (rounds + 1) (frontierLayerGateCount F level) := by
        rw [hgc, hcount, hlen]
      have hdepthClass :
          dtDepth T <= formulaClassDepthTreeBudget S d level s := by
        exact Nat.le_trans hdepth
          (by
            simpa [formulaClassDepthTreeBudget] using
              Nat.mul_le_mul_right (s - 1) hmClass)
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, hlast, heval, hdepthClass, ?_⟩
      · exact hgcRounds
      · rw [hb, hbgeom]
      · simpa [sched, hlen] using hsc
      · simpa [sched] using htree'
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

open GeneratedRefinedIteratedCertificate in
/-- Uniform class-envelope form for every in-depth recursive frontier layer
under a supplied width profile and supplied class-size/width envelopes. -/
theorem allFrontierLayers_geometricCollapseWithClassDepthWidthProfile_finalTree
    {n : Nat} (F : BDFormula n) (S W : Nat -> Nat)
    (d rounds : Nat) (parent : ParentKind)
    (profile : RecursiveFrontierWidthProfile F)
    (hDepth : depth F <= d)
    (hSize : formulaSize F <= S d)
    (hm : forall level, level <= depth F ->
      1 <= frontierLayerGateCount F level)
    (hwLevel : forall level, level <= depth F ->
      profile.widthBudget level <= W d)
    (hw1 : forall level, level <= depth F ->
      1 <= profile.widthBudget level)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * W d) <= n) :
    forall level, level <= depth F ->
      level <= d /\
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
        TreeBudgetFrom (formulaClassDepthTreeBudget S d)
          (frontierLayerGateCount F level) (rounds + 1)
          (geometricSchedule (frontierLayerGateCount F level)
            (n / (64 * frontierLayerGateCount F level *
              profile.widthBudget level)) (rounds + 1)) /\
        exists T : DTree n, exists s : Nat,
          cert.lastStage = some (T, frontierLayerGateCount F level, s) /\
          (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
          dtDepth T <= formulaClassDepthTreeBudget S d level s /\
          (forall a : Assignment n, Agree cert.finalComposed a ->
            dtEval a T = eval a (restrict cert.finalComposed
              (frontierLayerMinimalLayer F level parent).originalFormula)) := by
  intro level hk
  exact
    frontierLayer_geometricCollapseWithClassDepthWidthProfile_finalTree
      F S W d level rounds parent profile hDepth hSize hk
      (hm level hk) (hwLevel level hk) (hw1 level hk) hn

end FormulaRecursiveClassProfile
end PvNP
