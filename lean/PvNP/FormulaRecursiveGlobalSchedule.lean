import PvNP.FormulaRecursiveLayerProfile

/-!
# Recursive frontier layers with a formula-wide tree budget

`FormulaRecursiveLayerProfile` records gate counts, width budgets, and
per-layer tree budgets for the recursive frontier decomposition.  This module
adds the next narrow Gate B interface: each synthesized recursive frontier
layer, and the terminal full-depth bottom layer, can be consumed by the
existing frozen-product schedule theorem while sharing one formula-wide
tree-budget profile.

## HONEST SCOPE STATEMENT (read this)

* The global budget is a max-frontier budget over the already-synthesized
  recursive layers:

    `t_F(d,s) = max_k frontierLayerGateCount F k * (s - 1)`.

  It is global for this formula's recursive layer profile, but it is not an
  efficient asymptotic `t(d,s)` bound independent of the raw formula.
* Intermediate frontier layers still use the truth-table/path-DNF fallback,
  with width budget `n`.
* Product/counting beats are still supplied as `ProductValidFrom`; this module
  does not synthesize them.
* This is not full frozen-form B4, not a Gate A/PHP switching lemma, not a
  Frege/PHP lower bound, not an NP/circuit lower bound, and not a statement
  about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveGlobalSchedule

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveGateLayers
open FormulaRecursiveLayerProfile
open FrozenProductSchedule
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Minimal-layer views of recursive frontiers -/

/-- A synthesized recursive frontier layer under a caller-chosen parent kind. -/
def frontierLayerMinimalLayer {n : Nat} (F : BDFormula n) (k : Nat)
    (p : ParentKind) : MinimalLayeredFormula n where
  parent := p
  gates := ((fullDepthRecursiveGateLayers F).layer k).gates

/-- The original formula represented by the packaged frontier layer is the
chosen parent over the `k`-th recursive frontier formulas. -/
theorem frontierLayerMinimalLayer_originalFormula {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind) :
    (frontierLayerMinimalLayer F k p).originalFormula =
      p.merge (formulaDepthFrontier k F) := by
  change p.merge (((fullDepthRecursiveGateLayers F).layer k).gates.map
      GateSpec.formula) = p.merge (formulaDepthFrontier k F)
  rw [((fullDepthRecursiveGateLayers F).layer k).formulas_eq]

/-- The packaged frontier layer has the recorded recursive frontier gate
count. -/
theorem frontierLayerMinimalLayer_gateCount {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind) :
    (frontierLayerMinimalLayer F k p).gates.length =
      frontierLayerGateCount F k := by
  rfl

/-- The packaged frontier layer inherits the honest intermediate width budget. -/
theorem frontierLayerMinimalLayer_width_le_budget {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind) :
    forall g, g ∈ (frontierLayerMinimalLayer F k p).gates ->
      widthDNF g.theDNF <= frontierLayerWidthBudget F k := by
  simpa [frontierLayerMinimalLayer] using frontierLayer_width_le_budget F k

/-- Every formula in the packaged frontier layer retains the recursive
raw-depth budget. -/
theorem frontierLayerMinimalLayer_formula_depth_add_le {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind) :
    forall g, g ∈ (frontierLayerMinimalLayer F k p).gates ->
      depth g.formula + k <= depth F := by
  intro g hg
  exact fullDepthRecursiveGateLayers_depthBudget F k g.formula
    (List.mem_map_of_mem GateSpec.formula
      (by simpa [frontierLayerMinimalLayer] using hg))

/-! ## Terminal layer as a schedule input -/

/-- The terminal full-depth bottom layer under a caller-chosen parent kind. -/
def terminalLayerMinimalLayer {n : Nat} (F : BDFormula n)
    (p : ParentKind) : MinimalLayeredFormula n where
  parent := p
  gates := (fullDepthRecursiveGateLayers F).terminalBottom.gates

/-- The terminal packaged layer is the chosen parent over the full-depth
frontier formulas. -/
theorem terminalLayerMinimalLayer_originalFormula {n : Nat}
    (F : BDFormula n) (p : ParentKind) :
    (terminalLayerMinimalLayer F p).originalFormula =
      p.merge (formulaDepthFrontier (depth F) F) := by
  change p.merge ((fullDepthRecursiveGateLayers F).terminalBottom.gates.map
      GateSpec.formula) = p.merge (formulaDepthFrontier (depth F) F)
  rw [(fullDepthRecursiveGateLayers F).terminal_formulas_eq]
  rw [((fullDepthRecursiveGateLayers F).layer (depth F)).formulas_eq]

/-- The terminal layer gate count matches the full-depth frontier count. -/
theorem terminalLayerMinimalLayer_gateCount {n : Nat}
    (F : BDFormula n) (p : ParentKind) :
    (terminalLayerMinimalLayer F p).gates.length =
      frontierLayerGateCount F (depth F) := by
  unfold terminalLayerMinimalLayer frontierLayerGateCount
  rw [(fullDepthRecursiveGateLayers F).terminalBottom.gate_count]
  rw [((fullDepthRecursiveGateLayers F).layer (depth F)).count_eq]

/-- The terminal layer inherits the width-one bottom budget. -/
theorem terminalLayerMinimalLayer_width_le_budget {n : Nat}
    (F : BDFormula n) (p : ParentKind) :
    forall g, g ∈ (terminalLayerMinimalLayer F p).gates ->
      widthDNF g.theDNF <= terminalLayerWidthBudget F := by
  simpa [terminalLayerMinimalLayer] using terminalLayer_width_le_budget F

/-! ## One formula-wide max-frontier tree budget -/

/-- Maximum gate count among recursive frontier levels `0..depth F`. -/
def recursiveFrontierMaxGateCount {n : Nat} (F : BDFormula n) : Nat :=
  ((List.range (depth F + 1)).map (frontierLayerGateCount F)).foldr Nat.max 0

private theorem mem_le_foldr_max {xs : List Nat} {x : Nat}
    (hx : x ∈ xs) : x <= xs.foldr Nat.max 0 := by
  induction xs with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · rw [hxy]
        exact Nat.le_max_left y (ys.foldr Nat.max 0)
      · exact Nat.le_trans (ih hxys)
          (Nat.le_max_right y (ys.foldr Nat.max 0))

/-- Any in-depth frontier layer is bounded by the formula-wide maximum. -/
theorem frontierLayerGateCount_le_recursiveFrontierMaxGateCount {n : Nat}
    (F : BDFormula n) {k : Nat} (hk : k <= depth F) :
    frontierLayerGateCount F k <= recursiveFrontierMaxGateCount F := by
  unfold recursiveFrontierMaxGateCount
  apply mem_le_foldr_max
  exact List.mem_map.mpr
    ⟨k, List.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩

/-- Formula-wide global tree budget for the recursive frontier profile. -/
def recursiveFrontierGlobalTreeBudget {n : Nat} (F : BDFormula n)
    (_depth s : Nat) : Nat :=
  recursiveFrontierMaxGateCount F * (s - 1)

private theorem treeBudgetFrom_constant_of_le {m M : Nat} (hm : m <= M) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (fun _depth s => M * (s - 1)) m scheduleDepth sched
  | [], _ => trivial
  | st :: rest, scheduleDepth => by
      refine ⟨?_, treeBudgetFrom_constant_of_le hm rest
        (scheduleDepth - 1)⟩
      cases st with
      | mk s ell =>
          simpa [StageTreeBudget, stageS] using
            Nat.mul_le_mul_right (s - 1) hm

/-- The formula-wide global tree budget satisfies every numeric schedule for
any recursive frontier layer within the raw-depth profile. -/
theorem recursiveFrontierGlobalTreeBudgetFrom {n : Nat}
    (F : BDFormula n) {k : Nat} (hk : k <= depth F) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F k) scheduleDepth sched := by
  intro sched scheduleDepth
  have hm := frontierLayerGateCount_le_recursiveFrontierMaxGateCount F hk
  simpa [recursiveFrontierGlobalTreeBudget] using
    treeBudgetFrom_constant_of_le
      (m := frontierLayerGateCount F k)
      (M := recursiveFrontierMaxGateCount F) hm sched scheduleDepth

/-- Terminal-layer specialization of the formula-wide global tree budget. -/
theorem terminalLayer_globalTreeBudgetFrom {n : Nat} (F : BDFormula n) :
    forall (sched : List ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F (depth F)) scheduleDepth sched :=
  recursiveFrontierGlobalTreeBudgetFrom F (Nat.le_refl (depth F))

/-! ## Frozen-product consumers for synthesized recursive layers -/

open GeneratedRefinedIteratedCertificate in
/-- A recursive frontier layer can consume the existing frozen-product schedule
interface with the formula-wide global tree budget.  Product/counting beats are
still supplied; this theorem only supplies the synthesized layer, width budget,
and `t_F` tree-budget facts. -/
theorem frontierLayer_autoIteratedCollapse_of_globalProductBeats {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind)
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hk : k <= depth F)
    (hbeats : ProductValidFrom B (frontierLayerGateCount F k) n
      sched.length (frontierLayerWidthBudget F k)
      (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (frontierLayerMinimalLayer F k p).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F k) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F k) sched.length sched := by
  let L := frontierLayerMinimalLayer F k p
  have hcount : L.gates.length = frontierLayerGateCount F k := by
    simpa [L] using frontierLayerMinimalLayer_gateCount F k p
  have hwidth : forall g, g ∈ L.gates ->
      widthDNF g.theDNF <= frontierLayerWidthBudget F k := by
    simpa [L] using frontierLayerMinimalLayer_width_le_budget F k p
  have htree : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      (frontierLayerGateCount F k) sched.length sched :=
    recursiveFrontierGlobalTreeBudgetFrom F hk sched sched.length
  have hhyp : FrozenProductHypothesis B (recursiveFrontierGlobalTreeBudget F)
      L.gates.length n sched.length (frontierLayerWidthBudget F k)
      (stars (freeRestriction n)) sched := by
    refine ⟨?_, ?_⟩
    · simpa [hcount] using hbeats
    · simpa [hcount] using htree
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    autoIteratedCollapse_of_frozenProduct B
      (recursiveFrontierGlobalTreeBudget F) sched (freeRestriction n) L
      (frontierLayerWidthBudget F k) hwidth hhyp
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using ht

open GeneratedRefinedIteratedCertificate in
/-- Terminal bottom-layer consumer for the same formula-wide global tree
budget.  The terminal layer uses the sharp width-one budget, but product/counting
beats are still supplied. -/
theorem terminalLayer_autoIteratedCollapse_of_globalProductBeats {n : Nat}
    (F : BDFormula n) (p : ParentKind)
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hbeats : ProductValidFrom B (frontierLayerGateCount F (depth F)) n
      sched.length (terminalLayerWidthBudget F)
      (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (terminalLayerMinimalLayer F p).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F (depth F)) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F (depth F)) sched.length sched := by
  let L := terminalLayerMinimalLayer F p
  have hcount : L.gates.length = frontierLayerGateCount F (depth F) := by
    simpa [L] using terminalLayerMinimalLayer_gateCount F p
  have hwidth : forall g, g ∈ L.gates ->
      widthDNF g.theDNF <= terminalLayerWidthBudget F := by
    simpa [L] using terminalLayerMinimalLayer_width_le_budget F p
  have htree : TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
      (frontierLayerGateCount F (depth F)) sched.length sched :=
    terminalLayer_globalTreeBudgetFrom F sched sched.length
  have hhyp : FrozenProductHypothesis B (recursiveFrontierGlobalTreeBudget F)
      L.gates.length n sched.length (terminalLayerWidthBudget F)
      (stars (freeRestriction n)) sched := by
    refine ⟨?_, ?_⟩
    · simpa [hcount] using hbeats
    · simpa [hcount] using htree
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    autoIteratedCollapse_of_frozenProduct B
      (recursiveFrontierGlobalTreeBudget F) sched (freeRestriction n) L
      (terminalLayerWidthBudget F) hwidth hhyp
  refine ⟨cert, ?_, hb, hsc, ?_⟩
  · rw [hgc, hcount]
  · simpa [hcount] using ht

end FormulaRecursiveGlobalSchedule
end PvNP
