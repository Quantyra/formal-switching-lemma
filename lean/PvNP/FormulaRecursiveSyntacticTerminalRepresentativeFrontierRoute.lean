import Mathlib.Data.List.Dedup
import PvNP.FormulaRecursiveSyntacticTerminalNormalizedViewRoute
import PvNP.FormulaRecursiveFrontierCountRecurrence

/-!
# Representative frontier layers for the normalized-view route

This module adds duplicate-free (free-multiplicity) representative layers to
the restricted nonempty-fanin normalized-view frontier route: a supplied gate
list with the same membership as one recursive frontier may replace the raw
frontier list inside the geometric-collapse payload, and the final decision
tree is still certified against the ORIGINAL parent-merged frontier formula
through a parent-merge evaluation congruence.  Budgets `t(d,s) = S(d)*(s-1)`,
per-stage budget `2`, and the geometric star schedule are unchanged; only the
disclosed representative layer and a transported final clause are new.

Representative layers replace only syntactic duplicate gate copies by
membership-equal lists.  The synthesized route (S2169) adds decidable
syntactic equality for raw formulas and `dedupRepresentativeFrontier`, the
`List.dedup` of the raw frontier, whose representative-layer membership,
duplicate-freeness, and count bounds are proved once and for all, so
consumers no longer take supplied layer lists, membership proofs, or count
obligations.  This is not semantic formula minimization, an arbitrary
bounded-depth collapse theorem, a threshold improvement, full B4,
PHP switching, Frege/PHP, a circuit lower bound, Gate A, or P-versus-NP.

The finite cube/dedup packaging witnesses in this module, including the
coefficient-17 witness below, are NOT switching non-vacuity evidence.  They
exercise only schedule arithmetic and representative-layer packaging.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute

open BoundedDepthCanonicalDT BoundedDepthFrege BoundedDepthIteratedCollapse BoundedDepthLayerView
open BoundedDepthDecisionTree BoundedDepthRestriction CNFModel
open FormulaRecursiveClassProfile FormulaRecursiveDecomposition FormulaRecursiveDepth
open FormulaRecursiveFrontierCountRecurrence FormulaRecursiveGlobalSchedule
open FormulaRecursiveLayerProfile FormulaRecursiveNonempty
open FormulaRecursiveSizeBound FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget
open FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget
open FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget
open FormulaRecursiveSyntacticTerminalNormalizedViewRoute
open FormulaSyntacticDNF FormulaSyntacticDNFNormalization FormulaSyntacticSimpleBridge
open FormulaSyntacticClassGlobalTree FormulaTruthTableView FrozenDepthView
open FrozenProductSchedule FrozenProductScheduleRatio
open GeneratedGoodRestriction GeneratedIteratedCollapseFinal
open GeneratedOneStepDepthReduction GeneratedRefinedCollapse
open GeneratedRefinedIteratedCertificate
open SwitchingEncodeConstruct SwitchingLemmaStatement

/-! ## Representative layers and parent-merge evaluation congruence -/

/-- A representative layer for one frontier: the same gate set as the frontier,
with free multiplicity (duplicates on either side are irrelevant). -/
def RepresentativeFrontierLayer {n : Nat} (F : BDFormula n) (level : Nat)
    (gs : List (BDFormula n)) : Prop :=
  (∀ G, G ∈ gs → G ∈ formulaDepthFrontier level F) ∧
  (∀ G, G ∈ formulaDepthFrontier level F → G ∈ gs)

private theorem list_all_congr_of_mem_iff {α : Type _} {xs ys : List α}
    (f : α → Bool) (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    xs.all f = ys.all f := by
  cases hys : ys.all f with
  | true =>
      rw [List.all_eq_true] at hys ⊢
      intro x hx
      exact hys x ((h x).mp hx)
  | false =>
      cases hxs : xs.all f with
      | true =>
          rw [List.all_eq_true] at hxs
          have hy : ys.all f = true :=
            List.all_eq_true.mpr fun x hx => hxs x ((h x).mpr hx)
          rw [hy] at hys
          cases hys
      | false => rfl

private theorem list_any_congr_of_mem_iff {α : Type _} {xs ys : List α}
    (f : α → Bool) (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    xs.any f = ys.any f := by
  cases hys : ys.any f with
  | true =>
      rw [List.any_eq_true] at hys ⊢
      rcases hys with ⟨x, hx, hfx⟩
      exact ⟨x, (h x).mpr hx, hfx⟩
  | false =>
      cases hxs : xs.any f with
      | true =>
          rw [List.any_eq_true] at hxs
          rcases hxs with ⟨x, hx, hfx⟩
          have hy : ys.any f = true :=
            List.any_eq_true.mpr ⟨x, (h x).mp hx, hfx⟩
          rw [hy] at hys
          cases hys
      | false => rfl

private theorem list_all_map_id {α : Type _} (xs : List α) (p : α → Bool) :
    (xs.map p).all id = xs.all p := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem list_any_map_id {α : Type _} (xs : List α) (p : α → Bool) :
    (xs.map p).any id = xs.any p := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Parent-merge evaluation only sees child membership: merging two
membership-equal child lists evaluates identically, with free multiplicity on
both sides. -/
theorem eval_parentMerge_congr_of_mem_iff {n : Nat} (a : Assignment n)
    (k : ParentKind) {xs ys : List (BDFormula n)}
    (h : ∀ G, G ∈ xs ↔ G ∈ ys) :
    eval a (k.merge xs) = eval a (k.merge ys) := by
  rw [ParentKind.eval_merge, ParentKind.eval_merge]
  cases k with
  | and =>
      show (xs.map (fun F => eval a F)).all id =
        (ys.map (fun F => eval a F)).all id
      rw [list_all_map_id, list_all_map_id]
      exact list_all_congr_of_mem_iff (fun F => eval a F) h
  | or =>
      show (xs.map (fun F => eval a F)).any id =
        (ys.map (fun F => eval a F)).any id
      rw [list_any_map_id, list_any_map_id]
      exact list_any_congr_of_mem_iff (fun F => eval a F) h

/-- Restricted transport of the parent-merge congruence along any assignment
that agrees with the restriction, via `eval_restrict` on both sides. -/
theorem eval_restrict_parentMerge_congr_of_mem_iff {n : Nat} (ρ : Restriction n)
    (a : Assignment n) (k : ParentKind) {xs ys : List (BDFormula n)}
    (ha : Agree ρ a) (h : ∀ G, G ∈ xs ↔ G ∈ ys) :
    eval a (restrict ρ (k.merge xs)) = eval a (restrict ρ (k.merge ys)) := by
  rw [eval_restrict ρ a (k.merge xs) ha, eval_restrict ρ a (k.merge ys) ha]
  exact eval_parentMerge_congr_of_mem_iff a k h

/-! ## Representative minimal layers -/

/-- The minimal layered view of a supplied representative gate list, each gate
packaged through its unconditional normalized DNF view. -/
def representativeMinimalLayer {n : Nat} (gs : List (BDFormula n))
    (parent : ParentKind) : MinimalLayeredFormula n where
  parent := parent
  gates := gs.map normalizedFormulaGate

theorem representativeMinimalLayer_originalFormula {n : Nat}
    (gs : List (BDFormula n)) (parent : ParentKind) :
    (representativeMinimalLayer gs parent).originalFormula =
      parent.merge gs := by
  have hm : (gs.map normalizedFormulaGate).map GateSpec.formula = gs := by
    induction gs with
    | nil => rfl
    | cons G rest ih => simp [normalizedFormulaGate_formula, ih]
  exact congrArg (fun xs => parent.merge xs) hm

theorem representativeMinimalLayer_gateCount {n : Nat}
    (gs : List (BDFormula n)) (parent : ParentKind) :
    (representativeMinimalLayer gs parent).gates.length = gs.length := by
  simp [representativeMinimalLayer]

private theorem nat_le_foldr_max_of_mem (xs : List Nat) {x : Nat}
    (hx : x ∈ xs) : x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- Every gate of a frontier-contained representative layer obeys the actual
normalized-frontier DNF width schedule of that frontier. -/
theorem representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
    {n : Nat} (F : BDFormula n) (level : Nat) {gs : List (BDFormula n)}
    (hsub : ∀ G, G ∈ gs → G ∈ formulaDepthFrontier level F)
    (parent : ParentKind) (g : GateSpec n)
    (hg : g ∈ (representativeMinimalLayer gs parent).gates) :
    widthDNF g.theDNF ≤ normalizedFrontierWidthSchedule F level := by
  simp only [representativeMinimalLayer] at hg
  rcases List.mem_map.mp hg with ⟨G, hG, rfl⟩
  exact Nat.le_trans
    (nat_le_foldr_max_of_mem _
      (List.mem_map_of_mem (fun G => widthDNF (normalizedDNFView G).D)
        (hsub G hG)))
    (Nat.le_max_right _ _)

/-- A representative layer of an in-depth frontier of a nonempty-fanin formula
is itself nonempty. -/
theorem representative_length_pos {n : Nat} {F : BDFormula n} {level : Nat}
    {gs : List (BDFormula n)} (hNE : NonemptyFaninFormula F)
    (hk : level ≤ depth F) (hrep : RepresentativeFrontierLayer F level gs) :
    1 ≤ gs.length := by
  have hcount : 1 ≤ frontierLayerGateCount F level :=
    frontierLayerGateCount_nonempty_of_noEmptyFanins F level
      (nonemptyFanin_noEmptyFanins hNE) hk
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length] at hcount
  cases hfr : formulaDepthFrontier level F with
  | nil =>
      rw [hfr] at hcount
      simp at hcount
  | cons G rest =>
      have hG : G ∈ gs := hrep.2 G (by rw [hfr]; exact List.mem_cons_self G rest)
      exact Nat.succ_le_of_lt (List.length_pos_of_mem hG)

/-! ## Representative final-tree payload and consumers -/

private theorem treeBudgetFrom_classDepth_of_le {m : Nat} (S : Nat → Nat)
    (d : Nat) (hm : m ≤ S d) :
    ∀ (sched : List ScheduledAutoCollapse.ScheduleStage) (scheduleDepth : Nat),
      TreeBudgetFrom (formulaClassDepthTreeBudget S d) m scheduleDepth sched
  | [], _ => trivial
  | st :: rest, scheduleDepth => by
      refine And.intro ?_ (treeBudgetFrom_classDepth_of_le S d hm rest
        (scheduleDepth - 1))
      cases st with
      | mk s ell =>
          simpa [formulaClassDepthTreeBudget, StageTreeBudget, stageS] using
            Nat.mul_le_mul_right (s - 1) hm

/-- The unchanged final-tree payload over a representative layer, with the
final clause transported to the ORIGINAL parent-merged frontier formula. -/
def RepresentativeNormalizedViewClassDepthFinalTreeAt {n : Nat} (F : BDFormula n)
    (S W : Nat → Nat) (d rounds : Nat) (parent : ParentKind) (level : Nat)
    (gs : List (BDFormula n)) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (representativeMinimalLayer gs parent).originalFormula
      (geometricSchedule gs.length (n / (64 * gs.length * W level)) (rounds + 1)).length,
    cert.stageGateCounts = List.replicate (rounds + 1) gs.length ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts = (geometricSchedule gs.length
      (n / (64 * gs.length * W level)) (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d) gs.length (rounds + 1)
      (geometricSchedule gs.length (n / (64 * gs.length * W level)) (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, gs.length, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (parent.merge (formulaDepthFrontier level F))))

/-- Tight-entry supplied-width consumer over a representative layer.  The
certificate is built over the duplicate-free layer while its final tree is
still certified against the original parent-merged frontier formula. -/
theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (_hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level)
    (hn : 2 * (64 * gs.length) ^ rounds * (64 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAt F S W d rounds parent
      level gs := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule gs.length (n / (64 * gs.length * w)) (rounds + 1)
  let L := representativeMinimalLayer gs parent
  have hc : L.gates.length = gs.length := by
    simpa [L] using representativeMinimalLayer_gateCount gs parent
  have hm : 1 ≤ gs.length := representative_length_pos hNE hk hrep
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact treeBudgetFrom_classDepth_of_le S d hcount sched sched.length
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (formulaClassDepthTreeBudget S d) sched (freeRestriction n) L
      w hmL hwL hreg ht
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule_length gs.length (rounds + 1)
      (n / (64 * gs.length * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule_budgets gs.length (rounds + 1)
      (n / (64 * gs.length * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = gs.length := by
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
          simpa [formulaClassDepthTreeBudget] using
            Nat.mul_le_mul_right (s - 1) hcount)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]
        have horig : L.originalFormula = parent.merge gs :=
          representativeMinimalLayer_originalFormula gs parent
        exact (congrArg (fun G => eval a (restrict cert.finalComposed G))
          horig).trans
          (eval_restrict_parentMerge_congr_of_mem_iff cert.finalComposed a
            parent ha (fun G => ⟨hrep.1 G, hrep.2 G⟩))

/-- All-level tight-entry supplied-width representative consumer: one
representative layer and one frontier-local obligation set per level. -/
theorem allRepresentativeFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (gsAll : Nat → List (BDFormula n))
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F)
    (hrepAll : ∀ level, level ≤ depth F →
      RepresentativeFrontierLayer F level (gsAll level))
    (hcountAll : ∀ level, level ≤ depth F → (gsAll level).length ≤ S d)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g ∈ (representativeMinimalLayer (gsAll level) parent).gates,
        widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (gsAll level).length) ^ rounds *
        (64 * (gsAll level).length * W level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAt F S W d rounds parent
        level (gsAll level) := by
  intro level hk
  exact representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S W d level rounds parent (gsAll level) (hrepAll level hk) hDepth hSize
      hNE hk (hcountAll level hk) (hwAll level hk) (hwPos level hk)
      (hnAll level hk)

/-- Class-derived single-level representative wrapper using the actual
normalized-frontier DNF width schedule of the represented frontier. -/
theorem representativeFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hn : 2 * (64 * gs.length) ^ rounds *
      (64 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAt F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs := by
  apply representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S (normalizedFrontierWidthSchedule F) d level rounds parent gs hrep
      hDepth hSize hNE hk hcount
  · exact fun g hg =>
      representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
        F level hrep.1 parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

/-- Class-derived all-level representative wrapper using the actual
normalized-frontier DNF width schedule. -/
theorem allRepresentativeFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (gsAll : Nat → List (BDFormula n))
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hrepAll : ∀ level, level ≤ depth F →
      RepresentativeFrontierLayer F level (gsAll level))
    (hcountAll : ∀ level, level ≤ depth F → (gsAll level).length ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (gsAll level).length) ^ rounds *
        (64 * (gsAll level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAt F S
        (normalizedFrontierWidthSchedule F) d rounds parent level (gsAll level) := by
  intro level hk
  exact representativeFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth
    F S d level rounds parent (gsAll level) (hrepAll level hk) hNE hDepth hSize
      hk (hcountAll level hk) (hnAll level hk)

/-! ## Uniform coefficient-32 consumers (S2171) -/

/-- Representative final-tree payload for the schedule that divides by
`32*m` uniformly at every stage. -/
def RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 {n : Nat}
    (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (level : Nat) (gs : List (BDFormula n)) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (representativeMinimalLayer gs parent).originalFormula
      (geometricSchedule32 gs.length (n / (32 * gs.length * W level))
        (rounds + 1)).length,
    cert.stageGateCounts = List.replicate (rounds + 1) gs.length ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts = (geometricSchedule32 gs.length
      (n / (32 * gs.length * W level)) (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d) gs.length (rounds + 1)
      (geometricSchedule32 gs.length (n / (32 * gs.length * W level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, gs.length, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (parent.merge (formulaDepthFrontier level F))))

theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform32
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (_hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level) (hw1 : 1 ≤ W level)
    (hn : 2 * (32 * gs.length) ^ rounds * (32 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 F S W d rounds parent
      level gs := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule32 gs.length (n / (32 * gs.length * w)) (rounds + 1)
  let L := representativeMinimalLayer gs parent
  have hc : L.gates.length = gs.length := by
    simpa [L] using representativeMinimalLayer_gateCount gs parent
  have hm : 1 ≤ gs.length := representative_length_pos hNE hk hrep
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound32 hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact treeBudgetFrom_classDepth_of_le S d hcount sched sched.length
  obtain ⟨cert, hgc, hb, hsc, htree⟩ := autoIteratedCollapse_of_ratioRegime
    (formulaClassDepthTreeBudget S d) sched (freeRestriction n) L w hmL hwL hreg ht
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule32_length gs.length (rounds + 1)
      (n / (32 * gs.length * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule32_budgets gs.length (rounds + 1)
      (n / (32 * gs.length * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = gs.length := by
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
          simpa [formulaClassDepthTreeBudget] using
            Nat.mul_le_mul_right (s - 1) hcount)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]
        have horig : L.originalFormula = parent.merge gs :=
          representativeMinimalLayer_originalFormula gs parent
        exact (congrArg (fun G => eval a (restrict cert.finalComposed G)) horig).trans
          (eval_restrict_parentMerge_congr_of_mem_iff cert.finalComposed a parent ha
            (fun G => ⟨hrep.1 G, hrep.2 G⟩))

theorem representativeFrontier_geometricCollapse_finalTree_uniform32_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F) (hcount : gs.length ≤ S d)
    (hn : 2 * (32 * gs.length) ^ rounds *
      (32 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs := by
  apply representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform32
    F S (normalizedFrontierWidthSchedule F) d level rounds parent gs hrep
      hDepth hSize hNE hk hcount
  · exact fun g hg => representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
      F level hrep.1 parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

/-! ## Uniform coefficient-17 consumers (S2175 Gate B Route C1) -/

/-- Representative payload for the parallel coefficient-17 schedule. -/
def RepresentativeNormalizedViewClassDepthFinalTreeAtUniform17 {n : Nat}
    (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (level : Nat) (gs : List (BDFormula n)) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (representativeMinimalLayer gs parent).originalFormula
      (geometricSchedule17 gs.length (n / (17 * gs.length * W level))
        (rounds + 1)).length,
    cert.stageGateCounts = List.replicate (rounds + 1) gs.length ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts = (geometricSchedule17 gs.length
      (n / (17 * gs.length * W level)) (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d) gs.length (rounds + 1)
      (geometricSchedule17 gs.length (n / (17 * gs.length * W level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, gs.length, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (parent.merge (formulaDepthFrontier level F))))

theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform17
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (_hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level) (hw1 : 1 ≤ W level)
    (hn : 2 * (17 * gs.length) ^ rounds * (17 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform17 F S W d rounds parent
      level gs := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule17 gs.length (n / (17 * gs.length * w)) (rounds + 1)
  let L := representativeMinimalLayer gs parent
  have hc : L.gates.length = gs.length := by
    simpa [L] using representativeMinimalLayer_gateCount gs parent
  have hm : 1 ≤ gs.length := representative_length_pos hNE hk hrep
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom17 L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound17 hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact treeBudgetFrom_classDepth_of_le S d hcount sched sched.length
  obtain ⟨cert, hgc, hb, hsc⟩ := ScheduledAutoCollapse.autoIteratedCollapse
    sched (freeRestriction n) L w hwL
      (regimeFrom17_validFrom hmL sched w (stars (freeRestriction n))
        (stars_le (freeRestriction n)) hreg)
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule17_length gs.length (rounds + 1)
      (n / (17 * gs.length * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule17_budgets gs.length (rounds + 1)
      (n / (17 * gs.length * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = gs.length := by
        have := lastStage_gateCount_of_stageGateCounts_replicate cert hgc T m s hlast
        simpa [hc] using this
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, ?_, heval, ?_, ?_⟩
      · rw [hgc, hc, hlen]
      · rw [hb]
        simpa [stageS] using hbgeom
      · simpa [stageStars, sched, w, hlen] using hsc
      · simpa [hc, sched, w, hlen] using ht
      · simpa [hc] using hlast
      · exact Nat.le_trans hdepth (by
          simpa [formulaClassDepthTreeBudget] using
            Nat.mul_le_mul_right (s - 1) hcount)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]
        have horig : L.originalFormula = parent.merge gs :=
          representativeMinimalLayer_originalFormula gs parent
        exact (congrArg (fun G => eval a (restrict cert.finalComposed G)) horig).trans
          (eval_restrict_parentMerge_congr_of_mem_iff cert.finalComposed a parent ha
            (fun G => ⟨hrep.1 G, hrep.2 G⟩))

theorem representativeFrontier_geometricCollapse_finalTree_uniform17_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F) (hcount : gs.length ≤ S d)
    (hn : 2 * (17 * gs.length) ^ rounds *
      (17 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform17 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs := by
  apply representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform17
    F S (normalizedFrontierWidthSchedule F) d level rounds parent gs hrep
      hDepth hSize hNE hk hcount
  · exact fun g hg => representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
      F level hrep.1 parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

/-! ## Uniform coefficient-16 consumers (S2176 factor-4 ambient-8192) -/

/-- Representative payload for the parallel coefficient-16 schedule. -/
def RepresentativeNormalizedViewClassDepthFinalTreeAtUniform16 {n : Nat}
    (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (level : Nat) (gs : List (BDFormula n)) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (representativeMinimalLayer gs parent).originalFormula
      (geometricSchedule16 gs.length (n / (16 * gs.length * W level))
        (rounds + 1)).length,
    cert.stageGateCounts = List.replicate (rounds + 1) gs.length ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts = (geometricSchedule16 gs.length
      (n / (16 * gs.length * W level)) (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d) gs.length (rounds + 1)
      (geometricSchedule16 gs.length (n / (16 * gs.length * W level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, gs.length, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (parent.merge (formulaDepthFrontier level F))))

theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform16
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (_hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level) (hw1 : 1 ≤ W level)
    (hn : 2 * (16 * gs.length) ^ rounds * (16 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform16 F S W d rounds parent
      level gs := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule16 gs.length (n / (16 * gs.length * w)) (rounds + 1)
  let L := representativeMinimalLayer gs parent
  have hc : L.gates.length = gs.length := by
    simpa [L] using representativeMinimalLayer_gateCount gs parent
  have hm : 1 ≤ gs.length := representative_length_pos hNE hk hrep
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom16 L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound16 hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact treeBudgetFrom_classDepth_of_le S d hcount sched sched.length
  obtain ⟨cert, hgc, hb, hsc⟩ := ScheduledAutoCollapse.autoIteratedCollapse
    sched (freeRestriction n) L w hwL
      (regimeFrom16_validFrom4 hmL sched w (stars (freeRestriction n))
        (stars_le (freeRestriction n)) hreg)
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule16_length gs.length (rounds + 1)
      (n / (16 * gs.length * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule16_budgets gs.length (rounds + 1)
      (n / (16 * gs.length * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = gs.length := by
        have := lastStage_gateCount_of_stageGateCounts_replicate cert hgc T m s hlast
        simpa [hc] using this
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, ?_, heval, ?_, ?_⟩
      · rw [hgc, hc, hlen]
      · rw [hb]
        simpa [stageS] using hbgeom
      · simpa [stageStars, sched, w, hlen] using hsc
      · simpa [hc, sched, w, hlen] using ht
      · simpa [hc] using hlast
      · exact Nat.le_trans hdepth (by
          simpa [formulaClassDepthTreeBudget] using
            Nat.mul_le_mul_right (s - 1) hcount)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]
        have horig : L.originalFormula = parent.merge gs :=
          representativeMinimalLayer_originalFormula gs parent
        exact (congrArg (fun G => eval a (restrict cert.finalComposed G)) horig).trans
          (eval_restrict_parentMerge_congr_of_mem_iff cert.finalComposed a parent ha
            (fun G => ⟨hrep.1 G, hrep.2 G⟩))

theorem representativeFrontier_geometricCollapse_finalTree_uniform16_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F) (hcount : gs.length ≤ S d)
    (hn : 2 * (16 * gs.length) ^ rounds *
      (16 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform16 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs := by
  apply representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform16
    F S (normalizedFrontierWidthSchedule F) d level rounds parent gs hrep
      hDepth hSize hNE hk hcount
  · exact fun g hg => representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
      F level hrep.1 parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

/-! ## Uniform coefficient-9 consumers (S2177 Route A-sharp ambient-1458) -/

/-- Representative payload for the parallel coefficient-9 schedule. -/
def RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 {n : Nat}
    (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (level : Nat) (gs : List (BDFormula n)) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (representativeMinimalLayer gs parent).originalFormula
      (geometricSchedule9 gs.length (n / (9 * gs.length * W level))
        (rounds + 1)).length,
    cert.stageGateCounts = List.replicate (rounds + 1) gs.length ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts = (geometricSchedule9 gs.length
      (n / (9 * gs.length * W level)) (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d) gs.length (rounds + 1)
      (geometricSchedule9 gs.length (n / (9 * gs.length * W level))
        (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, gs.length, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (parent.merge (formulaDepthFrontier level F))))

theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform9
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (_hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level) (hw1 : 1 ≤ W level)
    (hn : 2 * (9 * gs.length) ^ rounds * (9 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 F S W d rounds parent
      level gs := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule9 gs.length (n / (9 * gs.length * w)) (rounds + 1)
  let L := representativeMinimalLayer gs parent
  have hc : L.gates.length = gs.length := by
    simpa [L] using representativeMinimalLayer_gateCount gs parent
  have hm : 1 ≤ gs.length := representative_length_pos hNE hk hrep
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom9 L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound9 hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact treeBudgetFrom_classDepth_of_le S d hcount sched sched.length
  obtain ⟨cert, hgc, hb, hsc⟩ := ScheduledAutoCollapse.autoIteratedCollapse
    sched (freeRestriction n) L w hwL
      (regimeFrom9_validFrom4 hmL sched w (stars (freeRestriction n))
        (stars_le (freeRestriction n)) hreg)
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule9_length gs.length (rounds + 1)
      (n / (9 * gs.length * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule9_budgets gs.length (rounds + 1)
      (n / (9 * gs.length * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = gs.length := by
        have := lastStage_gateCount_of_stageGateCounts_replicate cert hgc T m s hlast
        simpa [hc] using this
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst m
      refine ⟨cert, ?_, ?_, ?_, ?_, T, s, ?_, heval, ?_, ?_⟩
      · rw [hgc, hc, hlen]
      · rw [hb]
        simpa [stageS] using hbgeom
      · simpa [stageStars, sched, w, hlen] using hsc
      · simpa [hc, sched, w, hlen] using ht
      · simpa [hc] using hlast
      · exact Nat.le_trans hdepth (by
          simpa [formulaClassDepthTreeBudget] using
            Nat.mul_le_mul_right (s - 1) hcount)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]
        have horig : L.originalFormula = parent.merge gs :=
          representativeMinimalLayer_originalFormula gs parent
        exact (congrArg (fun G => eval a (restrict cert.finalComposed G)) horig).trans
          (eval_restrict_parentMerge_congr_of_mem_iff cert.finalComposed a parent ha
            (fun G => ⟨hrep.1 G, hrep.2 G⟩))

theorem representativeFrontier_geometricCollapse_finalTree_uniform9_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F) (hcount : gs.length ≤ S d)
    (hn : 2 * (9 * gs.length) ^ rounds *
      (9 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs := by
  apply representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_uniform9
    F S (normalizedFrontierWidthSchedule F) d level rounds parent gs hrep
      hDepth hSize hNE hk hcount
  · exact fun g hg => representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
      F level hrep.1 parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

/-! ## Coefficient-32 entry-star consumers (S2170) -/

/-- The parallel coefficient-32 entry-star payload.  Its conjunction and
final-tree clauses are identical to the legacy payload; only entry stars use
the tighter divisor. -/
def RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar {n : Nat}
    (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (level : Nat) (gs : List (BDFormula n)) : Prop :=
  level ≤ d ∧
  ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
      (representativeMinimalLayer gs parent).originalFormula
      (geometricSchedule gs.length (n / (32 * gs.length * W level)) (rounds + 1)).length,
    cert.stageGateCounts = List.replicate (rounds + 1) gs.length ∧
    cert.stageBudgets = List.replicate (rounds + 1) 2 ∧
    cert.stageStarCounts = (geometricSchedule gs.length
      (n / (32 * gs.length * W level)) (rounds + 1)).map stageStars ∧
    TreeBudgetFrom (formulaClassDepthTreeBudget S d) gs.length (rounds + 1)
      (geometricSchedule gs.length (n / (32 * gs.length * W level)) (rounds + 1)) ∧
    ∃ T : DTree n, ∃ s : Nat,
      cert.lastStage = some (T, gs.length, s) ∧
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
      dtDepth T ≤ formulaClassDepthTreeBudget S d level s ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        dtEval a T = eval a (restrict cert.finalComposed
          (parent.merge (formulaDepthFrontier level F))))

/-- Representative consumer with entry stars `n/(32*m*w)` and the matching
coefficient-`32` ambient product. -/
theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (_hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level)
    (hn : 2 * (64 * gs.length) ^ rounds * (32 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S W d rounds parent
      level gs := by
  refine ⟨frontierLevel_le_classDepth F hDepth hk, ?_⟩
  let w := W level
  let sched := geometricSchedule gs.length (n / (32 * gs.length * w)) (rounds + 1)
  let L := representativeMinimalLayer gs parent
  have hc : L.gates.length = gs.length := by
    simpa [L] using representativeMinimalLayer_gateCount gs parent
  have hm : 1 ≤ gs.length := representative_length_pos hNE hk hrep
  have hmL : 1 ≤ L.gates.length := by simpa [hc] using hm
  have hwL : ∀ g ∈ L.gates, widthDNF g.theDNF ≤ w := by simpa [L, w] using hw
  have hreg : RegimeFrom L.gates.length w (stars (freeRestriction n)) sched := by
    rw [hc, stars_freeRestriction]
    exact geometric_regime_of_bound_tightEntry hm (by simpa [w] using hw1) rounds
      (by simpa [w] using hn)
  have ht : TreeBudgetFrom (formulaClassDepthTreeBudget S d)
      L.gates.length sched.length sched := by
    rw [hc]
    exact treeBudgetFrom_classDepth_of_le S d hcount sched sched.length
  obtain ⟨cert, hgc, hb, hsc, htree⟩ :=
    autoIteratedCollapse_of_ratioRegime
      (formulaClassDepthTreeBudget S d) sched (freeRestriction n) L
      w hmL hwL hreg ht
  have hlen : sched.length = rounds + 1 := by
    simpa [sched, w] using geometricSchedule_length gs.length (rounds + 1)
      (n / (32 * gs.length * w))
  have hbgeom : sched.map stageS = List.replicate (rounds + 1) 2 := by
    simpa [sched, w] using geometricSchedule_budgets gs.length (rounds + 1)
      (n / (32 * gs.length * w))
  have hsome := lastStage_isSome cert (by rw [hlen]; exact Nat.succ_pos rounds)
  cases hlast : cert.lastStage with
  | none => simp [hlast] at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = gs.length := by
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
          simpa [formulaClassDepthTreeBudget] using
            Nat.mul_le_mul_right (s - 1) hcount)
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]
        have horig : L.originalFormula = parent.merge gs :=
          representativeMinimalLayer_originalFormula gs parent
        exact (congrArg (fun G => eval a (restrict cert.finalComposed G))
          horig).trans
          (eval_restrict_parentMerge_congr_of_mem_iff cert.finalComposed a
            parent ha (fun G => ⟨hrep.1 G, hrep.2 G⟩))

theorem allRepresentativeFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (gsAll : Nat → List (BDFormula n))
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F)
    (hrepAll : ∀ level, level ≤ depth F → RepresentativeFrontierLayer F level (gsAll level))
    (hcountAll : ∀ level, level ≤ depth F → (gsAll level).length ≤ S d)
    (hwAll : ∀ level, level ≤ depth F → ∀ g ∈ (representativeMinimalLayer (gsAll level) parent).gates, widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (gsAll level).length) ^ rounds * (32 * (gsAll level).length * W level) ≤ n) :
    ∀ level, level ≤ depth F → RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar
      F S W d rounds parent level (gsAll level) := by
  intro level hk
  exact representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    F S W d level rounds parent (gsAll level) (hrepAll level hk) hDepth hSize hNE hk
      (hcountAll level hk) (hwAll level hk) (hwPos level hk) (hnAll level hk)

theorem representativeFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F) (hcount : gs.length ≤ S d)
    (hn : 2 * (64 * gs.length) ^ rounds *
      (32 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs := by
  apply representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    F S (normalizedFrontierWidthSchedule F) d level rounds parent gs hrep
      hDepth hSize hNE hk hcount
  · exact fun g hg => representativeMinimalLayer_width_le_normalizedFrontierWidthSchedule
      F level hrep.1 parent g hg
  · exact normalizedFrontierWidthSchedule_pos F level
  · exact hn

theorem allRepresentativeFrontiers_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (gsAll : Nat → List (BDFormula n))
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hrepAll : ∀ level, level ≤ depth F → RepresentativeFrontierLayer F level (gsAll level))
    (hcountAll : ∀ level, level ≤ depth F → (gsAll level).length ≤ S d)
    (hnAll : ∀ level, level ≤ depth F → 2 * (64 * (gsAll level).length) ^ rounds *
      (32 * (gsAll level).length * normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F → RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
      (normalizedFrontierWidthSchedule F) d rounds parent level (gsAll level) := by
  intro level hk
  exact representativeFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    F S d level rounds parent (gsAll level) (hrepAll level hk) hNE hDepth hSize hk
      (hcountAll level hk) (hnAll level hk)

/-! ## Duplicated-square witness at ambient `2^19` (S2167) -/

private def dupSquareInner19 : BDFormula 524288 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

/-- `(x₀ ∧ x₀) ∧ (x₀ ∧ x₀)` at ambient `2^19`: every frontier layer consists of
syntactic duplicate copies of one gate. -/
def dupSquareWitness19 : BDFormula 524288 :=
  .and [dupSquareInner19, dupSquareInner19]

/-- Per-level representative layers for `dupSquareWitness19`: the root, the
single duplicated inner gate, and the single literal.  Levels beyond the depth
reuse the literal layer so the definition is total; only levels `≤ 2` are
consumed. -/
def dupSquareRepLayer19 : Nat → List (BDFormula 524288)
  | 0 => [dupSquareWitness19]
  | 1 => [dupSquareInner19]
  | _ + 2 => [.lit { var := ⟨0, by decide⟩, sign := true }]

private theorem dupSquareRepLayer19_zero_eq :
    dupSquareRepLayer19 0 = [dupSquareWitness19] := rfl

private theorem dupSquareRepLayer19_one_eq :
    dupSquareRepLayer19 1 = [dupSquareInner19] := rfl

private theorem dupSquareRepLayer19_two_eq :
    dupSquareRepLayer19 2 =
      [.lit { var := ⟨0, by decide⟩, sign := true }] := rfl

private theorem dupSquareInner19_nonempty :
    NonemptyFaninFormula dupSquareInner19 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner19] at hG
  subst hG
  exact .lit _

theorem dupSquareWitness19_nonemptyFanin :
    NonemptyFaninFormula dupSquareWitness19 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness19] at hG
  subst hG
  exact dupSquareInner19_nonempty

private theorem dupSquareWitness19_syntacticDNF_eq :
    syntacticDNF dupSquareWitness19 =
      [[{ var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true }]] := by
  simp [dupSquareWitness19, dupSquareInner19, syntacticDNF, syntacticAndDNF,
    andDNF, FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF]

/-- The raw syntactic expansion of the witness is not simple: its only term is
the repeated-variable term `[x₀, x₀, x₀, x₀]`. -/
theorem dupSquareWitness19_syntacticDNF_not_simple :
    ¬ SimpleDNF (syntacticDNF dupSquareWitness19) := by
  intro h
  have ht : ([{ var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true }] : Term 524288) ∈
      syntacticDNF dupSquareWitness19 := by
    rw [dupSquareWitness19_syntacticDNF_eq]
    exact List.mem_cons_self _ _
  have hs := h _ ht
  simp [SimpleTerm] at hs

theorem dupSquareWitness19_formulaSize :
    formulaSize dupSquareWitness19 = 7 := by
  simp [dupSquareWitness19, dupSquareInner19, formulaSize_and, formulaSize_lit]

theorem dupSquareWitness19_depth : depth dupSquareWitness19 = 2 := by
  simp [dupSquareWitness19, dupSquareInner19, depth]

theorem dupSquareWitness19_recurrenceWidth :
    formulaRecurrenceWidth dupSquareWitness19 = 4 := by
  simp [dupSquareWitness19, dupSquareInner19, formulaRecurrenceWidth_and,
    formulaRecurrenceWidth_lit]

theorem dupSquareWitness19_frontierGateCount_zero :
    frontierLayerGateCount dupSquareWitness19 0 = 1 :=
  frontierLayerGateCount_zero dupSquareWitness19

theorem dupSquareWitness19_frontierGateCount_one :
    frontierLayerGateCount dupSquareWitness19 1 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem dupSquareWitness19_frontierGateCount_two :
    frontierLayerGateCount dupSquareWitness19 2 = 4 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

/-- The witness's normalized DNF view has width exactly `1`: the normalized
DNF is a genuine width-`1` DNF rather than the empty DNF, so the schedule
value `1` below is not only the `max 1 0` fallback. -/
theorem dupSquareWitness19_normalizedWidth :
    widthDNF (normalizedDNFView dupSquareWitness19).D = 1 := by
  rw [normalizedDNFView_D, dupSquareWitness19_syntacticDNF_eq]
  rfl

private theorem dupSquareInner19_syntacticDNF_eq :
    syntacticDNF dupSquareInner19 =
      [[{ var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true }]] := by
  simp [dupSquareInner19, syntacticDNF, syntacticAndDNF, andDNF,
    FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF]

private theorem dupSquareInner19_normalizedWidth :
    widthDNF (normalizedDNFView dupSquareInner19).D = 1 := by
  rw [normalizedDNFView_D, dupSquareInner19_syntacticDNF_eq]
  rfl

private theorem litGate19_syntacticDNF_eq :
    syntacticDNF
      (.lit { var := 0, sign := true } : BDFormula 524288) =
      [[{ var := 0, sign := true }]] := by
  simp [syntacticDNF, FormulaSyntacticDNF.literalDNF]

private theorem litGate19_normalizedWidth :
    widthDNF (normalizedDNFView
      (.lit { var := 0, sign := true } : BDFormula 524288)).D = 1 := by
  rw [normalizedDNFView_D, litGate19_syntacticDNF_eq]
  rfl

theorem dupSquareWitness19_normalizedFrontierWidthSchedule_zero :
    normalizedFrontierWidthSchedule dupSquareWitness19 0 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    formulaDepthFrontier, depthFrontier, dupSquareWitness19_normalizedWidth]

theorem dupSquareWitness19_normalizedFrontierWidthSchedule_one :
    normalizedFrontierWidthSchedule dupSquareWitness19 1 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    dupSquareWitness19, formulaDepthFrontier, depthFrontier, topChildren,
    dupSquareInner19_normalizedWidth]

theorem dupSquareWitness19_normalizedFrontierWidthSchedule_two :
    normalizedFrontierWidthSchedule dupSquareWitness19 2 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    dupSquareWitness19, dupSquareInner19, formulaDepthFrontier, depthFrontier,
    topChildren, litGate19_normalizedWidth]

/-- Every representative layer of `dupSquareRepLayer19` has the same gate set
as the corresponding raw frontier of `dupSquareWitness19`. -/
theorem dupSquareWitness19_representativeLayers :
    ∀ level, level ≤ depth dupSquareWitness19 →
      RepresentativeFrontierLayer dupSquareWitness19 level
        (dupSquareRepLayer19 level) := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 := by
    rw [dupSquareWitness19_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl
  · refine ⟨fun G hG => ?_, fun G hG => ?_⟩
    · rw [dupSquareRepLayer19_zero_eq] at hG
      simpa [formulaDepthFrontier, depthFrontier] using hG
    · rw [dupSquareRepLayer19_zero_eq]
      simpa [formulaDepthFrontier, depthFrontier] using hG
  · refine ⟨fun G hG => ?_, fun G hG => ?_⟩
    · rw [dupSquareRepLayer19_one_eq] at hG
      simp at hG
      simp [formulaDepthFrontier, depthFrontier, topChildren,
        dupSquareWitness19, hG]
    · simp [formulaDepthFrontier, depthFrontier, topChildren,
        dupSquareWitness19] at hG
      rw [dupSquareRepLayer19_one_eq]
      simp [hG]
  · refine ⟨fun G hG => ?_, fun G hG => ?_⟩
    · rw [dupSquareRepLayer19_two_eq] at hG
      simp at hG
      simp [formulaDepthFrontier, depthFrontier, topChildren,
        dupSquareWitness19, dupSquareInner19, hG]
    · simp [formulaDepthFrontier, depthFrontier, topChildren,
        dupSquareWitness19, dupSquareInner19] at hG
      rw [dupSquareRepLayer19_two_eq]
      simp [hG]

/-- Every representative layer is a singleton: one gate per level replaces the
raw duplicate-carrying frontier lists of lengths `1`, `2`, `4`. -/
theorem dupSquareRepLayer19_length :
    ∀ level, (dupSquareRepLayer19 level).length = 1
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- Exact entry product at `rounds = 2`, count 1, width 1:
`2*(64*1)^2*(64*1*1) = 524288 = 2^19`. -/
theorem dupSquareWitness19_entryProduct_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 1) = 524288 := by decide

/-- Zero-hypothesis all-level representative instance at ambient `2^19`,
`rounds = 2`, parent kind `and`: the entry product is exactly `2^19` at EVERY
level, because every representative layer is the same singleton count.  The
final tree at each level is certified against the original parent-merged
frontier formula. -/
theorem dupSquareWitness19_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth dupSquareWitness19 →
      RepresentativeNormalizedViewClassDepthFinalTreeAt dupSquareWitness19
        (fun _ => 7) (normalizedFrontierWidthSchedule dupSquareWitness19)
        2 2 ParentKind.and level (dupSquareRepLayer19 level) := by
  refine allRepresentativeFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    dupSquareWitness19 (fun _ => 7) 2 2 ParentKind.and dupSquareRepLayer19
      dupSquareWitness19_nonemptyFanin (Nat.le_of_eq dupSquareWitness19_depth)
      (Nat.le_of_eq dupSquareWitness19_formulaSize)
      dupSquareWitness19_representativeLayers ?_ ?_
  · intro level _
    rw [dupSquareRepLayer19_length]
    decide
  · intro level hlevel
    have hcase : level = 0 ∨ level = 1 ∨ level = 2 := by
      rw [dupSquareWitness19_depth] at hlevel
      omega
    rcases hcase with rfl | rfl | rfl
    · rw [dupSquareRepLayer19_length,
        dupSquareWitness19_normalizedFrontierWidthSchedule_zero]
      decide
    · rw [dupSquareRepLayer19_length,
        dupSquareWitness19_normalizedFrontierWidthSchedule_one]
      decide
    · rw [dupSquareRepLayer19_length,
        dupSquareWitness19_normalizedFrontierWidthSchedule_two]
      decide

/-- Same-witness entry separation at ambient `2^19`: the S2166 raw-count
route's level-2 entry product at `rounds = 2` is `2^25`, which exceeds this
ambient, so that route's entry hypothesis fails here at level 2 at
`rounds = 2` while the representative route enters. -/
theorem dupSquareWitness19_rawCount_entry_fails_level2 :
    ¬ (2 * (64 * frontierLayerGateCount dupSquareWitness19 2) ^ 2 *
      (64 * frontierLayerGateCount dupSquareWitness19 2 *
        normalizedFrontierWidthSchedule dupSquareWitness19 2) ≤ 524288) := by
  rw [dupSquareWitness19_frontierGateCount_two,
    dupSquareWitness19_normalizedFrontierWidthSchedule_two]
  decide

/-- Bookkeeping comparison across different witnesses: this ambient `2^19`
against the S2166 package's ambient `2^22`. -/
theorem dupSquareWitness19_ambient_lt_nestedDupWitness22_ambient :
    524288 < 4194304 := by decide

/-! ## Depth-3 duplicated-cube witness at ambient `2^19` (S2168) -/

/-- The depth-3 duplicate cube obtained by conjoining two copies of
`dupSquareWitness19`. -/
def dupCubeWitness19 : BDFormula 524288 :=
  .and [dupSquareWitness19, dupSquareWitness19]

/-- Singleton representatives for all four levels of `dupCubeWitness19`. -/
def dupCubeRepLayer19 : Nat → List (BDFormula 524288)
  | 0 => [dupCubeWitness19]
  | 1 => [dupSquareWitness19]
  | 2 => [dupSquareInner19]
  | _ + 3 => [.lit { var := ⟨0, by decide⟩, sign := true }]

theorem dupCubeWitness19_nonemptyFanin :
    NonemptyFaninFormula dupCubeWitness19 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness19] at hG
  subst hG
  exact dupSquareWitness19_nonemptyFanin

private theorem dupCubeWitness19_syntacticDNF_eq :
    syntacticDNF dupCubeWitness19 =
      [[{ var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true },
        { var := ⟨0, by decide⟩, sign := true }]] := by
  simp [dupCubeWitness19, dupSquareWitness19, dupSquareInner19, syntacticDNF,
    syntacticAndDNF, andDNF, FormulaSyntacticDNF.literalDNF,
    FormulaSyntacticDNF.trueDNF]

theorem dupCubeWitness19_syntacticDNF_not_simple :
    ¬ SimpleDNF (syntacticDNF dupCubeWitness19) := by
  intro h
  have ht : ([{ var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true },
      { var := ⟨0, by decide⟩, sign := true }] : Term 524288) ∈
      syntacticDNF dupCubeWitness19 := by
    rw [dupCubeWitness19_syntacticDNF_eq]
    exact List.mem_cons_self _ _
  have hs := h _ ht
  simp [SimpleTerm] at hs

theorem dupCubeWitness19_formulaSize :
    formulaSize dupCubeWitness19 = 15 := by
  simp [dupCubeWitness19, formulaSize_and, dupSquareWitness19_formulaSize]

/-- The max-one count recurrence evaluates to eight on the duplicated cube. -/
theorem dupCubeWitness19_recurrenceCount :
    formulaRecurrenceCount dupCubeWitness19 = 8 := by
  simp [dupCubeWitness19, dupSquareWitness19, dupSquareInner19,
    formulaRecurrenceCount_and, formulaRecurrenceCount_lit]

/-- The count recurrence strictly improves on raw formula size for the witness. -/
theorem dupCubeWitness19_recurrenceCount_lt_formulaSize :
    formulaRecurrenceCount dupCubeWitness19 < formulaSize dupCubeWitness19 := by
  rw [dupCubeWitness19_recurrenceCount, dupCubeWitness19_formulaSize]
  decide

/-- Every raw frontier layer of the duplicated cube has at most eight gates. -/
theorem dupCubeWitness19_frontierGateCount_le_eight (level : Nat) :
    frontierLayerGateCount dupCubeWitness19 level ≤ 8 := by
  simpa [dupCubeWitness19_recurrenceCount] using
    frontierLayerGateCount_le_formulaRecurrenceCount dupCubeWitness19 level

theorem dupCubeWitness19_depth : depth dupCubeWitness19 = 3 := by
  simp [dupCubeWitness19, depth, dupSquareWitness19_depth]

theorem dupCubeWitness19_recurrenceWidth :
    formulaRecurrenceWidth dupCubeWitness19 = 8 := by
  simp [dupCubeWitness19, formulaRecurrenceWidth_and,
    dupSquareWitness19_recurrenceWidth]

theorem dupCubeWitness19_frontierGateCount_zero :
    frontierLayerGateCount dupCubeWitness19 0 = 1 :=
  frontierLayerGateCount_zero dupCubeWitness19

theorem dupCubeWitness19_frontierGateCount_one :
    frontierLayerGateCount dupCubeWitness19 1 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem dupCubeWitness19_frontierGateCount_two :
    frontierLayerGateCount dupCubeWitness19 2 = 4 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem dupCubeWitness19_frontierGateCount_three :
    frontierLayerGateCount dupCubeWitness19 3 = 8 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

theorem dupCubeWitness19_normalizedWidth :
    widthDNF (normalizedDNFView dupCubeWitness19).D = 1 := by
  rw [normalizedDNFView_D, dupCubeWitness19_syntacticDNF_eq]
  rfl

theorem dupCubeWitness19_normalizedFrontierWidthSchedule_zero :
    normalizedFrontierWidthSchedule dupCubeWitness19 0 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    formulaDepthFrontier, depthFrontier, dupCubeWitness19_normalizedWidth]

theorem dupCubeWitness19_normalizedFrontierWidthSchedule_one :
    normalizedFrontierWidthSchedule dupCubeWitness19 1 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    dupCubeWitness19, formulaDepthFrontier, depthFrontier, topChildren,
    dupSquareWitness19_normalizedWidth]

theorem dupCubeWitness19_normalizedFrontierWidthSchedule_two :
    normalizedFrontierWidthSchedule dupCubeWitness19 2 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    dupCubeWitness19, dupSquareWitness19, formulaDepthFrontier, depthFrontier,
    topChildren, dupSquareInner19_normalizedWidth]

theorem dupCubeWitness19_normalizedFrontierWidthSchedule_three :
    normalizedFrontierWidthSchedule dupCubeWitness19 3 = 1 := by
  simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
    dupCubeWitness19, dupSquareWitness19, dupSquareInner19,
    formulaDepthFrontier, depthFrontier, topChildren, litGate19_normalizedWidth]

theorem dupCubeWitness19_representativeLayers :
    ∀ level, level ≤ depth dupCubeWitness19 →
      RepresentativeFrontierLayer dupCubeWitness19 level
        (dupCubeRepLayer19 level) := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness19_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    constructor <;> intro G hG <;>
    simp [RepresentativeFrontierLayer, dupCubeRepLayer19, formulaDepthFrontier,
      depthFrontier, topChildren, dupCubeWitness19, dupSquareWitness19,
      dupSquareInner19] at hG ⊢ <;> assumption

theorem dupCubeRepLayer19_length :
    ∀ level, (dupCubeRepLayer19 level).length = 1
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

theorem dupCubeWitness19_entryProduct_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 1) = 524288 := by decide

theorem dupCubeWitness19_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth dupCubeWitness19 →
      RepresentativeNormalizedViewClassDepthFinalTreeAt dupCubeWitness19
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness19)
        3 2 ParentKind.and level (dupCubeRepLayer19 level) := by
  refine allRepresentativeFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    dupCubeWitness19 (fun _ => 15) 3 2 ParentKind.and dupCubeRepLayer19
      dupCubeWitness19_nonemptyFanin (Nat.le_of_eq dupCubeWitness19_depth)
      (Nat.le_of_eq dupCubeWitness19_formulaSize)
      dupCubeWitness19_representativeLayers ?_ ?_
  · intro level _
    rw [dupCubeRepLayer19_length]
    decide
  · intro level hlevel
    have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
      rw [dupCubeWitness19_depth] at hlevel
      omega
    rcases hcase with rfl | rfl | rfl | rfl
    · rw [dupCubeRepLayer19_length,
        dupCubeWitness19_normalizedFrontierWidthSchedule_zero]
      decide
    · rw [dupCubeRepLayer19_length,
        dupCubeWitness19_normalizedFrontierWidthSchedule_one]
      decide
    · rw [dupCubeRepLayer19_length,
        dupCubeWitness19_normalizedFrontierWidthSchedule_two]
      decide
    · rw [dupCubeRepLayer19_length,
        dupCubeWitness19_normalizedFrontierWidthSchedule_three]
      decide

theorem dupCubeWitness19_rawCount_entry_fails_level3 :
    ¬ (2 * (64 * frontierLayerGateCount dupCubeWitness19 3) ^ 2 *
      (64 * frontierLayerGateCount dupCubeWitness19 3 *
        normalizedFrontierWidthSchedule dupCubeWitness19 3) ≤ 524288) := by
  rw [dupCubeWitness19_frontierGateCount_three,
    dupCubeWitness19_normalizedFrontierWidthSchedule_three]
  decide

theorem dupCubeWitness19_rawCount_entryProduct_level3_eq :
    2 * (64 * 8) ^ 2 * (64 * 8 * 1) = 268435456 := by decide

/-! ## Synthesized duplicate-free representative layers (S2169)

Decidable syntactic equality for raw formulas makes `List.dedup` available on
raw depth frontiers.  `dedupRepresentativeFrontier` is then AUTOMATICALLY a
representative layer: its membership equations, duplicate-freeness, and count
bounds are proved once for every formula and level, so the consumers below
drop the manually supplied layer lists (`gsAll`), membership proofs
(`hrepAll`), and count obligations (`hcountAll`) of the S2167 route. -/

mutual

/-- Structural Boolean equality of raw formulas. -/
def formulaBEq {n : Nat} : BDFormula n → BDFormula n → Bool
  | .tru, .tru => true
  | .fls, .fls => true
  | .lit a, .lit b => decide (a = b)
  | .and xs, .and ys => formulaListBEq xs ys
  | .or xs, .or ys => formulaListBEq xs ys
  | _, _ => false
termination_by F _ => sizeOf F
decreasing_by all_goals (simp_wf; try omega)

/-- Structural Boolean equality of raw-formula lists. -/
def formulaListBEq {n : Nat} : List (BDFormula n) → List (BDFormula n) → Bool
  | [], [] => true
  | x :: xs, y :: ys => formulaBEq x y && formulaListBEq xs ys
  | [], _ :: _ => false
  | _ :: _, [] => false
termination_by xs _ => sizeOf xs
decreasing_by all_goals (simp_wf; try omega)

end

private theorem formulaListBEq_eq_true_iff {n : Nat} :
    ∀ (xs ys : List (BDFormula n)),
      (∀ f ∈ xs, ∀ G, formulaBEq f G = true ↔ f = G) →
      (formulaListBEq xs ys = true ↔ xs = ys)
  | [], [], _ => by simp [formulaListBEq]
  | [], _ :: _, _ => by simp [formulaListBEq]
  | _ :: _, [], _ => by simp [formulaListBEq]
  | x :: xs, y :: ys, h => by
      have hx := h x (List.mem_cons_self x xs) y
      have hxs := formulaListBEq_eq_true_iff xs ys
        (fun f hf G => h f (List.mem_cons_of_mem x hf) G)
      simp only [formulaListBEq, Bool.and_eq_true, List.cons.injEq, hx, hxs]

/-- Structural Boolean equality decides propositional equality. -/
theorem formulaBEq_eq_true_iff {n : Nat} (F : BDFormula n) :
    ∀ G, formulaBEq F G = true ↔ F = G := by
  induction F using BDFormula.recAux with
  | htru => intro G; cases G <;> simp [formulaBEq]
  | hfls => intro G; cases G <;> simp [formulaBEq]
  | hlit a => intro G; cases G <;> simp [formulaBEq]
  | hand xs ih =>
      intro G
      cases G with
      | and ys => simp only [formulaBEq, BDFormula.and.injEq,
          formulaListBEq_eq_true_iff xs ys ih]
      | tru => simp [formulaBEq]
      | fls => simp [formulaBEq]
      | lit b => simp [formulaBEq]
      | or ys => simp [formulaBEq]
  | hor xs ih =>
      intro G
      cases G with
      | or ys => simp only [formulaBEq, BDFormula.or.injEq,
          formulaListBEq_eq_true_iff xs ys ih]
      | tru => simp [formulaBEq]
      | fls => simp [formulaBEq]
      | lit b => simp [formulaBEq]
      | and ys => simp [formulaBEq]

/-- Raw formulas have decidable syntactic equality (module-local). -/
local instance instDecidableEqBDFormula {n : Nat} : DecidableEq (BDFormula n) :=
  fun F G =>
    if h : formulaBEq F G = true then
      isTrue ((formulaBEq_eq_true_iff F G).mp h)
    else
      isFalse fun hFG => h ((formulaBEq_eq_true_iff F G).mpr hFG)

/-- The synthesized representative layer: the raw depth frontier with
syntactic duplicates removed. -/
def dedupRepresentativeFrontier {n : Nat} (F : BDFormula n) (level : Nat) :
    List (BDFormula n) :=
  (formulaDepthFrontier level F).dedup

/-- The synthesized layer is a representative layer of its own frontier with
zero supplied hypotheses. -/
theorem dedupRepresentativeFrontier_representative {n : Nat} (F : BDFormula n)
    (level : Nat) :
    RepresentativeFrontierLayer F level (dedupRepresentativeFrontier F level) :=
  ⟨fun _ hG => List.mem_dedup.mp hG, fun _ hG => List.mem_dedup.mpr hG⟩

/-- The synthesized layer is duplicate-free. -/
theorem dedupRepresentativeFrontier_nodup {n : Nat} (F : BDFormula n)
    (level : Nat) : (dedupRepresentativeFrontier F level).Nodup :=
  List.nodup_dedup (formulaDepthFrontier level F)

/-- The synthesized layer never exceeds the raw frontier gate count. -/
theorem dedupRepresentativeFrontier_length_le_frontierGateCount {n : Nat}
    (F : BDFormula n) (level : Nat) :
    (dedupRepresentativeFrontier F level).length ≤
      frontierLayerGateCount F level := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  exact (List.dedup_sublist (formulaDepthFrontier level F)).length_le

/-- The synthesized layer never exceeds the formula size, so the S2167 count
obligation is derivable from the class size hypothesis alone. -/
theorem dedupRepresentativeFrontier_length_le_formulaSize {n : Nat}
    (F : BDFormula n) (level : Nat) :
    (dedupRepresentativeFrontier F level).length ≤ formulaSize F :=
  Nat.le_trans
    (dedupRepresentativeFrontier_length_le_frontierGateCount F level)
    (frontierLayerGateCount_le_formulaSize F level)

/-- In-depth synthesized layers of nonempty-fanin formulas are nonempty. -/
theorem dedupRepresentativeFrontier_length_pos {n : Nat} {F : BDFormula n}
    {level : Nat} (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F) :
    1 ≤ (dedupRepresentativeFrontier F level).length :=
  representative_length_pos hNE hk
    (dedupRepresentativeFrontier_representative F level)

/-! ## Consumers over synthesized layers -/

/-- All-level supplied-width tight-entry consumer over synthesized layers:
the manually supplied per-level layer lists, membership proofs, and count
obligations of the S2167 consumer are all synthesized from the raw formula.
Only the class data and the per-level width and ambient obligations remain. -/
theorem allDedupFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g ∈ (representativeMinimalLayer
        (dedupRepresentativeFrontier F level) parent).gates,
        widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (64 * (dedupRepresentativeFrontier F level).length * W level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAt F S W d rounds parent
        level (dedupRepresentativeFrontier F level) :=
  allRepresentativeFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S W d rounds parent (dedupRepresentativeFrontier F) hDepth hSize hNE
    (fun level _ => dedupRepresentativeFrontier_representative F level)
    (fun level _ => Nat.le_trans
      (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize)
    hwAll hwPos hnAll

/-- Single-level class-derived consumer over the synthesized layer using the
actual normalized-frontier DNF width schedule: the only witness-specific
obligation is the ambient entry product. -/
theorem dedupFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d) (hk : level ≤ depth F)
    (hn : 2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (64 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAt F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  representativeFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth
    F S d level rounds parent (dedupRepresentativeFrontier F level)
    (dedupRepresentativeFrontier_representative F level) hNE hDepth hSize hk
    (Nat.le_trans (dedupRepresentativeFrontier_length_le_formulaSize F level)
      hSize)
    hn

/-- All-level class-derived consumer over synthesized layers using the actual
normalized-frontier DNF width schedule: for every nonempty-fanin formula in
class `(d, S)`, the only remaining per-level obligation is the ambient entry
product over the synthesized count. -/
theorem allDedupFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hNE : NonemptyFaninFormula F) (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (64 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAt F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) := by
  intro level hk
  exact dedupFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk (hnAll level hk)

/-- Coefficient-32 all-level supplied-width consumer over synthesized layers. -/
theorem allDedupFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F)
    (hwAll : ∀ level, level ≤ depth F → ∀ g ∈ (representativeMinimalLayer
      (dedupRepresentativeFrontier F level) parent).gates,
      widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (32 * (dedupRepresentativeFrontier F level).length * W level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S W d
        rounds parent level (dedupRepresentativeFrontier F level) :=
  allRepresentativeFrontiers_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    F S W d rounds parent (dedupRepresentativeFrontier F) hDepth hSize hNE
    (fun level _ => dedupRepresentativeFrontier_representative F level)
    (fun level _ => Nat.le_trans
      (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize)
    hwAll hwPos hnAll

/-- Coefficient-32 single-level normalized-width synthesized consumer. -/
theorem dedupFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (32 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  representativeFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    F S d level rounds parent (dedupRepresentativeFrontier F level)
    (dedupRepresentativeFrontier_representative F level) hNE hDepth hSize hk
    (Nat.le_trans (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize) hn

/-- Coefficient-32 all-level normalized-width synthesized consumer. -/
theorem allDedupFrontiers_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (32 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) := by
  intro level hk
  exact dedupFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk (hnAll level hk)

/-! Public coefficient-32 naming aliases.  These preserve the S2170 payload
and hypotheses while spelling the changed entry coefficient explicitly. -/

theorem representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntry32
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hNE : NonemptyFaninFormula F) (hk : level ≤ depth F)
    (hcount : gs.length ≤ S d)
    (hw : ∀ g ∈ (representativeMinimalLayer gs parent).gates,
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level)
    (hn : 2 * (64 * gs.length) ^ rounds * (32 * gs.length * W level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S W d rounds parent
      level gs :=
  representativeFrontier_geometricCollapseWithSuppliedWidth_finalTree_tightEntryStar
    F S W d level rounds parent gs hrep hDepth hSize hNE hk hcount hw hw1 hn

theorem representativeFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth32
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (gs : List (BDFormula n))
    (hrep : RepresentativeFrontierLayer F level gs) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F) (hcount : gs.length ≤ S d)
    (hn : 2 * (64 * gs.length) ^ rounds *
      (32 * gs.length * normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
      (normalizedFrontierWidthSchedule F) d rounds parent level gs :=
  representativeFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    F S d level rounds parent gs hrep hNE hDepth hSize hk hcount hn

theorem allDedupFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth32
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (32 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) :=
  allDedupFrontiers_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    F S d rounds parent hNE hDepth hSize hnAll

theorem dedupFrontier_geometricCollapse_finalTree_tightEntry_normalizedWidth32
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (64 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (32 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  dedupFrontier_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk hn

/-- Uniform-32 single-level normalized-width consumer over a synthesized layer. -/
theorem dedupFrontier_geometricCollapse_finalTree_uniform32_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (32 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (32 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  representativeFrontier_geometricCollapse_finalTree_uniform32_normalizedWidth
    F S d level rounds parent (dedupRepresentativeFrontier F level)
    (dedupRepresentativeFrontier_representative F level) hNE hDepth hSize hk
    (Nat.le_trans (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize) hn

/-- Uniform-32 all-level normalized-width consumer over synthesized layers. -/
theorem allDedupFrontiers_geometricCollapse_finalTree_uniform32_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (32 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (32 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) := by
  intro level hk
  exact dedupFrontier_geometricCollapse_finalTree_uniform32_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk (hnAll level hk)

/-- Uniform-17 single-level normalized-width consumer over a synthesized layer. -/
theorem dedupFrontier_geometricCollapse_finalTree_uniform17_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (17 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (17 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform17 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  representativeFrontier_geometricCollapse_finalTree_uniform17_normalizedWidth
    F S d level rounds parent (dedupRepresentativeFrontier F level)
    (dedupRepresentativeFrontier_representative F level) hNE hDepth hSize hk
    (Nat.le_trans (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize) hn

/-- Uniform-17 all-level normalized-width consumer over synthesized layers. -/
theorem allDedupFrontiers_geometricCollapse_finalTree_uniform17_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (17 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (17 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform17 F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) := by
  intro level hk
  exact dedupFrontier_geometricCollapse_finalTree_uniform17_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk (hnAll level hk)

/-- Uniform-16 single-level normalized-width consumer over a synthesized layer. -/
theorem dedupFrontier_geometricCollapse_finalTree_uniform16_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (16 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (16 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform16 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  representativeFrontier_geometricCollapse_finalTree_uniform16_normalizedWidth
    F S d level rounds parent (dedupRepresentativeFrontier F level)
    (dedupRepresentativeFrontier_representative F level) hNE hDepth hSize hk
    (Nat.le_trans (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize) hn

/-- Uniform-16 all-level normalized-width consumer over synthesized layers. -/
theorem allDedupFrontiers_geometricCollapse_finalTree_uniform16_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (16 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (16 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform16 F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) := by
  intro level hk
  exact dedupFrontier_geometricCollapse_finalTree_uniform16_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk (hnAll level hk)

/-- Uniform-9 single-level normalized-width consumer over a synthesized layer. -/
theorem dedupFrontier_geometricCollapse_finalTree_uniform9_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d level rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (9 * (dedupRepresentativeFrontier F level).length) ^ rounds *
      (9 * (dedupRepresentativeFrontier F level).length *
        normalizedFrontierWidthSchedule F level) ≤ n) :
    RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 F S
      (normalizedFrontierWidthSchedule F) d rounds parent level
      (dedupRepresentativeFrontier F level) :=
  representativeFrontier_geometricCollapse_finalTree_uniform9_normalizedWidth
    F S d level rounds parent (dedupRepresentativeFrontier F level)
    (dedupRepresentativeFrontier_representative F level) hNE hDepth hSize hk
    (Nat.le_trans (dedupRepresentativeFrontier_length_le_formulaSize F level) hSize) hn

/-- Uniform-9 all-level normalized-width consumer over synthesized layers. -/
theorem allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    {n : Nat} (F : BDFormula n) (S : Nat → Nat) (d rounds : Nat)
    (parent : ParentKind) (hNE : NonemptyFaninFormula F)
    (hDepth : depth F ≤ d) (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (9 * (dedupRepresentativeFrontier F level).length) ^ rounds *
        (9 * (dedupRepresentativeFrontier F level).length *
          normalizedFrontierWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 F S
        (normalizedFrontierWidthSchedule F) d rounds parent level
        (dedupRepresentativeFrontier F level) := by
  intro level hk
  exact dedupFrontier_geometricCollapse_finalTree_uniform9_normalizedWidth
    F S d level rounds parent hNE hDepth hSize hk (hnAll level hk)

/-! ## The dedup route on the depth-3 cube witness (S2169) -/

private theorem dedup_replicate_succ {α : Type _} [DecidableEq α] (a : α) :
    ∀ k, (List.replicate (k + 1) a).dedup = [a]
  | 0 => by
      rw [List.replicate_succ, List.replicate_zero,
        List.dedup_cons_of_not_mem (List.not_mem_nil a), List.dedup_nil]
  | k + 1 => by
      rw [List.replicate_succ, List.dedup_cons_of_mem (by simp),
        dedup_replicate_succ a k]

/-- The synthesized level-0 layer coincides with the hand-supplied S2168
representative layer. -/
theorem dupCubeWitness19_dedupFrontier_zero :
    dedupRepresentativeFrontier dupCubeWitness19 0 = dupCubeRepLayer19 0 :=
  dedup_replicate_succ dupCubeWitness19 0

/-- The synthesized level-1 layer coincides with the hand-supplied S2168
representative layer: the two duplicate square copies collapse to one. -/
theorem dupCubeWitness19_dedupFrontier_one :
    dedupRepresentativeFrontier dupCubeWitness19 1 = dupCubeRepLayer19 1 :=
  dedup_replicate_succ dupSquareWitness19 1

/-- The synthesized level-2 layer coincides with the hand-supplied S2168
representative layer: the four duplicate inner copies collapse to one. -/
theorem dupCubeWitness19_dedupFrontier_two :
    dedupRepresentativeFrontier dupCubeWitness19 2 = dupCubeRepLayer19 2 :=
  dedup_replicate_succ dupSquareInner19 3

/-- The synthesized level-3 layer coincides with the hand-supplied S2168
representative layer: the eight duplicate literal copies collapse to one. -/
theorem dupCubeWitness19_dedupFrontier_three :
    dedupRepresentativeFrontier dupCubeWitness19 3 = dupCubeRepLayer19 3 :=
  dedup_replicate_succ
    (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7

/-- Synthesized level-0 count. -/
theorem dupCubeWitness19_dedupFrontier_length_zero :
    (dedupRepresentativeFrontier dupCubeWitness19 0).length = 1 :=
  (congrArg List.length dupCubeWitness19_dedupFrontier_zero).trans
    (dupCubeRepLayer19_length 0)

/-- Synthesized level-1 count. -/
theorem dupCubeWitness19_dedupFrontier_length_one :
    (dedupRepresentativeFrontier dupCubeWitness19 1).length = 1 :=
  (congrArg List.length dupCubeWitness19_dedupFrontier_one).trans
    (dupCubeRepLayer19_length 1)

/-- Synthesized level-2 count. -/
theorem dupCubeWitness19_dedupFrontier_length_two :
    (dedupRepresentativeFrontier dupCubeWitness19 2).length = 1 :=
  (congrArg List.length dupCubeWitness19_dedupFrontier_two).trans
    (dupCubeRepLayer19_length 2)

/-- Synthesized level-3 count. -/
theorem dupCubeWitness19_dedupFrontier_length_three :
    (dedupRepresentativeFrontier dupCubeWitness19 3).length = 1 :=
  (congrArg List.length dupCubeWitness19_dedupFrontier_three).trans
    (dupCubeRepLayer19_length 3)

/-- Pinned strict synthesized-versus-raw separation at the deepest level: the
synthesized count `1` is strictly below the raw count `8`. -/
theorem dupCubeWitness19_dedup_length_lt_rawCount_level3 :
    (dedupRepresentativeFrontier dupCubeWitness19 3).length <
      frontierLayerGateCount dupCubeWitness19 3 := by
  rw [dupCubeWitness19_dedupFrontier_length_three,
    dupCubeWitness19_frontierGateCount_three]
  decide

/-- Zero-hypothesis all-level instance at ambient `2^19`, `rounds = 2`, parent
kind `and`, through the SYNTHESIZED layers: no representative layer list,
membership proof, or count obligation is supplied anywhere; each level's
ambient entry product is exactly `2^19` because every synthesized layer has
count `1`. -/
theorem dupCubeWitness19_dedup_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth dupCubeWitness19 →
      RepresentativeNormalizedViewClassDepthFinalTreeAt dupCubeWitness19
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness19)
        3 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness19 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_tightEntry_normalizedWidth
    dupCubeWitness19 (fun _ => 15) 3 2 ParentKind.and
    dupCubeWitness19_nonemptyFanin (Nat.le_of_eq dupCubeWitness19_depth)
    (Nat.le_of_eq dupCubeWitness19_formulaSize) ?_
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness19_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · rw [dupCubeWitness19_dedupFrontier_length_zero,
      dupCubeWitness19_normalizedFrontierWidthSchedule_zero]
    decide
  · rw [dupCubeWitness19_dedupFrontier_length_one,
      dupCubeWitness19_normalizedFrontierWidthSchedule_one]
    decide
  · rw [dupCubeWitness19_dedupFrontier_length_two,
      dupCubeWitness19_normalizedFrontierWidthSchedule_two]
    decide
  · rw [dupCubeWitness19_dedupFrontier_length_three,
      dupCubeWitness19_normalizedFrontierWidthSchedule_three]
    decide

/-! ## Coefficient-32 entry witness at ambient `2^18` (S2170) -/

private def dupSquareInner18 : BDFormula 262144 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness18 : BDFormula 262144 :=
  .and [dupSquareInner18, dupSquareInner18]

/-- The depth-3 duplicated cube at ambient `2^18`. -/
def dupCubeWitness18 : BDFormula 262144 :=
  .and [dupSquareWitness18, dupSquareWitness18]

private theorem dupSquareInner18_nonempty : NonemptyFaninFormula dupSquareInner18 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner18] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness18_nonempty : NonemptyFaninFormula dupSquareWitness18 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness18] at hG
  subst hG
  exact dupSquareInner18_nonempty

private theorem dupCubeWitness18_nonempty : NonemptyFaninFormula dupCubeWitness18 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness18] at hG
  subst hG
  exact dupSquareWitness18_nonempty

private theorem dupCubeWitness18_size : formulaSize dupCubeWitness18 = 15 := by
  simp [dupCubeWitness18, dupSquareWitness18, dupSquareInner18, formulaSize_and,
    formulaSize_lit]

private theorem dupCubeWitness18_depth : depth dupCubeWitness18 = 3 := by
  simp [dupCubeWitness18, dupSquareWitness18, dupSquareInner18, depth]

private theorem dupCubeWitness18_widthSchedule :
    ∀ level, level ≤ depth dupCubeWitness18 →
      normalizedFrontierWidthSchedule dupCubeWitness18 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness18_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness18,
      dupSquareWitness18, dupSquareInner18] <;> rfl

private theorem dupCubeWitness18_dedup_length :
    ∀ level, level ≤ depth dupCubeWitness18 →
      (dedupRepresentativeFrontier dupCubeWitness18 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness18_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness18 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness18 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner18 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

/-- Exact tight-entry product at count and width one. -/
theorem dupCubeWitness18_tightEntryProduct_eq :
    2 * (64 * 1) ^ 2 * (32 * 1 * 1) = 262144 := by decide

/-- The former coefficient-`64` entry product fails at ambient `2^18`. -/
theorem dupCubeWitness18_coarseEntryProduct_fails :
    ¬ (2 * (64 * 1) ^ 2 * (64 * 1 * 1) ≤ 262144) := by decide

/-- Exact coefficient-32 schedule-entry arithmetic at ambient `2^18`. -/
theorem dupCubeWitness19_tightEntry_product_eq :
    2 * (64 * 1) ^ 2 * (32 * 1 * 1) = 262144 :=
  dupCubeWitness18_tightEntryProduct_eq

/-- The former coefficient-64 schedule entry does not fit ambient `2^18`. -/
theorem dupCubeWitness19_oldEntry_fails_at_2pow18 :
    ¬ (2 * (64 * 1) ^ 2 * (64 * 1 * 1) ≤ 262144) :=
  dupCubeWitness18_coarseEntryProduct_fails

/-- Requested S2170 all-level pin: despite the retained historical `19` in
the declaration name, this theorem is over `dupCubeWitness18` at ambient
`2^18`, with synthesized singleton layers and two rounds. -/
theorem dupCubeWitness19_dedup_finalTree_allLevels_rounds2_ambient18 :
    ∀ level, level ≤ depth dupCubeWitness18 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtTightEntryStar dupCubeWitness18
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness18)
        3 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness18 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_tightEntryStar_normalizedWidth
    dupCubeWitness18 (fun _ => 15) 3 2 ParentKind.and dupCubeWitness18_nonempty
      (Nat.le_of_eq dupCubeWitness18_depth) (Nat.le_of_eq dupCubeWitness18_size) ?_
  intro level hlevel
  rw [dupCubeWitness18_dedup_length level hlevel,
    dupCubeWitness18_widthSchedule level hlevel]
  decide

/-! ## Uniform-32 witness at ambient `2^16` (S2171) -/

private def dupSquareInner16 : BDFormula 65536 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness16 : BDFormula 65536 :=
  .and [dupSquareInner16, dupSquareInner16]

/-- The depth-3 duplicated cube at ambient `2^16`. -/
def dupCubeWitness16 : BDFormula 65536 :=
  .and [dupSquareWitness16, dupSquareWitness16]

private theorem dupSquareInner16_nonempty : NonemptyFaninFormula dupSquareInner16 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner16] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness16_nonempty : NonemptyFaninFormula dupSquareWitness16 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness16] at hG
  subst hG
  exact dupSquareInner16_nonempty

private theorem dupCubeWitness16_nonempty : NonemptyFaninFormula dupCubeWitness16 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness16] at hG
  subst hG
  exact dupSquareWitness16_nonempty

private theorem dupCubeWitness16_size : formulaSize dupCubeWitness16 = 15 := by
  simp [dupCubeWitness16, dupSquareWitness16, dupSquareInner16, formulaSize_and,
    formulaSize_lit]

private theorem dupCubeWitness16_depth : depth dupCubeWitness16 = 3 := by
  simp [dupCubeWitness16, dupSquareWitness16, dupSquareInner16, depth]

private theorem dupCubeWitness16_widthSchedule :
    ∀ level, level ≤ depth dupCubeWitness16 →
      normalizedFrontierWidthSchedule dupCubeWitness16 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness16_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness16,
      dupSquareWitness16, dupSquareInner16] <;> rfl

private theorem dupCubeWitness16_dedup_length :
    ∀ level, level ≤ depth dupCubeWitness16 →
      (dedupRepresentativeFrontier dupCubeWitness16 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness16_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness16 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness16 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner16 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

/-- Exact two-round uniform-32 product at count and width one. -/
theorem dupCubeWitness16_uniform32_product_eq :
    2 * (32 * 1) ^ 2 * (32 * 1 * 1) = 65536 := by decide

/-- The S2170 schedule, whose later stages divide by `64`, does not fit the
same ambient size. -/
theorem dupCubeWitness16_s2170_product_fails :
    ¬ (2 * (64 * 1) ^ 2 * (32 * 1 * 1) ≤ 65536) := by decide

/-- All synthesized representative levels of the finite witness carry the
uniform-32 two-round final-tree payload. -/
theorem dupCubeWitness16_dedup_finalTree_allLevels_rounds2_uniform32 :
    ∀ level, level ≤ depth dupCubeWitness16 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 dupCubeWitness16
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness16)
        3 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness16 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform32_normalizedWidth
    dupCubeWitness16 (fun _ => 15) 3 2 ParentKind.and dupCubeWitness16_nonempty
      (Nat.le_of_eq dupCubeWitness16_depth) (Nat.le_of_eq dupCubeWitness16_size)
      ?_
  intro level hlevel
  rw [dupCubeWitness16_dedup_length level hlevel,
    dupCubeWitness16_widthSchedule level hlevel]
  decide

/-! ## Uniform-32 witnesses at ambients `2^21` and `2^26` (S2172) -/

private def dupSquareInner21 : BDFormula 2097152 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness21 : BDFormula 2097152 :=
  .and [dupSquareInner21, dupSquareInner21]

/-- The depth-3 duplicated cube at ambient `2^21`. -/
def dupCubeWitness21 : BDFormula 2097152 :=
  .and [dupSquareWitness21, dupSquareWitness21]

private theorem dupSquareInner21_nonempty : NonemptyFaninFormula dupSquareInner21 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner21] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness21_nonempty : NonemptyFaninFormula dupSquareWitness21 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness21] at hG
  subst hG
  exact dupSquareInner21_nonempty

private theorem dupCubeWitness21_nonempty : NonemptyFaninFormula dupCubeWitness21 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness21] at hG
  subst hG
  exact dupSquareWitness21_nonempty

private theorem dupCubeWitness21_size : formulaSize dupCubeWitness21 = 15 := by
  simp [dupCubeWitness21, dupSquareWitness21, dupSquareInner21, formulaSize_and,
    formulaSize_lit]

private theorem dupCubeWitness21_depth : depth dupCubeWitness21 = 3 := by
  simp [dupCubeWitness21, dupSquareWitness21, dupSquareInner21, depth]

private theorem dupCubeWitness21_widthSchedule :
    ∀ level, level ≤ depth dupCubeWitness21 →
      normalizedFrontierWidthSchedule dupCubeWitness21 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness21_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness21,
      dupSquareWitness21, dupSquareInner21] <;> rfl

private theorem dupCubeWitness21_dedup_length :
    ∀ level, level ≤ depth dupCubeWitness21 →
      (dedupRepresentativeFrontier dupCubeWitness21 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness21_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness21 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness21 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner21 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

/-- Exact three-round uniform-32 product at count and width one. -/
theorem dupCubeWitness21_uniform32_rounds3_product_eq :
    2 * (32 * 1) ^ 3 * (32 * 1 * 1) = 2097152 := by decide

/-- The three-round uniform-32 product does not fit ambient `2^16`. -/
theorem dupCubeWitness21_rounds3_fails_at_s2171_ambient :
    ¬ (2 * (32 * 1) ^ 3 * (32 * 1 * 1) ≤ 65536) := by decide

/-- All synthesized representative levels of the finite witness carry the
uniform-32 three-round final-tree payload. -/
theorem dupCubeWitness21_dedup_finalTree_allLevels_rounds3_uniform32 :
    ∀ level, level ≤ depth dupCubeWitness21 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 dupCubeWitness21
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness21)
        3 3 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness21 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform32_normalizedWidth
    dupCubeWitness21 (fun _ => 15) 3 3 ParentKind.and dupCubeWitness21_nonempty
      (Nat.le_of_eq dupCubeWitness21_depth) (Nat.le_of_eq dupCubeWitness21_size)
      ?_
  intro level hlevel
  rw [dupCubeWitness21_dedup_length level hlevel,
    dupCubeWitness21_widthSchedule level hlevel]
  decide

private def dupSquareInner26 : BDFormula 67108864 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness26 : BDFormula 67108864 :=
  .and [dupSquareInner26, dupSquareInner26]

/-- The depth-3 duplicated cube at ambient `2^26`. -/
def dupCubeWitness26 : BDFormula 67108864 :=
  .and [dupSquareWitness26, dupSquareWitness26]

private theorem dupSquareInner26_nonempty : NonemptyFaninFormula dupSquareInner26 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner26] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness26_nonempty : NonemptyFaninFormula dupSquareWitness26 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness26] at hG
  subst hG
  exact dupSquareInner26_nonempty

private theorem dupCubeWitness26_nonempty : NonemptyFaninFormula dupCubeWitness26 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness26] at hG
  subst hG
  exact dupSquareWitness26_nonempty

private theorem dupCubeWitness26_size : formulaSize dupCubeWitness26 = 15 := by
  simp [dupCubeWitness26, dupSquareWitness26, dupSquareInner26, formulaSize_and,
    formulaSize_lit]

private theorem dupCubeWitness26_depth : depth dupCubeWitness26 = 3 := by
  simp [dupCubeWitness26, dupSquareWitness26, dupSquareInner26, depth]

private theorem dupCubeWitness26_widthSchedule :
    ∀ level, level ≤ depth dupCubeWitness26 →
      normalizedFrontierWidthSchedule dupCubeWitness26 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness26_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness26,
      dupSquareWitness26, dupSquareInner26] <;> rfl

private theorem dupCubeWitness26_dedup_length :
    ∀ level, level ≤ depth dupCubeWitness26 →
      (dedupRepresentativeFrontier dupCubeWitness26 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness26_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness26 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness26 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner26 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

/-- Exact four-round uniform-32 product at count and width one. -/
theorem dupCubeWitness26_uniform32_product_eq :
    2 * (32 * 1) ^ 4 * (32 * 1 * 1) = 67108864 := by decide

/-- All synthesized representative levels of the finite witness carry the
uniform-32 four-round final-tree payload. -/
theorem dupCubeWitness26_dedup_finalTree_allLevels_rounds4_uniform32 :
    ∀ level, level ≤ depth dupCubeWitness26 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform32 dupCubeWitness26
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness26)
        3 4 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness26 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform32_normalizedWidth
    dupCubeWitness26 (fun _ => 15) 3 4 ParentKind.and dupCubeWitness26_nonempty
      (Nat.le_of_eq dupCubeWitness26_depth) (Nat.le_of_eq dupCubeWitness26_size)
      ?_
  intro level hlevel
  rw [dupCubeWitness26_dedup_length level hlevel,
    dupCubeWitness26_widthSchedule level hlevel]
  decide

/-! ## Coefficient-17 finite packaging witness (S2175 Gate B Route C1)

This cube/dedup witness is NOT switching non-vacuity evidence.  It pins only
bounded schedule arithmetic and representative-layer packaging. -/

private def dupSquareInner14 : BDFormula 9826 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness14 : BDFormula 9826 :=
  .and [dupSquareInner14, dupSquareInner14]

/-- The duplicated depth-3 cube at exact ambient `9826`. -/
def dupCubeWitness14 : BDFormula 9826 :=
  .and [dupSquareWitness14, dupSquareWitness14]

private theorem dupSquareInner14_nonempty : NonemptyFaninFormula dupSquareInner14 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner14] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness14_nonempty : NonemptyFaninFormula dupSquareWitness14 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness14] at hG
  subst hG
  exact dupSquareInner14_nonempty

theorem dupCubeWitness14_nonemptyFanin : NonemptyFaninFormula dupCubeWitness14 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness14] at hG
  subst hG
  exact dupSquareWitness14_nonempty

theorem dupCubeWitness14_formulaSize : formulaSize dupCubeWitness14 = 15 := by
  simp [dupCubeWitness14, dupSquareWitness14, dupSquareInner14, formulaSize_and,
    formulaSize_lit]

theorem dupCubeWitness14_depth : depth dupCubeWitness14 = 3 := by
  simp [dupCubeWitness14, dupSquareWitness14, dupSquareInner14, depth]

theorem dupCubeWitness14_normalizedFrontierWidthSchedule :
    ∀ level, level ≤ depth dupCubeWitness14 →
      normalizedFrontierWidthSchedule dupCubeWitness14 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness14_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness14,
      dupSquareWitness14, dupSquareInner14] <;> rfl

theorem dupCubeWitness14_dedupFrontier_length :
    ∀ level, level ≤ depth dupCubeWitness14 →
      (dedupRepresentativeFrontier dupCubeWitness14 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness14_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness14 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness14 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner14 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

theorem dupCubeWitness14_uniform17_product_eq :
    2 * (17 * 1) ^ 2 * (17 * 1 * 1) = 9826 := by decide

theorem dupCubeWitness14_uniform32_product_fails :
    ¬ (2 * 32 ^ 2 * 32 ≤ 9826) := by decide

theorem dupCubeWitness14_dedup_finalTree_allLevels_rounds2_uniform17 :
    ∀ level, level ≤ depth dupCubeWitness14 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform17 dupCubeWitness14
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness14)
        3 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness14 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform17_normalizedWidth
    dupCubeWitness14 (fun _ => 15) 3 2 ParentKind.and
      dupCubeWitness14_nonemptyFanin (Nat.le_of_eq dupCubeWitness14_depth)
      (Nat.le_of_eq dupCubeWitness14_formulaSize) ?_
  intro level hlevel
  rw [dupCubeWitness14_dedupFrontier_length level hlevel,
    dupCubeWitness14_normalizedFrontierWidthSchedule level hlevel]
  decide

/-! ## Coefficient-16 finite packaging witness (S2176)

Pins ambient `8192 = 2*(16*1)^2*(16*1*1)` under factor-4 counting.  The
17-product `9826` fails at this ambient.  Packaging witness only — not
switching non-vacuity. -/

private def dupSquareInner13 : BDFormula 8192 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness13 : BDFormula 8192 :=
  .and [dupSquareInner13, dupSquareInner13]

/-- The duplicated depth-3 cube at exact ambient `8192`. -/
def dupCubeWitness13 : BDFormula 8192 :=
  .and [dupSquareWitness13, dupSquareWitness13]

private theorem dupSquareInner13_nonempty : NonemptyFaninFormula dupSquareInner13 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner13] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness13_nonempty : NonemptyFaninFormula dupSquareWitness13 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness13] at hG
  subst hG
  exact dupSquareInner13_nonempty

theorem dupCubeWitness13_nonemptyFanin : NonemptyFaninFormula dupCubeWitness13 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness13] at hG
  subst hG
  exact dupSquareWitness13_nonempty

theorem dupCubeWitness13_formulaSize : formulaSize dupCubeWitness13 = 15 := by
  simp [dupCubeWitness13, dupSquareWitness13, dupSquareInner13, formulaSize_and,
    formulaSize_lit]

theorem dupCubeWitness13_depth : depth dupCubeWitness13 = 3 := by
  simp [dupCubeWitness13, dupSquareWitness13, dupSquareInner13, depth]

theorem dupCubeWitness13_normalizedFrontierWidthSchedule :
    ∀ level, level ≤ depth dupCubeWitness13 →
      normalizedFrontierWidthSchedule dupCubeWitness13 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness13_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness13,
      dupSquareWitness13, dupSquareInner13] <;> rfl

theorem dupCubeWitness13_dedupFrontier_length :
    ∀ level, level ≤ depth dupCubeWitness13 →
      (dedupRepresentativeFrontier dupCubeWitness13 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness13_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness13 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness13 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner13 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

theorem dupCubeWitness13_uniform16_product_eq :
    2 * (16 * 1) ^ 2 * (16 * 1 * 1) = 8192 := by decide

theorem dupCubeWitness13_uniform17_product_fails :
    ¬ (2 * (17 * 1) ^ 2 * (17 * 1 * 1) ≤ 8192) := by decide

theorem dupCubeWitness13_dedup_finalTree_allLevels_rounds2_uniform16 :
    ∀ level, level ≤ depth dupCubeWitness13 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform16 dupCubeWitness13
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness13)
        3 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness13 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform16_normalizedWidth
    dupCubeWitness13 (fun _ => 15) 3 2 ParentKind.and
      dupCubeWitness13_nonemptyFanin (Nat.le_of_eq dupCubeWitness13_depth)
      (Nat.le_of_eq dupCubeWitness13_formulaSize) ?_
  intro level hlevel
  rw [dupCubeWitness13_dedupFrontier_length level hlevel,
    dupCubeWitness13_normalizedFrontierWidthSchedule level hlevel]
  decide

/-! ## Coefficient-9 finite packaging witness (S2177 Route A-sharp)

Pins ambient `1458 = 2*(9*1)^2*(9*1*1)` under factor-4 counting with the
multiplicative `9*m*w` packaging of the exact affine `(8*m*w+1)*l ≤ p`
condition.  The 16-product `8192` fails at this ambient.
Packaging witness only — not switching non-vacuity. -/

private def dupSquareInner11 : BDFormula 1458 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitness11 : BDFormula 1458 :=
  .and [dupSquareInner11, dupSquareInner11]

/-- The duplicated depth-3 cube at exact ambient `1458`. -/
def dupCubeWitness11 : BDFormula 1458 :=
  .and [dupSquareWitness11, dupSquareWitness11]

private theorem dupSquareInner11_nonempty : NonemptyFaninFormula dupSquareInner11 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInner11] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitness11_nonempty : NonemptyFaninFormula dupSquareWitness11 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitness11] at hG
  subst hG
  exact dupSquareInner11_nonempty

theorem dupCubeWitness11_nonemptyFanin : NonemptyFaninFormula dupCubeWitness11 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitness11] at hG
  subst hG
  exact dupSquareWitness11_nonempty

theorem dupCubeWitness11_formulaSize : formulaSize dupCubeWitness11 = 15 := by
  simp [dupCubeWitness11, dupSquareWitness11, dupSquareInner11, formulaSize_and,
    formulaSize_lit]

theorem dupCubeWitness11_depth : depth dupCubeWitness11 = 3 := by
  simp [dupCubeWitness11, dupSquareWitness11, dupSquareInner11, depth]

theorem dupCubeWitness11_normalizedFrontierWidthSchedule :
    ∀ level, level ≤ depth dupCubeWitness11 →
      normalizedFrontierWidthSchedule dupCubeWitness11 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness11_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitness11,
      dupSquareWitness11, dupSquareInner11] <;> rfl

theorem dupCubeWitness11_dedupFrontier_length :
    ∀ level, level ≤ depth dupCubeWitness11 →
      (dedupRepresentativeFrontier dupCubeWitness11 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitness11_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitness11 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitness11 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInner11 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

theorem dupCubeWitness11_uniform9_product_eq :
    2 * (9 * 1) ^ 2 * (9 * 1 * 1) = 1458 := by decide

theorem dupCubeWitness11_uniform16_product_fails :
    ¬ (2 * (16 * 1) ^ 2 * (16 * 1 * 1) ≤ 1458) := by decide

theorem dupCubeWitness11_dedup_finalTree_allLevels_rounds2_uniform9 :
    ∀ level, level ≤ depth dupCubeWitness11 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 dupCubeWitness11
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitness11)
        3 2 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitness11 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    dupCubeWitness11 (fun _ => 15) 3 2 ParentKind.and
      dupCubeWitness11_nonemptyFanin (Nat.le_of_eq dupCubeWitness11_depth)
      (Nat.le_of_eq dupCubeWitness11_formulaSize) ?_
  intro level hlevel
  rw [dupCubeWitness11_dedupFrontier_length level hlevel,
    dupCubeWitness11_normalizedFrontierWidthSchedule level hlevel]
  decide

/-! ## Multi-round coefficient-9 finite packaging witnesses (S2179) -/

private def dupSquareInnerU9R3 : BDFormula 13122 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitnessU9R3 : BDFormula 13122 :=
  .and [dupSquareInnerU9R3, dupSquareInnerU9R3]

/-- The depth-3 duplicated cube at exact three-round uniform-9 ambient `13122`. -/
def dupCubeWitnessU9R3 : BDFormula 13122 :=
  .and [dupSquareWitnessU9R3, dupSquareWitnessU9R3]

private theorem dupSquareInnerU9R3_nonempty : NonemptyFaninFormula dupSquareInnerU9R3 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInnerU9R3] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitnessU9R3_nonempty : NonemptyFaninFormula dupSquareWitnessU9R3 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitnessU9R3] at hG
  subst hG
  exact dupSquareInnerU9R3_nonempty

private theorem dupCubeWitnessU9R3_nonempty : NonemptyFaninFormula dupCubeWitnessU9R3 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitnessU9R3] at hG
  subst hG
  exact dupSquareWitnessU9R3_nonempty

private theorem dupCubeWitnessU9R3_size : formulaSize dupCubeWitnessU9R3 = 15 := by
  simp [dupCubeWitnessU9R3, dupSquareWitnessU9R3, dupSquareInnerU9R3, formulaSize_and,
    formulaSize_lit]

private theorem dupCubeWitnessU9R3_depth : depth dupCubeWitnessU9R3 = 3 := by
  simp [dupCubeWitnessU9R3, dupSquareWitnessU9R3, dupSquareInnerU9R3, depth]

private theorem dupCubeWitnessU9R3_widthSchedule :
    ∀ level, level ≤ depth dupCubeWitnessU9R3 →
      normalizedFrontierWidthSchedule dupCubeWitnessU9R3 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitnessU9R3_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitnessU9R3,
      dupSquareWitnessU9R3, dupSquareInnerU9R3] <;> rfl

private theorem dupCubeWitnessU9R3_dedup_length :
    ∀ level, level ≤ depth dupCubeWitnessU9R3 →
      (dedupRepresentativeFrontier dupCubeWitnessU9R3 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitnessU9R3_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitnessU9R3 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitnessU9R3 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInnerU9R3 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

theorem dupCubeWitnessU9R3_uniform9_rounds3_product_eq :
    2 * (9 * 1) ^ 3 * (9 * 1 * 1) = 13122 := by decide

theorem dupCubeWitnessU9R3_rounds3_fails_at_s2177_ambient :
    ¬ (2 * (9 * 1) ^ 3 * (9 * 1 * 1) ≤ 1458) := by decide

theorem dupCubeWitnessU9R3_dedup_finalTree_allLevels_rounds3_uniform9 :
    ∀ level, level ≤ depth dupCubeWitnessU9R3 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 dupCubeWitnessU9R3
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitnessU9R3)
        3 3 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitnessU9R3 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    dupCubeWitnessU9R3 (fun _ => 15) 3 3 ParentKind.and dupCubeWitnessU9R3_nonempty
      (Nat.le_of_eq dupCubeWitnessU9R3_depth) (Nat.le_of_eq dupCubeWitnessU9R3_size)
      ?_
  intro level hlevel
  rw [dupCubeWitnessU9R3_dedup_length level hlevel,
    dupCubeWitnessU9R3_widthSchedule level hlevel]
  decide

private def dupSquareInnerU9R4 : BDFormula 118098 :=
  .and [.lit { var := ⟨0, by decide⟩, sign := true },
        .lit { var := ⟨0, by decide⟩, sign := true }]

private def dupSquareWitnessU9R4 : BDFormula 118098 :=
  .and [dupSquareInnerU9R4, dupSquareInnerU9R4]

/-- The depth-3 duplicated cube at exact four-round uniform-9 ambient `118098`. -/
def dupCubeWitnessU9R4 : BDFormula 118098 :=
  .and [dupSquareWitnessU9R4, dupSquareWitnessU9R4]

private theorem dupSquareInnerU9R4_nonempty : NonemptyFaninFormula dupSquareInnerU9R4 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareInnerU9R4] at hG
  subst hG
  exact .lit _

private theorem dupSquareWitnessU9R4_nonempty : NonemptyFaninFormula dupSquareWitnessU9R4 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupSquareWitnessU9R4] at hG
  subst hG
  exact dupSquareInnerU9R4_nonempty

private theorem dupCubeWitnessU9R4_nonempty : NonemptyFaninFormula dupCubeWitnessU9R4 := by
  refine .and (List.cons_ne_nil _ _) ?_
  intro G hG
  simp [dupCubeWitnessU9R4] at hG
  subst hG
  exact dupSquareWitnessU9R4_nonempty

private theorem dupCubeWitnessU9R4_size : formulaSize dupCubeWitnessU9R4 = 15 := by
  simp [dupCubeWitnessU9R4, dupSquareWitnessU9R4, dupSquareInnerU9R4, formulaSize_and,
    formulaSize_lit]

private theorem dupCubeWitnessU9R4_depth : depth dupCubeWitnessU9R4 = 3 := by
  simp [dupCubeWitnessU9R4, dupSquareWitnessU9R4, dupSquareInnerU9R4, depth]

private theorem dupCubeWitnessU9R4_widthSchedule :
    ∀ level, level ≤ depth dupCubeWitnessU9R4 →
      normalizedFrontierWidthSchedule dupCubeWitnessU9R4 level = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitnessU9R4_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    simp [normalizedFrontierWidthSchedule, frontierMaxNormalizedWidth,
      normalizedDNFView_D, syntacticDNF, syntacticAndDNF, andDNF,
      FormulaSyntacticDNF.literalDNF, FormulaSyntacticDNF.trueDNF,
      formulaDepthFrontier, depthFrontier, topChildren, dupCubeWitnessU9R4,
      dupSquareWitnessU9R4, dupSquareInnerU9R4] <;> rfl

private theorem dupCubeWitnessU9R4_dedup_length :
    ∀ level, level ≤ depth dupCubeWitnessU9R4 →
      (dedupRepresentativeFrontier dupCubeWitnessU9R4 level).length = 1 := by
  intro level hlevel
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 ∨ level = 3 := by
    rw [dupCubeWitnessU9R4_depth] at hlevel
    omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact congrArg List.length (dedup_replicate_succ dupCubeWitnessU9R4 0)
  · exact congrArg List.length (dedup_replicate_succ dupSquareWitnessU9R4 1)
  · exact congrArg List.length (dedup_replicate_succ dupSquareInnerU9R4 3)
  · exact congrArg List.length (dedup_replicate_succ
      (BDFormula.lit { var := ⟨0, by decide⟩, sign := true }) 7)

theorem dupCubeWitnessU9R4_uniform9_rounds4_product_eq :
    2 * (9 * 1) ^ 4 * (9 * 1 * 1) = 118098 := by decide

theorem dupCubeWitnessU9R4_dedup_finalTree_allLevels_rounds4_uniform9 :
    ∀ level, level ≤ depth dupCubeWitnessU9R4 →
      RepresentativeNormalizedViewClassDepthFinalTreeAtUniform9 dupCubeWitnessU9R4
        (fun _ => 15) (normalizedFrontierWidthSchedule dupCubeWitnessU9R4)
        3 4 ParentKind.and level
        (dedupRepresentativeFrontier dupCubeWitnessU9R4 level) := by
  refine allDedupFrontiers_geometricCollapse_finalTree_uniform9_normalizedWidth
    dupCubeWitnessU9R4 (fun _ => 15) 3 4 ParentKind.and dupCubeWitnessU9R4_nonempty
      (Nat.le_of_eq dupCubeWitnessU9R4_depth) (Nat.le_of_eq dupCubeWitnessU9R4_size)
      ?_
  intro level hlevel
  rw [dupCubeWitnessU9R4_dedup_length level hlevel,
    dupCubeWitnessU9R4_widthSchedule level hlevel]
  decide

end FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute
end PvNP
