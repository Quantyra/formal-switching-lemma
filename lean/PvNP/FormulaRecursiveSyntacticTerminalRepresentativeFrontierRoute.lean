import PvNP.FormulaRecursiveSyntacticTerminalNormalizedViewRoute

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
membership-equal lists.  This is not semantic formula minimization, an
arbitrary bounded-depth collapse theorem, a threshold improvement, full B4,
PHP switching, Frege/PHP, a circuit lower bound, Gate A, or P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute

open BoundedDepthCanonicalDT BoundedDepthFrege BoundedDepthIteratedCollapse BoundedDepthLayerView
open BoundedDepthDecisionTree BoundedDepthRestriction CNFModel
open FormulaRecursiveClassProfile FormulaRecursiveDecomposition FormulaRecursiveDepth
open FormulaRecursiveGlobalSchedule FormulaRecursiveLayerProfile FormulaRecursiveNonempty
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

end FormulaRecursiveSyntacticTerminalRepresentativeFrontierRoute
end PvNP
