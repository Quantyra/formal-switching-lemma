import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget

/-!
# Restricted OR/AND disjoint-support synthesis class under supplied width (S2158)

This module advances Gate B after S2157 by replacing the constructor-carried
`syntacticAndListSimpleDNF` compatibility hypothesis of the recurrence-fanin
class with a purely syntactic pairwise-disjoint-support condition on AND
children.  A support function `formulaVars` collects the variables of a raw
formula; term-support inclusion lemmas show every literal of every term of the
syntactic DNF draws its variable from the support; and a synthesis lemma shows
that pairwise-disjoint child supports imply `syntacticAndListSimpleDNF` — no
hand-proved `CompatibleDNF` fact is needed for variable-disjoint ANDs.

The resulting structural class `DisjointSupportFaninFormula` embeds into the
S2157 `RecurrenceFaninFormula` class, so the whole S2157 consumer surface
(syntactic simplicity, no empty fanins, syntactic-terminal class membership,
syntactic DNF width ≤ recurrence width, frontier closure, and the formula-level
plus packed-family supplied-width final-tree routes under unchanged
`formulaClassDepthTreeBudget` / `t(d,s)=S(d)*(s-1)` and the coarse ambient
threshold) is inherited by thin wrappers.

Witnesses: the S2157 two-literal AND lies in the class with no manual
compatibility proof, and a richer AND-of-two-variable-disjoint-ORs witness on
`BDFormula 4` has recurrence width 2 and top-child count 2.

This is only a restricted disjoint-support OR/AND package.  Shared-variable
ANDs still require a supplied compatibility proof.  It does not claim
arbitrary-class width synthesis, threshold improvement, full B4, PHP switching,
Frege/PHP, NP/circuit lower bounds, P-vs-NP, or Gate A.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget

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
open FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget
open FormulaRecursiveSyntacticTerminalBoundedShallowOrOnlyTightBudget
open FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget
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
open SwitchingEncodeConstruct
open SwitchingLemmaStatement

/-! ## Syntactic variable support of a raw formula -/

/-- Syntactic variable support: constants contribute nothing, a literal
contributes its variable, gates concatenate the supports of their children
(duplicates are kept; only membership matters below). -/
def formulaVars {n : Nat} : BDFormula n → List (Fin n)
  | .tru => []
  | .fls => []
  | .lit l => [l.var]
  | .or children =>
      (children.attach.map (fun f => formulaVars f.1)).foldr (· ++ ·) []
  | .and children =>
      (children.attach.map (fun f => formulaVars f.1)).foldr (· ++ ·) []
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

/-- `or` support with the `attach` erased. -/
theorem formulaVars_or {n : Nat} (l : List (BDFormula n)) :
    formulaVars (BDFormula.or l) =
      (l.map (fun f => formulaVars f)).foldr (· ++ ·) [] := by
  rw [show formulaVars (BDFormula.or l) =
        (l.attach.map (fun f => formulaVars f.1)).foldr (· ++ ·) [] from by
      rw [formulaVars]]
  rw [List.attach_map_val l (fun f => formulaVars f)]

/-- `and` support with the `attach` erased. -/
theorem formulaVars_and {n : Nat} (l : List (BDFormula n)) :
    formulaVars (BDFormula.and l) =
      (l.map (fun f => formulaVars f)).foldr (· ++ ·) [] := by
  rw [show formulaVars (BDFormula.and l) =
        (l.attach.map (fun f => formulaVars f.1)).foldr (· ++ ·) [] from by
      rw [formulaVars]]
  rw [List.attach_map_val l (fun f => formulaVars f)]

/-- Support of a literal is its variable. -/
theorem formulaVars_lit {n : Nat} (l : Literal n) :
    formulaVars (BDFormula.lit l) = [l.var] := by
  simp only [formulaVars]

/-- Support of `tru` is empty. -/
theorem formulaVars_tru {n : Nat} :
    formulaVars (BDFormula.tru : BDFormula n) = [] := by
  simp only [formulaVars]

/-- Support of `fls` is empty. -/
theorem formulaVars_fls {n : Nat} :
    formulaVars (BDFormula.fls : BDFormula n) = [] := by
  simp only [formulaVars]

/-! ## Fold-append membership helper -/

private theorem mem_foldr_append_of_mem {α β : Type _} (f : α → List β) :
    ∀ (xs : List α) (a : α), a ∈ xs → ∀ b, b ∈ f a →
      b ∈ (xs.map f).foldr (· ++ ·) []
  | [], _, ha, _, _ => by cases ha
  | x :: xs, a, ha, b, hb => by
      simp only [List.map_cons, List.foldr]
      rcases List.mem_cons.mp ha with hEq | hMem
      · subst hEq
        exact List.mem_append.mpr (Or.inl hb)
      · exact List.mem_append.mpr
          (Or.inr (mem_foldr_append_of_mem f xs a hMem b hb))

/-! ## Term-support inclusion for the syntactic DNF expansion -/

mutual
  /-- Every literal of every term of `syntacticDNF F` draws its variable from
  `formulaVars F`. -/
  theorem litVar_mem_formulaVars_of_mem_syntacticDNF {n : Nat} :
      ∀ F : BDFormula n, ∀ t, t ∈ syntacticDNF F → ∀ l, l ∈ t →
        l.var ∈ formulaVars F
    | .tru, t, ht, l, hl => by
        have ht' : t = [] := by
          simpa [syntacticDNF, trueDNF] using ht
        subst ht'
        cases hl
    | .fls, t, ht, _, _ => by
        simp [syntacticDNF, falseDNF] at ht
    | .lit l0, t, ht, l, hl => by
        have ht' : t = [l0] := by
          simpa [syntacticDNF, literalDNF] using ht
        subst ht'
        have hl' : l = l0 := by simpa using hl
        subst hl'
        rw [formulaVars_lit]
        exact List.mem_cons_self _ _
    | .and children, t, ht, l, hl => by
        have ht' : t ∈ syntacticAndDNF children := by
          simpa [syntacticDNF] using ht
        rcases exists_child_var_of_mem_syntacticAndDNF children t ht' l hl with
          ⟨G, hG, hvar⟩
        rw [formulaVars_and]
        exact mem_foldr_append_of_mem (fun f => formulaVars f) children G hG
          l.var hvar
    | .or children, t, ht, l, hl => by
        have ht' : t ∈ syntacticOrDNF children := by
          simpa [syntacticDNF] using ht
        rcases exists_child_var_of_mem_syntacticOrDNF children t ht' l hl with
          ⟨G, hG, hvar⟩
        rw [formulaVars_or]
        exact mem_foldr_append_of_mem (fun f => formulaVars f) children G hG
          l.var hvar

  /-- Every literal of every term of an AND-list expansion draws its variable
  from the support of some child. -/
  theorem exists_child_var_of_mem_syntacticAndDNF {n : Nat} :
      ∀ children : List (BDFormula n), ∀ t, t ∈ syntacticAndDNF children →
        ∀ l, l ∈ t → ∃ G, G ∈ children ∧ l.var ∈ formulaVars G
    | [], t, ht, l, hl => by
        have ht' : t = [] := by
          simpa [syntacticAndDNF, trueDNF] using ht
        subst ht'
        cases hl
    | F :: rest, t, ht, l, hl => by
        rw [syntacticAndDNF, andDNF, List.mem_bind] at ht
        rcases ht with ⟨u, huF, ht⟩
        rw [List.mem_map] at ht
        rcases ht with ⟨v, hvRest, rfl⟩
        rcases List.mem_append.mp hl with hu | hv
        · exact ⟨F, List.mem_cons_self F rest,
            litVar_mem_formulaVars_of_mem_syntacticDNF F u huF l hu⟩
        · rcases exists_child_var_of_mem_syntacticAndDNF rest v hvRest l hv
            with ⟨G, hG, hvar⟩
          exact ⟨G, List.mem_cons_of_mem F hG, hvar⟩

  /-- Every literal of every term of an OR-list expansion draws its variable
  from the support of some child. -/
  theorem exists_child_var_of_mem_syntacticOrDNF {n : Nat} :
      ∀ children : List (BDFormula n), ∀ t, t ∈ syntacticOrDNF children →
        ∀ l, l ∈ t → ∃ G, G ∈ children ∧ l.var ∈ formulaVars G
    | [], t, ht, _, _ => by
        simp [syntacticOrDNF, falseDNF] at ht
    | F :: rest, t, ht, l, hl => by
        rw [syntacticOrDNF, orDNF] at ht
        rcases List.mem_append.mp ht with htF | htRest
        · exact ⟨F, List.mem_cons_self F rest,
            litVar_mem_formulaVars_of_mem_syntacticDNF F t htF l hl⟩
        · rcases exists_child_var_of_mem_syntacticOrDNF rest t htRest l hl
            with ⟨G, hG, hvar⟩
          exact ⟨G, List.mem_cons_of_mem F hG, hvar⟩
end

/-! ## Compatibility synthesis from disjoint supports -/

/-- If `F` and every member of `rest` are structurally simple and the support
of `F` is disjoint from the support of every member of `rest`, then the two
syntactic expansions are compatible: every distributed conjunction term stays
simple.  No constructor-carried compatibility Prop is needed. -/
theorem compatibleDNF_of_disjointSupport {n : Nat}
    {F : BDFormula n} {rest : List (BDFormula n)}
    (hF : syntacticFormulaSimpleDNF F)
    (hrest : syntacticAndListSimpleDNF rest)
    (hdisj : ∀ v ∈ formulaVars F, ∀ G ∈ rest, v ∉ formulaVars G) :
    CompatibleDNF (syntacticDNF F) (syntacticAndDNF rest) := by
  intro t ht u hu
  have htSimple : (t.map (fun l : Literal n => l.var)).Nodup :=
    simpleDNF_syntacticDNF_of_simple F hF t ht
  have huSimple : (u.map (fun l : Literal n => l.var)).Nodup :=
    simpleDNF_syntacticAndDNF_of_simple rest hrest u hu
  have hcross : ∀ x, x ∈ t.map (fun l : Literal n => l.var) →
      x ∉ u.map (fun l : Literal n => l.var) := by
    intro x hx hxu
    rcases List.mem_map.mp hx with ⟨l, hl, rfl⟩
    rcases List.mem_map.mp hxu with ⟨l', hl', hvar⟩
    have hxF : l.var ∈ formulaVars F :=
      litVar_mem_formulaVars_of_mem_syntacticDNF F t ht l hl
    rcases exists_child_var_of_mem_syntacticAndDNF rest u hu l' hl' with
      ⟨G, hG, hvarG⟩
    rw [hvar] at hvarG
    exact hdisj l.var hxF G hG hvarG
  change ((t ++ u).map (fun l : Literal n => l.var)).Nodup
  rw [List.map_append]
  exact htSimple.append huSimple (fun a ha hb => hcross a ha hb)

/-- Main synthesis theorem: structurally simple children with pairwise
disjoint supports form a structurally simple AND-list.  The per-cons
`CompatibleDNF` obligations are synthesized, not supplied. -/
theorem syntacticAndListSimpleDNF_of_disjointSupports {n : Nat} :
    ∀ children : List (BDFormula n),
      (∀ child ∈ children, syntacticFormulaSimpleDNF child) →
      List.Pairwise
        (fun F G => ∀ v ∈ formulaVars F, v ∉ formulaVars G) children →
      syntacticAndListSimpleDNF children
  | [], _, _ => by simp [syntacticAndListSimpleDNF]
  | F :: rest, hsimple, hpair => by
      cases hpair with
      | cons hhead htail =>
          have hF : syntacticFormulaSimpleDNF F :=
            hsimple F (List.mem_cons_self F rest)
          have hrest : syntacticAndListSimpleDNF rest :=
            syntacticAndListSimpleDNF_of_disjointSupports rest
              (fun child hchild => hsimple child (List.mem_cons_of_mem F hchild))
              htail
          exact And.intro hF (And.intro hrest
            (compatibleDNF_of_disjointSupport hF hrest
              (fun v hv G hG => hhead G hG v hv)))

/-! ## Restricted nonempty OR/AND disjoint-support class -/

/-- Restricted disjoint-support formula trees: constants and literals, closed
under nonempty OR and nonempty AND lists.  AND nodes carry only the purely
syntactic pairwise-disjoint-support condition on their children; the
`syntacticAndListSimpleDNF` compatibility fact is synthesized on embedding. -/
inductive DisjointSupportFaninFormula {n : Nat} : BDFormula n → Prop where
  | tru : DisjointSupportFaninFormula BDFormula.tru
  | fls : DisjointSupportFaninFormula BDFormula.fls
  | lit (l : Literal n) : DisjointSupportFaninFormula (BDFormula.lit l)
  | or {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : ∀ child, child ∈ children →
        DisjointSupportFaninFormula child) :
      DisjointSupportFaninFormula (BDFormula.or children)
  | and {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : ∀ child, child ∈ children →
        DisjointSupportFaninFormula child)
      (hdisj : List.Pairwise
        (fun F G => ∀ v ∈ formulaVars F, v ∉ formulaVars G) children) :
      DisjointSupportFaninFormula (BDFormula.and children)

/-! ## Embedding into the S2157 recurrence-fanin class -/

/-- Disjoint-support formulas are recurrence-fanin formulas: the S2157 `and`
constructor's `syntacticAndListSimpleDNF` hypothesis is discharged by the
synthesis theorem from pairwise support disjointness. -/
theorem disjointSupportFanin_recurrenceFanin {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F) :
    RecurrenceFaninFormula F := by
  induction h with
  | tru =>
      exact RecurrenceFaninFormula.tru
  | fls =>
      exact RecurrenceFaninFormula.fls
  | lit l =>
      exact RecurrenceFaninFormula.lit l
  | or hne _ ih =>
      exact RecurrenceFaninFormula.or hne ih
  | and hne _ hdisj ih =>
      exact RecurrenceFaninFormula.and hne ih
        (syntacticAndListSimpleDNF_of_disjointSupports _
          (fun child hchild =>
            recurrenceFanin_syntacticFormulaSimpleDNF (ih child hchild))
          hdisj)

/-! ## Inherited consumer surface (thin wrappers over S2157) -/

/-- Class members are syntactically simple for DNF expansion. -/
theorem disjointSupportFanin_syntacticFormulaSimpleDNF {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F) :
    syntacticFormulaSimpleDNF F :=
  recurrenceFanin_syntacticFormulaSimpleDNF
    (disjointSupportFanin_recurrenceFanin h)

/-- Class members have no empty fanins. -/
theorem disjointSupportFanin_noEmptyFanins {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F) :
    NoEmptyFanins F :=
  recurrenceFanin_noEmptyFanins (disjointSupportFanin_recurrenceFanin h)

/-- Class membership implies the restricted syntactic-terminal class. -/
theorem disjointSupportFanin_syntacticTerminalClass {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F) :
    SyntacticTerminalFormulaClass F :=
  recurrenceFanin_syntacticTerminalClass
    (disjointSupportFanin_recurrenceFanin h)

/-- Class members have syntactic DNF width at most the recurrence width. -/
theorem disjointSupportFanin_widthDNF_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F) :
    widthDNF (syntacticDNF F) ≤ formulaRecurrenceWidth F :=
  recurrenceFanin_widthDNF_le_recurrenceWidth
    (disjointSupportFanin_recurrenceFanin h)

/-- Top children of a disjoint-support formula remain disjoint-support. -/
theorem disjointSupportFanin_topChildren_closed {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F)
    {G : BDFormula n} (hG : G ∈ topChildren F) :
    DisjointSupportFaninFormula G := by
  cases h with
  | tru =>
      simp [topChildren] at hG
  | fls =>
      simp [topChildren] at hG
  | lit l =>
      simp [topChildren] at hG
  | or hne hchildren =>
      simpa [topChildren] using hchildren G hG
  | and hne hchildren _ =>
      simpa [topChildren] using hchildren G hG

/-- Recursive depth-frontier members remain disjoint-support. -/
theorem disjointSupportFanin_frontier_closed {n : Nat}
    {F : BDFormula n} (h : DisjointSupportFaninFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    DisjointSupportFaninFormula G := by
  induction level generalizing G with
  | zero =>
      have hEq : G = F := by
        simpa [formulaDepthFrontier, depthFrontier] using hG
      simpa [hEq] using h
  | succ level ih =>
      have hbind :
          G ∈ (formulaDepthFrontier level F).bind topChildren := by
        simpa [formulaDepthFrontier_succ_eq_bind_topChildren level F] using hG
      rcases List.mem_bind.mp hbind with ⟨mid, hmid, hchild⟩
      exact disjointSupportFanin_topChildren_closed (ih hmid) hchild

/-- Frontier members have actual DNF width at most the root recurrence
width. -/
theorem disjointSupportFanin_frontier_member_widthDNF_le_recurrenceWidth
    {n : Nat} {F : BDFormula n} (h : DisjointSupportFaninFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    widthDNF (syntacticDNF G) ≤ formulaRecurrenceWidth F :=
  recurrenceFanin_frontier_member_widthDNF_le_recurrenceWidth
    (disjointSupportFanin_recurrenceFanin h) level hG

/-- Every selected syntactic-terminal frontier gate has DNF width at most the
class-derived schedule `max 1 (formulaRecurrenceWidth F)`. -/
theorem disjointSupportFanin_width_le_recurrenceWidthSchedule {n : Nat}
    {F : BDFormula n} (hDS : DisjointSupportFaninFormula F)
    (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F)
    (level : Nat)
    (hk : level ≤ depth F)
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates) :
    widthDNF g.theDNF ≤ recurrenceWidthSchedule F level :=
  recurrenceFanin_width_le_recurrenceWidthSchedule
    (disjointSupportFanin_recurrenceFanin hDS) parent hClass level hk g hg

/-! ## Formula-level final-tree routing (reused S2155/S2157 consumers) -/

/-- Single-level final-tree route for a disjoint-support formula under the
class-derived width schedule, reusing the S2157 supplied-width consumer under
unchanged `formulaClassDepthTreeBudget`. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDS : DisjointSupportFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F) d rounds
      parent (disjointSupportFanin_syntacticTerminalClass hDS) level :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFanin
    F S d level rounds parent (disjointSupportFanin_recurrenceFanin hDS)
    hDepth hSize hk hn

/-- All-level final-tree route for a disjoint-support formula. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDS : DisjointSupportFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F) d
        rounds parent (disjointSupportFanin_syntacticTerminalClass hDS)
        level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
      F S d level rounds parent hDS hDepth hSize hk hn

/-! ## Packed-family disjoint-support predicates -/

/-- Every packed formula lies in the restricted disjoint-support class. -/
def SyntacticTerminalPackedFamilyDisjointSupport
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∀ d, DisjointSupportFaninFormula (syntacticTerminalPackedFamilyFormula F d)

/-- Disjoint-support packed families are recurrence-fanin packed families. -/
theorem SyntacticTerminalPackedFamilyRecurrenceFanin.of_disjointSupport
    {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyDisjointSupport F) :
    SyntacticTerminalPackedFamilyRecurrenceFanin F :=
  fun d => disjointSupportFanin_recurrenceFanin (h d)

/-- Disjoint-support packed families are in the syntactic-terminal class. -/
theorem SyntacticTerminalPackedFamilyClass.of_disjointSupport
    {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyDisjointSupport F) :
    SyntacticTerminalPackedFamilyClass F :=
  fun d => disjointSupportFanin_syntacticTerminalClass (h d)

/-- Packed-family all-level final-tree route under the S2155 supplied-width
consumer, for generic families satisfying the disjoint-support class,
class-size envelope, depth-index bound, and structural ambient hypotheses.
The class budget remains `t(d,s)=S(d)*(s-1)`.  Per-index width is
`max 1 (formulaRecurrenceWidth F_d)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportPacked
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (d : Nat) (parent : ParentKind)
    (hDS : SyntacticTerminalPackedFamilyDisjointSupport F)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S)
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      SuppliedWidthClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d) S
        (recurrenceWidthSchedule (syntacticTerminalPackedFamilyFormula F d))
        d (roundsOf d) parent
        (disjointSupportFanin_syntacticTerminalClass (hDS d)) level := by
  intro level hk
  exact
    allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFaninPacked
      d parent (fun d' => disjointSupportFanin_recurrenceFanin (hDS d'))
      hDepth hSize hAmb level hk

/-! ## S2156 OR-only formulas embed into the disjoint-support class -/

/-- OR-only formulas are disjoint-support formulas: they have no AND nodes,
so no disjointness obligation ever arises. -/
theorem orOnlyFormula_disjointSupportFanin {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
    DisjointSupportFaninFormula F := by
  induction h with
  | tru =>
      exact DisjointSupportFaninFormula.tru
  | fls =>
      exact DisjointSupportFaninFormula.fls
  | lit l =>
      exact DisjointSupportFaninFormula.lit l
  | or hne _ ih =>
      exact DisjointSupportFaninFormula.or hne ih

/-! ## Witness: the S2157 two-literal AND, with no manual compatibility -/

/-- The S2157 two-literal AND witness lies in the disjoint-support class: its
two literal children have supports `[0]` and `[1]`, which are pairwise
disjoint.  No hand-proved `CompatibleDNF` fact is used anywhere in this
proof — that is the point of the synthesis route. -/
theorem andTwoDistinctLits_disjointSupportFanin :
    DisjointSupportFaninFormula andTwoDistinctLits := by
  refine DisjointSupportFaninFormula.and (List.cons_ne_nil _ _) ?_ ?_
  · intro child hchild
    have hmem :
        child = BDFormula.lit { var := ⟨0, by decide⟩, sign := true } ∨
          child = BDFormula.lit { var := ⟨1, by decide⟩, sign := true } := by
      simpa [andTwoDistinctLits] using hchild
    rcases hmem with h | h
    · subst child; exact DisjointSupportFaninFormula.lit _
    · subst child; exact DisjointSupportFaninFormula.lit _
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
    · intro G hG
      have hG' :
          G = BDFormula.lit { var := ⟨1, by decide⟩, sign := true } := by
        simpa using hG
      subst hG'
      simp only [formulaVars_lit]
      decide
    · intro G hG
      cases hG

/-! ## Witness: an AND of two variable-disjoint ORs -/

private def lit0_4 : Literal 4 := { var := ⟨0, by decide⟩, sign := true }
private def lit1_4 : Literal 4 := { var := ⟨1, by decide⟩, sign := true }
private def lit2_4 : Literal 4 := { var := ⟨2, by decide⟩, sign := true }
private def lit3_4 : Literal 4 := { var := ⟨3, by decide⟩, sign := true }

/-- Concrete AND of two variable-disjoint ORs over `BDFormula 4` (all
positive literals on variables 0,1,2,3).  This witness is not an S2156
OR-only formula (formalized below as `andOfTwoDisjointOrs_not_orOnly`), and
certifying it in the S2157 class would have required, before this module, a
supplied `syntacticAndListSimpleDNF` compatibility hypothesis; here class
membership follows purely from the syntactic pairwise-disjoint supports
`[0,1]` and `[2,3]`. -/
def andOfTwoDisjointOrs : BDFormula 4 :=
  BDFormula.and
    [ BDFormula.or
        [ BDFormula.lit { var := ⟨0, by decide⟩, sign := true }
        , BDFormula.lit { var := ⟨1, by decide⟩, sign := true } ]
    , BDFormula.or
        [ BDFormula.lit { var := ⟨2, by decide⟩, sign := true }
        , BDFormula.lit { var := ⟨3, by decide⟩, sign := true } ] ]

private def orLeft4 : BDFormula 4 :=
  BDFormula.or [BDFormula.lit lit0_4, BDFormula.lit lit1_4]

private def orRight4 : BDFormula 4 :=
  BDFormula.or [BDFormula.lit lit2_4, BDFormula.lit lit3_4]

private theorem andOfTwoDisjointOrs_eq :
    andOfTwoDisjointOrs = BDFormula.and [orLeft4, orRight4] := rfl

private theorem orLeft4_disjointSupportFanin :
    DisjointSupportFaninFormula orLeft4 := by
  refine DisjointSupportFaninFormula.or (List.cons_ne_nil _ _) ?_
  intro child hchild
  have hmem : child = BDFormula.lit lit0_4 ∨ child = BDFormula.lit lit1_4 := by
    simpa [orLeft4] using hchild
  rcases hmem with h | h
  · subst child; exact DisjointSupportFaninFormula.lit _
  · subst child; exact DisjointSupportFaninFormula.lit _

private theorem orRight4_disjointSupportFanin :
    DisjointSupportFaninFormula orRight4 := by
  refine DisjointSupportFaninFormula.or (List.cons_ne_nil _ _) ?_
  intro child hchild
  have hmem : child = BDFormula.lit lit2_4 ∨ child = BDFormula.lit lit3_4 := by
    simpa [orRight4] using hchild
  rcases hmem with h | h
  · subst child; exact DisjointSupportFaninFormula.lit _
  · subst child; exact DisjointSupportFaninFormula.lit _

private theorem formulaVars_orLeft4 :
    formulaVars orLeft4 = [lit0_4.var, lit1_4.var] := by
  simp [orLeft4, formulaVars_or, formulaVars_lit]

private theorem formulaVars_orRight4 :
    formulaVars orRight4 = [lit2_4.var, lit3_4.var] := by
  simp [orRight4, formulaVars_or, formulaVars_lit]

private theorem orLeft4_orRight4_disjoint :
    ∀ v ∈ formulaVars orLeft4, v ∉ formulaVars orRight4 := by
  simp only [formulaVars_orLeft4, formulaVars_orRight4]
  decide

/-- The AND-of-two-disjoint-ORs witness lies in the disjoint-support class:
supports `[0,1]` and `[2,3]` are pairwise disjoint.  No hand-proved
`CompatibleDNF` fact is used. -/
theorem andOfTwoDisjointOrs_disjointSupportFanin :
    DisjointSupportFaninFormula andOfTwoDisjointOrs := by
  rw [andOfTwoDisjointOrs_eq]
  refine DisjointSupportFaninFormula.and (List.cons_ne_nil _ _) ?_ ?_
  · intro child hchild
    have hmem : child = orLeft4 ∨ child = orRight4 := by
      simpa using hchild
    rcases hmem with h | h
    · subst child; exact orLeft4_disjointSupportFanin
    · subst child; exact orRight4_disjointSupportFanin
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
    · intro G hG
      have hG' : G = orRight4 := by simpa using hG
      subst hG'
      exact orLeft4_orRight4_disjoint
    · intro G hG
      cases hG

/-- The witness is not an S2156 OR-only formula: `OrOnlyFormula` has no AND
constructor and the witness root is an AND gate, so the disjoint-support
class surface is not an OR-only restatement. -/
theorem andOfTwoDisjointOrs_not_orOnly :
    ¬ OrOnlyFormula andOfTwoDisjointOrs := by
  rw [andOfTwoDisjointOrs_eq]
  intro h
  cases h

/-- Recurrence width of the AND-of-two-disjoint-ORs is two
(`max(1,1) + max(1,1)`). -/
theorem andOfTwoDisjointOrs_recurrenceWidth :
    formulaRecurrenceWidth andOfTwoDisjointOrs = 2 := by
  simp [andOfTwoDisjointOrs, formulaRecurrenceWidth_and,
    formulaRecurrenceWidth_or, formulaRecurrenceWidth_lit,
    Nat.max_zero, Nat.max_self]

/-- Top-child count of the AND-of-two-disjoint-ORs is two. -/
theorem andOfTwoDisjointOrs_topChildCount :
    topChildCount andOfTwoDisjointOrs = 2 := by
  simp [topChildCount, topChildren, andOfTwoDisjointOrs]

/-- The AND-of-two-disjoint-ORs is syntactically terminal. -/
theorem andOfTwoDisjointOrs_syntacticTerminalClass :
    SyntacticTerminalFormulaClass andOfTwoDisjointOrs :=
  disjointSupportFanin_syntacticTerminalClass
    andOfTwoDisjointOrs_disjointSupportFanin

/-- Syntactic DNF width of the AND-of-two-disjoint-ORs is at most two. -/
theorem andOfTwoDisjointOrs_widthDNF_le_two :
    widthDNF (syntacticDNF andOfTwoDisjointOrs) ≤ 2 := by
  have h := disjointSupportFanin_widthDNF_le_recurrenceWidth
    andOfTwoDisjointOrs_disjointSupportFanin
  simpa [andOfTwoDisjointOrs_recurrenceWidth] using h

/-! ## Existence package -/

/-- Existence package: the disjoint-support class contains the S2157
two-literal AND witness and the AND-of-two-disjoint-ORs witness (recurrence
width 2, top-child count 2) with no manual compatibility proofs, embeds every
OR-only formula with recurrence width ≤ 1, and supplies a formula-level
final-tree route shape under the class-derived supplied-width schedule. -/
theorem exists_disjointSupportFanin_class_andOrWitness_orOnlyEmbed_finalTreeRoute
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDS : DisjointSupportFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    DisjointSupportFaninFormula andTwoDistinctLits ∧
      DisjointSupportFaninFormula andOfTwoDisjointOrs ∧
      formulaRecurrenceWidth andOfTwoDisjointOrs = 2 ∧
      topChildCount andOfTwoDisjointOrs = 2 ∧
      (∀ {m : Nat} {G : BDFormula m}, OrOnlyFormula G →
        DisjointSupportFaninFormula G ∧ formulaRecurrenceWidth G ≤ 1) ∧
      (∀ level, level ≤ depth F →
        SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F)
          d rounds parent (disjointSupportFanin_syntacticTerminalClass hDS)
          level) := by
  refine ⟨andTwoDistinctLits_disjointSupportFanin,
    andOfTwoDisjointOrs_disjointSupportFanin,
    andOfTwoDisjointOrs_recurrenceWidth,
    andOfTwoDisjointOrs_topChildCount, ?_, ?_⟩
  · intro m G hOr
    exact ⟨orOnlyFormula_disjointSupportFanin hOr,
      orOnlyFormula_recurrenceWidth_le_one hOr⟩
  · exact
      allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
        F S d rounds parent hDS hDepth hSize hn

end FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget
end PvNP
