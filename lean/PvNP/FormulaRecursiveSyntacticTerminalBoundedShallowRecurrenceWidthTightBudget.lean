import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowOrOnlyTightBudget

/-!
# Restricted OR/AND recurrence-width class under supplied width (S2157)

This module advances Gate B after S2156 by generalizing the OR-only class to a
restricted nonempty OR/AND formula-tree class over literals and constants with
an explicit recurrence-width measure (max under OR, sum under AND).  Class
members are proved syntactically simple (AND nodes carry the structural
`syntacticAndListSimpleDNF` / CompatibleDNF hypothesis needed for syntactic DNF
simplicity), free of empty fanins, and of syntactic DNF width at most the
recurrence width.  Top-child and recursive-frontier closure lift the recurrence
bound to every selected syntactic-terminal frontier gate.

Under a class-derived width schedule
`W ≡ Nat.max 1 (formulaRecurrenceWidth F)`, formula-level and packed-family
final-tree consumers reuse the S2155 supplied-width route under unchanged
`formulaClassDepthTreeBudget` / `t(d,s)=S(d)*(s-1)` and the coarse ambient
threshold.

S2156 OR-only formulas embed into the class with recurrence width ≤ 1.  A
concrete two-literal AND witness shows the surface is not merely another
OR-only restatement.

This is only a restricted OR/AND / recurrence-width package.  It does not claim
arbitrary-class width synthesis, threshold improvement, full B4, PHP switching,
Frege/PHP, NP/circuit lower bounds, P-vs-NP, or Gate A.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget

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

/-! ## Recurrence-width measure (max under OR, sum under AND) -/

/-- Recurrence width: constants `0`, literals `1`, OR takes the max of children,
AND takes the sum of children. -/
def formulaRecurrenceWidth {n : Nat} : BDFormula n → Nat
  | .tru => 0
  | .fls => 0
  | .lit _ => 1
  | .or children =>
      (children.attach.map (fun f => formulaRecurrenceWidth f.1)).foldr Nat.max 0
  | .and children =>
      (children.attach.map (fun f => formulaRecurrenceWidth f.1)).foldr (· + ·) 0
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

/-- `or` recurrence width with the `attach` erased. -/
theorem formulaRecurrenceWidth_or {n : Nat} (l : List (BDFormula n)) :
    formulaRecurrenceWidth (BDFormula.or l) =
      (l.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0 := by
  rw [show formulaRecurrenceWidth (BDFormula.or l) =
        (l.attach.map (fun f => formulaRecurrenceWidth f.1)).foldr Nat.max 0 from by
      rw [formulaRecurrenceWidth]]
  rw [List.attach_map_val l (fun f => formulaRecurrenceWidth f)]

/-- `and` recurrence width with the `attach` erased. -/
theorem formulaRecurrenceWidth_and {n : Nat} (l : List (BDFormula n)) :
    formulaRecurrenceWidth (BDFormula.and l) =
      (l.map (fun f => formulaRecurrenceWidth f)).foldr (· + ·) 0 := by
  rw [show formulaRecurrenceWidth (BDFormula.and l) =
        (l.attach.map (fun f => formulaRecurrenceWidth f.1)).foldr (· + ·) 0 from by
      rw [formulaRecurrenceWidth]]
  rw [List.attach_map_val l (fun f => formulaRecurrenceWidth f)]

/-- Recurrence width of a literal is one. -/
theorem formulaRecurrenceWidth_lit {n : Nat} (l : Literal n) :
    formulaRecurrenceWidth (BDFormula.lit l) = 1 := by
  simp only [formulaRecurrenceWidth]

/-- Recurrence width of `tru` is zero. -/
theorem formulaRecurrenceWidth_tru {n : Nat} :
    formulaRecurrenceWidth (BDFormula.tru : BDFormula n) = 0 := by
  simp only [formulaRecurrenceWidth]

/-- Recurrence width of `fls` is zero. -/
theorem formulaRecurrenceWidth_fls {n : Nat} :
    formulaRecurrenceWidth (BDFormula.fls : BDFormula n) = 0 := by
  simp only [formulaRecurrenceWidth]

/-! ## Fold lemmas for max / sum -/

private theorem foldr_max_of_mem (xs : List Nat) (x : Nat) (hx : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => cases hx
  | cons head tail ih =>
      rcases List.mem_cons.mp hx with hEq | hMem
      · rw [hEq]
        exact Nat.le_max_left head (tail.foldr Nat.max 0)
      · exact Nat.le_trans (ih hMem) (Nat.le_max_right head (tail.foldr Nat.max 0))

private theorem foldr_add_of_mem (xs : List Nat) (x : Nat) (hx : x ∈ xs) :
    x ≤ xs.foldr (· + ·) 0 := by
  induction xs with
  | nil => cases hx
  | cons head tail ih =>
      rcases List.mem_cons.mp hx with hEq | hMem
      · rw [hEq]
        exact Nat.le_add_right head (tail.foldr (· + ·) 0)
      · exact Nat.le_trans (ih hMem)
          (Nat.le_add_left (tail.foldr (· + ·) 0) head)

private theorem map_mem_of_mem {α β : Type _} (f : α → β)
    (xs : List α) (x : α) (hx : x ∈ xs) : f x ∈ xs.map f :=
  List.mem_map_of_mem f hx

/-! ## Restricted nonempty OR/AND recurrence-fanin class -/

/-- Restricted recurrence-fanin formula trees: constants and literals, closed
under nonempty OR and nonempty AND lists.  AND nodes carry the structural
simplicity hypothesis `syntacticAndListSimpleDNF` so syntactic DNF simplicity
holds by construction. -/
inductive RecurrenceFaninFormula {n : Nat} : BDFormula n → Prop where
  | tru : RecurrenceFaninFormula BDFormula.tru
  | fls : RecurrenceFaninFormula BDFormula.fls
  | lit (l : Literal n) : RecurrenceFaninFormula (BDFormula.lit l)
  | or {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : ∀ child, child ∈ children → RecurrenceFaninFormula child) :
      RecurrenceFaninFormula (BDFormula.or children)
  | and {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : ∀ child, child ∈ children → RecurrenceFaninFormula child)
      (hsimple : syntacticAndListSimpleDNF children) :
      RecurrenceFaninFormula (BDFormula.and children)

/-! ## Structural simplicity, no empty fanins, syntactic width ≤ recurrence -/

/-- Every disjunct of a structurally simple OR-list is simple. -/
private theorem syntacticOrListSimpleDNF_of_forall {n : Nat} :
    ∀ children : List (BDFormula n),
      (∀ F, F ∈ children → syntacticFormulaSimpleDNF F) →
        syntacticOrListSimpleDNF children
  | [], _ => by
      simp [syntacticOrListSimpleDNF]
  | F :: rest, h => by
      refine And.intro (h F (List.mem_cons_self F rest)) ?_
      exact syntacticOrListSimpleDNF_of_forall rest
        (fun G hG => h G (List.mem_cons_of_mem F hG))

/-- Class members are syntactically simple for DNF expansion. -/
theorem recurrenceFanin_syntacticFormulaSimpleDNF {n : Nat}
    {F : BDFormula n} (h : RecurrenceFaninFormula F) :
    syntacticFormulaSimpleDNF F := by
  induction h with
  | tru =>
      simp [syntacticFormulaSimpleDNF]
  | fls =>
      simp [syntacticFormulaSimpleDNF]
  | lit _ =>
      simp [syntacticFormulaSimpleDNF]
  | or _ _ ih =>
      change syntacticOrListSimpleDNF _
      exact syntacticOrListSimpleDNF_of_forall _ ih
  | and _ _ hsimple _ =>
      change syntacticAndListSimpleDNF _
      exact hsimple

/-- Class members have no empty fanins. -/
theorem recurrenceFanin_noEmptyFanins {n : Nat}
    {F : BDFormula n} (h : RecurrenceFaninFormula F) :
    NoEmptyFanins F := by
  induction h with
  | tru =>
      exact NoEmptyFanins.tru
  | fls =>
      exact NoEmptyFanins.fls
  | lit l =>
      exact NoEmptyFanins.lit l
  | or hne _ ih =>
      exact NoEmptyFanins.or hne ih
  | and hne _ _ ih =>
      exact NoEmptyFanins.and hne ih

/-- Class membership implies the restricted syntactic-terminal class. -/
theorem recurrenceFanin_syntacticTerminalClass {n : Nat}
    {F : BDFormula n} (h : RecurrenceFaninFormula F) :
    SyntacticTerminalFormulaClass F :=
  ⟨recurrenceFanin_syntacticFormulaSimpleDNF h, recurrenceFanin_noEmptyFanins h⟩

/-- Width of a syntactic OR-list is at most the max of child recurrence widths. -/
theorem widthDNF_syntacticOrDNF_le_foldr_max {n : Nat} :
    ∀ children : List (BDFormula n),
      (∀ G, G ∈ children →
        widthDNF (syntacticDNF G) ≤ formulaRecurrenceWidth G) →
        widthDNF (syntacticOrDNF children) ≤
          (children.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0
  | [], _ => by
      simp [syntacticOrDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
  | G :: rest, h => by
      have hG : widthDNF (syntacticDNF G) ≤ formulaRecurrenceWidth G :=
        h G (List.mem_cons_self G rest)
      have hRest :
          widthDNF (syntacticOrDNF rest) ≤
            (rest.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0 :=
        widthDNF_syntacticOrDNF_le_foldr_max rest
          (fun H hH => h H (List.mem_cons_of_mem G hH))
      have hB :
          widthDNF (syntacticDNF G) ≤
            Nat.max (formulaRecurrenceWidth G)
              ((rest.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0) :=
        Nat.le_trans hG (Nat.le_max_left _ _)
      have hB' :
          widthDNF (syntacticOrDNF rest) ≤
            Nat.max (formulaRecurrenceWidth G)
              ((rest.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0) :=
        Nat.le_trans hRest (Nat.le_max_right _ _)
      simp only [syntacticOrDNF, List.map_cons, List.foldr]
      exact widthDNF_orDNF_le hB hB'

/-- Width of a syntactic AND-list is at most the sum of child recurrence widths. -/
theorem widthDNF_syntacticAndDNF_le_foldr_add {n : Nat} :
    ∀ children : List (BDFormula n),
      (∀ G, G ∈ children →
        widthDNF (syntacticDNF G) ≤ formulaRecurrenceWidth G) →
        widthDNF (syntacticAndDNF children) ≤
          (children.map (fun f => formulaRecurrenceWidth f)).foldr (· + ·) 0
  | [], _ => by
      have h : widthDNF (syntacticAndDNF ([] : List (BDFormula n))) = 0 := by
        simp [syntacticAndDNF, FormulaSyntacticDNF.trueDNF, widthDNF, termWidth]
      simpa [List.map_nil, List.foldr] using (le_of_eq h)
  | G :: rest, h => by
      have hG : widthDNF (syntacticDNF G) ≤ formulaRecurrenceWidth G :=
        h G (List.mem_cons_self G rest)
      have hRest :
          widthDNF (syntacticAndDNF rest) ≤
            (rest.map (fun f => formulaRecurrenceWidth f)).foldr (· + ·) 0 :=
        widthDNF_syntacticAndDNF_le_foldr_add rest
          (fun H hH => h H (List.mem_cons_of_mem G hH))
      simp only [syntacticAndDNF, List.map_cons, List.foldr]
      exact widthDNF_andDNF_le_add hG hRest

/-- Every raw formula's syntactic DNF width is bounded by its recurrence width.
This is structural bookkeeping and requires no formula-class hypothesis. -/
theorem widthDNF_syntacticDNF_le_recurrenceWidth {n : Nat} :
    ∀ F : BDFormula n,
      widthDNF (syntacticDNF F) ≤ formulaRecurrenceWidth F
  | .tru => by
      simp [syntacticDNF, FormulaSyntacticDNF.trueDNF, widthDNF, termWidth,
        formulaRecurrenceWidth]
  | .fls => by
      simp [syntacticDNF, FormulaSyntacticDNF.falseDNF, widthDNF,
        formulaRecurrenceWidth]
  | .lit l => by
      simp [syntacticDNF, FormulaSyntacticDNF.literalDNF, widthDNF, termWidth,
        formulaRecurrenceWidth]
  | .or children => by
      change widthDNF (syntacticOrDNF children) ≤ _
      simpa [formulaRecurrenceWidth_or] using
        widthDNF_syntacticOrDNF_le_foldr_max children
          (fun G _ => widthDNF_syntacticDNF_le_recurrenceWidth G)
  | .and children => by
      change widthDNF (syntacticAndDNF children) ≤ _
      simpa [formulaRecurrenceWidth_and] using
        widthDNF_syntacticAndDNF_le_foldr_add children
          (fun G _ => widthDNF_syntacticDNF_le_recurrenceWidth G)
  termination_by F => sizeOf F

/-- Class members have syntactic DNF width at most the recurrence width. -/
theorem recurrenceFanin_widthDNF_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (_h : RecurrenceFaninFormula F) :
    widthDNF (syntacticDNF F) ≤ formulaRecurrenceWidth F :=
  widthDNF_syntacticDNF_le_recurrenceWidth F

/-! ## Empty-fanin boundary witness -/

/-- The raw empty AND at ambient arity one. -/
def emptyAndOne : BDFormula 1 := .and []

/-- Empty AND has recurrence width zero. -/
theorem emptyAndOne_recurrenceWidth : formulaRecurrenceWidth emptyAndOne = 0 := by
  simp [emptyAndOne, formulaRecurrenceWidth_and]

/-- Empty AND's syntactic DNF has width at most zero. -/
theorem emptyAndOne_syntacticWidth_le_zero :
    widthDNF (syntacticDNF emptyAndOne) ≤ 0 := by
  simpa [emptyAndOne_recurrenceWidth] using
    widthDNF_syntacticDNF_le_recurrenceWidth emptyAndOne

/-! ## Top-child and recursive-frontier closure -/

/-- Top children of a recurrence-fanin formula remain recurrence-fanin. -/
theorem recurrenceFanin_topChildren_closed {n : Nat}
    {F : BDFormula n} (h : RecurrenceFaninFormula F)
    {G : BDFormula n} (hG : G ∈ topChildren F) :
    RecurrenceFaninFormula G := by
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

/-- Recursive depth-frontier members remain recurrence-fanin. -/
theorem recurrenceFanin_frontier_closed {n : Nat}
    {F : BDFormula n} (h : RecurrenceFaninFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    RecurrenceFaninFormula G := by
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
      exact recurrenceFanin_topChildren_closed (ih hmid) hchild

/-- A top child has recurrence width at most the parent's. -/
theorem formulaRecurrenceWidth_topChild_le {n : Nat}
    (F G : BDFormula n) (hG : G ∈ topChildren F) :
    formulaRecurrenceWidth G ≤ formulaRecurrenceWidth F := by
  cases F with
  | tru =>
      simp [topChildren] at hG
  | fls =>
      simp [topChildren] at hG
  | lit l =>
      simp [topChildren] at hG
  | or children =>
      have hmem : formulaRecurrenceWidth G ∈
          children.map (fun f => formulaRecurrenceWidth f) := by
        simpa [topChildren] using
          map_mem_of_mem (fun f => formulaRecurrenceWidth f) children G hG
      simpa [formulaRecurrenceWidth_or] using
        foldr_max_of_mem _ _ hmem
  | and children =>
      have hmem : formulaRecurrenceWidth G ∈
          children.map (fun f => formulaRecurrenceWidth f) := by
        simpa [topChildren] using
          map_mem_of_mem (fun f => formulaRecurrenceWidth f) children G hG
      simpa [formulaRecurrenceWidth_and] using
        foldr_add_of_mem _ _ hmem

/-- Frontier members have recurrence width at most the root's. -/
theorem recurrenceFanin_frontier_member_recurrenceWidth_le {n : Nat}
    {F : BDFormula n} (_h : RecurrenceFaninFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    formulaRecurrenceWidth G ≤ formulaRecurrenceWidth F := by
  induction level generalizing G with
  | zero =>
      have hEq : G = F := by
        simpa [formulaDepthFrontier, depthFrontier] using hG
      simp [hEq]
  | succ level ih =>
      have hbind :
          G ∈ (formulaDepthFrontier level F).bind topChildren := by
        simpa [formulaDepthFrontier_succ_eq_bind_topChildren level F] using hG
      rcases List.mem_bind.mp hbind with ⟨mid, hmid, hchild⟩
      exact Nat.le_trans (formulaRecurrenceWidth_topChild_le mid G hchild) (ih hmid)

/-- Frontier members have actual DNF width at most the root recurrence width. -/
theorem recurrenceFanin_frontier_member_widthDNF_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (h : RecurrenceFaninFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    widthDNF (syntacticDNF G) ≤ formulaRecurrenceWidth F :=
  Nat.le_trans
    (recurrenceFanin_widthDNF_le_recurrenceWidth
      (recurrenceFanin_frontier_closed h level hG))
    (recurrenceFanin_frontier_member_recurrenceWidth_le h level hG)

/-! ## Recurrence width ≤ formula size (for class-envelope discharge) -/

private theorem formulaRecurrenceWidth_le_formulaSize {n : Nat} :
    ∀ F : BDFormula n, formulaRecurrenceWidth F ≤ formulaSize F
  | .tru => by
      simp [formulaRecurrenceWidth, formulaSize]
  | .fls => by
      simp [formulaRecurrenceWidth, formulaSize]
  | .lit _ => by
      simp [formulaRecurrenceWidth, formulaSize]
  | .or children => by
      have ih : ∀ G ∈ children,
          formulaRecurrenceWidth G ≤ formulaSize G := fun G _ =>
        formulaRecurrenceWidth_le_formulaSize G
      have hmap :
          (children.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0 ≤
            (children.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
        induction children with
        | nil => simp
        | cons G rest ihrest =>
            have hG := ih G (List.mem_cons_self G rest)
            have hrest :
                (rest.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0 ≤
                  (rest.map (fun f => formulaSize f)).foldr (· + ·) 0 :=
              ihrest (fun H hH => ih H (List.mem_cons_of_mem G hH))
            have hmax :
                Nat.max (formulaRecurrenceWidth G)
                    ((rest.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0) ≤
                  formulaSize G +
                    (rest.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
              exact Nat.max_le.mpr
                ⟨Nat.le_trans hG (Nat.le_add_right _ _),
                  Nat.le_trans hrest (Nat.le_add_left _ _)⟩
            simpa [List.map_cons, List.foldr] using hmax
      have hsize :
          formulaSize (BDFormula.or children) =
            1 + (children.map (fun f => formulaSize f)).foldr (· + ·) 0 :=
        formulaSize_or children
      have hrec :
          formulaRecurrenceWidth (BDFormula.or children) =
            (children.map (fun f => formulaRecurrenceWidth f)).foldr Nat.max 0 :=
        formulaRecurrenceWidth_or children
      omega
  | .and children => by
      have ih : ∀ G ∈ children,
          formulaRecurrenceWidth G ≤ formulaSize G := fun G _ =>
        formulaRecurrenceWidth_le_formulaSize G
      have hmap :
          (children.map (fun f => formulaRecurrenceWidth f)).foldr (· + ·) 0 ≤
            (children.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
        induction children with
        | nil => simp
        | cons G rest ihrest =>
            have hG := ih G (List.mem_cons_self G rest)
            have hrest :
                (rest.map (fun f => formulaRecurrenceWidth f)).foldr (· + ·) 0 ≤
                  (rest.map (fun f => formulaSize f)).foldr (· + ·) 0 :=
              ihrest (fun H hH => ih H (List.mem_cons_of_mem G hH))
            simpa [List.map_cons, List.foldr] using Nat.add_le_add hG hrest
      have hsize :
          formulaSize (BDFormula.and children) =
            1 + (children.map (fun f => formulaSize f)).foldr (· + ·) 0 :=
        formulaSize_and children
      have hrec :
          formulaRecurrenceWidth (BDFormula.and children) =
            (children.map (fun f => formulaRecurrenceWidth f)).foldr (· + ·) 0 :=
        formulaRecurrenceWidth_and children
      omega
termination_by F => sizeOf F

/-- Class-derived positive width schedule: `max 1 (formulaRecurrenceWidth F)`. -/
def recurrenceWidthSchedule {n : Nat} (F : BDFormula n) : Nat → Nat :=
  fun _ => Nat.max 1 (formulaRecurrenceWidth F)

theorem recurrenceWidthSchedule_pos {n : Nat} (F : BDFormula n) (level : Nat) :
    1 ≤ recurrenceWidthSchedule F level := by
  simp [recurrenceWidthSchedule, Nat.le_max_left]

theorem recurrenceWidthSchedule_le_formulaSize {n : Nat} (F : BDFormula n)
    (level : Nat) :
    recurrenceWidthSchedule F level ≤ formulaSize F := by
  simp only [recurrenceWidthSchedule]
  have hw : formulaRecurrenceWidth F ≤ formulaSize F :=
    formulaRecurrenceWidth_le_formulaSize F
  have hsize : 1 ≤ formulaSize F := by
    cases F <;> simp [formulaSize]
  exact Nat.max_le.mpr ⟨hsize, hw⟩

theorem recurrenceWidthSchedule_le_classSize {n : Nat} (F : BDFormula n)
    (S : Nat → Nat) (d level : Nat) (hSize : formulaSize F ≤ S d) :
    recurrenceWidthSchedule F level ≤ S d :=
  Nat.le_trans (recurrenceWidthSchedule_le_formulaSize F level) hSize

/-! ## Selected GateSpec width against the recurrence schedule -/

/-- Intermediate (non-terminal) selected GateSpec DNF width is at most the root
recurrence width. -/
theorem recurrenceFanin_intermediate_gate_width_le_recurrenceWidth {n : Nat}
    {F : BDFormula n} (hRec : RecurrenceFaninFormula F)
    (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F)
    (level : Nat)
    (_hk : level ≤ depth F)
    (hlevel : level ≠ depth F)
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates) :
    widthDNF g.theDNF ≤ formulaRecurrenceWidth F := by
  have hg' : List.Mem g (syntacticFrontierMinimalLayer F level parent
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
        hClass.1)).gates := by
    simpa [syntacticTerminalFrontierLayer, hlevel] using hg
  have hg'' : List.Mem g (syntacticFrontierGateList F level
      (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
        hClass.1)) := by
    simpa [syntacticFrontierMinimalLayer, syntacticFrontierGateLayer] using hg'
  rw [syntacticFrontierGateList] at hg''
  rcases List.mem_map.mp hg'' with ⟨G, _, rfl⟩
  have hDNF :
      (syntacticSimpleFormulaGate G.1
        (frontierSyntacticSimple_of_syntacticFormulaSimpleDNF F level
          hClass.1 G.1 G.2)).theDNF =
        syntacticDNF G.1 := by
    simp [syntacticSimpleFormulaGate, syntacticDNFViewOfFormulaSimple,
      syntacticDNFView, GateSpec.theDNF]
  have hwidth : widthDNF (syntacticDNF G.1) ≤ formulaRecurrenceWidth F :=
    recurrenceFanin_frontier_member_widthDNF_le_recurrenceWidth hRec level G.2
  simpa [hDNF] using hwidth

/-- Every selected syntactic-terminal frontier gate has DNF width at most the
class-derived schedule `max 1 (formulaRecurrenceWidth F)`. -/
theorem recurrenceFanin_width_le_recurrenceWidthSchedule {n : Nat}
    {F : BDFormula n} (hRec : RecurrenceFaninFormula F)
    (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F)
    (level : Nat)
    (hk : level ≤ depth F)
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates) :
    widthDNF g.theDNF ≤ recurrenceWidthSchedule F level := by
  have hbudget : recurrenceWidthSchedule F level =
      Nat.max 1 (formulaRecurrenceWidth F) := rfl
  by_cases hlevel : level = depth F
  · subst hlevel
    have hg' : List.Mem g (terminalLayerMinimalLayer F parent).gates := by
      simpa [syntacticTerminalFrontierLayer] using hg
    have hterm : widthDNF g.theDNF ≤ 1 := by
      simpa [terminalLayerWidthBudget] using
        terminalLayerMinimalLayer_width_le_budget F parent g hg'
    exact Nat.le_trans hterm (by
      simp only [recurrenceWidthSchedule]
      exact Nat.le_max_left 1 _)
  · have hwidth :
        widthDNF g.theDNF ≤ formulaRecurrenceWidth F :=
      recurrenceFanin_intermediate_gate_width_le_recurrenceWidth hRec parent
        hClass level hk hlevel g hg
    exact Nat.le_trans hwidth (by
      simp only [recurrenceWidthSchedule]
      exact Nat.le_max_right 1 _)

/-! ## Formula-level final-tree routing via S2155 supplied-width consumers -/

/-- Single-level final-tree route for a recurrence-fanin formula under the
class-derived width schedule, reusing the S2155 supplied-width consumer under
unchanged `formulaClassDepthTreeBudget`. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFanin
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hRec : RecurrenceFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F) d rounds parent
      (recurrenceFanin_syntacticTerminalClass hRec) level := by
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree
      F S (recurrenceWidthSchedule F) d level rounds parent hDepth hSize
      (recurrenceFanin_syntacticTerminalClass hRec) hk ?hwL
      (recurrenceWidthSchedule_pos F level)
      (recurrenceWidthSchedule_le_classSize F S d level hSize) hn
  intro g hg
  exact recurrenceFanin_width_le_recurrenceWidthSchedule hRec parent
    (recurrenceFanin_syntacticTerminalClass hRec) level hk g hg

/-- All-level final-tree route for a recurrence-fanin formula. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFanin
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hRec : RecurrenceFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F) d rounds parent
        (recurrenceFanin_syntacticTerminalClass hRec) level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFanin
      F S d level rounds parent hRec hDepth hSize hk hn

/-! ## Packed-family recurrence-fanin predicates -/

/-- Every packed formula lies in the restricted recurrence-fanin class. -/
def SyntacticTerminalPackedFamilyRecurrenceFanin
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∀ d, RecurrenceFaninFormula (syntacticTerminalPackedFamilyFormula F d)

/-- Recurrence-fanin packed families are in the syntactic-terminal class. -/
theorem SyntacticTerminalPackedFamilyClass.of_recurrenceFanin
    {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyRecurrenceFanin F) :
    SyntacticTerminalPackedFamilyClass F :=
  fun d => recurrenceFanin_syntacticTerminalClass (h d)

/-- All-level gate width ≤ recurrence schedule for a recurrence-fanin packed
family (discharged from class membership). -/
theorem recurrenceFaninPackedFamily_width_le_recurrenceWidthSchedule
    {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyRecurrenceFanin F)
    (d : Nat) (parent : ParentKind)
    (level : Nat)
    (hk : level ≤ depth (syntacticTerminalPackedFamilyFormula F d))
    (g : GateSpec (syntacticTerminalPackedFamilyArity F d))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (syntacticTerminalPackedFamilyFormula F d) level parent
      (recurrenceFanin_syntacticTerminalClass (h d))).gates) :
    widthDNF g.theDNF ≤
      recurrenceWidthSchedule (syntacticTerminalPackedFamilyFormula F d) level :=
  recurrenceFanin_width_le_recurrenceWidthSchedule (h d) parent
    (recurrenceFanin_syntacticTerminalClass (h d)) level hk g hg

private theorem structuralAmbient_entry
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf)
    (d : Nat) :
    2 * (64 * S d) ^ roundsOf d * (64 * S d * S d) ≤
      syntacticTerminalPackedFamilyArity F d := by
  simpa [SyntacticTerminalPackedFamilyStructuralAmbientAdequate,
    syntacticTerminalClassCoarseEntryThreshold] using hAmb d

/-- Packed-family all-level final-tree route under the S2155 supplied-width
consumer, for generic families satisfying the recurrence-fanin class,
class-size envelope, depth-index bound, and structural ambient hypotheses.
The class budget remains `t(d,s)=S(d)*(s-1)`.  Per-index width is
`max 1 (formulaRecurrenceWidth F_d)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFaninPacked
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (d : Nat) (parent : ParentKind)
    (hRec : SyntacticTerminalPackedFamilyRecurrenceFanin F)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S)
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      SuppliedWidthClassDepthFinalTreeAt
        (syntacticTerminalPackedFamilyFormula F d) S
        (recurrenceWidthSchedule (syntacticTerminalPackedFamilyFormula F d))
        d (roundsOf d) parent
        (recurrenceFanin_syntacticTerminalClass (hRec d)) level := by
  intro level hk
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFanin
      (syntacticTerminalPackedFamilyFormula F d) S d level (roundsOf d) parent
      (hRec d) (hDepth d) ?hSize hk ?hn
  · simpa [syntacticTerminalPackedFamilySizeCap] using hSize d
  · exact structuralAmbient_entry hAmb d

/-! ## S2156 OR-only formulas embed into the recurrence-fanin class -/

/-- OR-only formulas are recurrence-fanin formulas. -/
theorem orOnlyFormula_recurrenceFanin {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
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

/-- Fold-max of a list of values each ≤ 1 is itself ≤ 1. -/
private theorem foldr_max_le_one_of_forall (xs : List Nat)
    (h : ∀ x, x ∈ xs → x ≤ 1) : xs.foldr Nat.max 0 ≤ 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (List.mem_cons_self x xs)
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.foldr]
      exact Nat.max_le.mpr ⟨hx, hxs⟩

/-- OR-only formulas have recurrence width at most one. -/
theorem orOnlyFormula_recurrenceWidth_le_one {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
    formulaRecurrenceWidth F ≤ 1 := by
  induction h with
  | tru =>
      simp [formulaRecurrenceWidth_tru]
  | fls =>
      simp [formulaRecurrenceWidth_fls]
  | lit l =>
      simp [formulaRecurrenceWidth_lit]
  | or _ _ ih =>
      rw [formulaRecurrenceWidth_or]
      exact foldr_max_le_one_of_forall _
        (fun x hx => by
          rcases List.mem_map.mp hx with ⟨G, hG, rfl⟩
          exact ih G hG)

/-! ## Concrete two-literal AND witness -/

/-- Concrete AND of two distinct-variable positive literals on `BDFormula 2`. -/
def andTwoDistinctLits : BDFormula 2 :=
  BDFormula.and
    [ BDFormula.lit { var := ⟨0, by decide⟩, sign := true }
    , BDFormula.lit { var := ⟨1, by decide⟩, sign := true } ]

private def lit0_2 : Literal 2 := { var := ⟨0, by decide⟩, sign := true }
private def lit1_2 : Literal 2 := { var := ⟨1, by decide⟩, sign := true }

private theorem compatible_lit0_lit1 :
    CompatibleDNF (syntacticDNF (BDFormula.lit lit0_2))
      (syntacticAndDNF [BDFormula.lit lit1_2]) := by
  intro t ht u hu
  have ht' : t = [lit0_2] := by
    simpa [syntacticDNF, FormulaSyntacticDNF.literalDNF] using ht
  have hu' : u = [lit1_2] := by
    -- andDNF [[lit1]] [[]] = [[lit1]]
    simp only [syntacticAndDNF, FormulaSyntacticDNF.andDNF,
      FormulaSyntacticDNF.trueDNF, FormulaSyntacticDNF.literalDNF,
      syntacticDNF, List.bind_cons, List.map_cons, List.map_nil,
      List.bind_nil, List.cons_append, List.nil_append] at hu
    simpa using hu
  rw [ht', hu']
  -- SimpleTerm [lit0, lit1]: mapped vars [0, 1] are Nodup
  change (List.map (fun l : Literal 2 => l.var) [lit0_2, lit1_2]).Nodup
  simp [lit0_2, lit1_2]

private theorem compatible_lit1_true :
    CompatibleDNF (syntacticDNF (BDFormula.lit lit1_2))
      (syntacticAndDNF ([] : List (BDFormula 2))) := by
  intro t ht u hu
  have ht' : t = [lit1_2] := by
    simpa [syntacticDNF, FormulaSyntacticDNF.literalDNF] using ht
  have hu' : u = [] := by
    simpa [syntacticAndDNF, FormulaSyntacticDNF.trueDNF] using hu
  rw [ht', hu']
  change (List.map (fun l : Literal 2 => l.var) [lit1_2]).Nodup
  simp [lit1_2]

private theorem syntacticAndListSimpleDNF_twoLits :
    syntacticAndListSimpleDNF
      [ BDFormula.lit lit0_2, BDFormula.lit lit1_2 ] := by
  refine And.intro (by simp [syntacticFormulaSimpleDNF]) ?_
  refine And.intro ?_ compatible_lit0_lit1
  refine And.intro (by simp [syntacticFormulaSimpleDNF]) ?_
  refine And.intro (by simp [syntacticAndListSimpleDNF]) ?_
  exact compatible_lit1_true

/-- The two-literal AND witness is recurrence-fanin. -/
theorem andTwoDistinctLits_recurrenceFanin :
    RecurrenceFaninFormula andTwoDistinctLits := by
  refine RecurrenceFaninFormula.and (List.cons_ne_nil _ _) ?_ ?_
  · intro child hchild
    have hmem :
        child = BDFormula.lit lit0_2 ∨ child = BDFormula.lit lit1_2 := by
      simpa [andTwoDistinctLits, lit0_2, lit1_2] using hchild
    rcases hmem with h | h
    · subst child; exact RecurrenceFaninFormula.lit _
    · subst child; exact RecurrenceFaninFormula.lit _
  · simpa [andTwoDistinctLits, lit0_2, lit1_2] using
      syntacticAndListSimpleDNF_twoLits

/-- Recurrence width of the two-literal AND is two. -/
theorem andTwoDistinctLits_recurrenceWidth :
    formulaRecurrenceWidth andTwoDistinctLits = 2 := by
  simp [andTwoDistinctLits, formulaRecurrenceWidth_and, formulaRecurrenceWidth_lit,
    lit0_2, lit1_2]

/-- Top-child count of the two-literal AND is two. -/
theorem andTwoDistinctLits_topChildCount :
    topChildCount andTwoDistinctLits = 2 := by
  simp [topChildCount, topChildren, andTwoDistinctLits]

/-- The two-literal AND is syntactically terminal. -/
theorem andTwoDistinctLits_syntacticTerminalClass :
    SyntacticTerminalFormulaClass andTwoDistinctLits :=
  recurrenceFanin_syntacticTerminalClass andTwoDistinctLits_recurrenceFanin

/-- Syntactic DNF width of the two-literal AND is at most two. -/
theorem andTwoDistinctLits_widthDNF_le_two :
    widthDNF (syntacticDNF andTwoDistinctLits) ≤ 2 := by
  have h := recurrenceFanin_widthDNF_le_recurrenceWidth
    andTwoDistinctLits_recurrenceFanin
  simpa [andTwoDistinctLits_recurrenceWidth] using h

/-! ## Existence package -/

/-- Existence package: the recurrence-fanin class admits a concrete AND
member with recurrence width 2 and top-child count 2, embeds every OR-only
formula with recurrence width ≤ 1, and supplies a formula-level final-tree
route shape under the class-derived supplied-width schedule. -/
theorem exists_recurrenceFanin_class_andWitness_orOnlyEmbed_finalTreeRoute
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hRec : RecurrenceFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    RecurrenceFaninFormula andTwoDistinctLits ∧
      formulaRecurrenceWidth andTwoDistinctLits = 2 ∧
      topChildCount andTwoDistinctLits = 2 ∧
      (∀ {m : Nat} {G : BDFormula m}, OrOnlyFormula G →
        RecurrenceFaninFormula G ∧ formulaRecurrenceWidth G ≤ 1) ∧
      (∀ level, level ≤ depth F →
        SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F)
          d rounds parent (recurrenceFanin_syntacticTerminalClass hRec) level) := by
  refine ⟨andTwoDistinctLits_recurrenceFanin,
    andTwoDistinctLits_recurrenceWidth,
    andTwoDistinctLits_topChildCount, ?_, ?_⟩
  · intro m G hOr
    exact ⟨orOnlyFormula_recurrenceFanin hOr, orOnlyFormula_recurrenceWidth_le_one hOr⟩
  · exact
      allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_recurrenceFanin
        F S d rounds parent hRec hDepth hSize hn

end FormulaRecursiveSyntacticTerminalBoundedShallowRecurrenceWidthTightBudget
end PvNP
