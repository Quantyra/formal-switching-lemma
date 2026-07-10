import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowTightBudget

/-!
# Bounded-shallow OR-only class under the tight budget (S2156)

This module advances Gate B after S2155 by generalizing the pure nested-OR
witness to a restricted nonempty OR-only formula-tree class over literals and
constants.  Class members are proved syntactically simple, free of empty
fanins, and of syntactic DNF width at most `1`.  Top-child and recursive
frontier closure lift width-one discharge to every selected syntactic-terminal
frontier gate.  Under the bounded-shallow restriction `depth F ≤ k`, the
S2155 tight width envelope with `W = 1` is discharged, and formula-level plus
packed-family final-tree consumers reuse the existing S2155
supplied/bounded-shallow route under unchanged
`formulaClassDepthTreeBudget` / `t(d,s)=S(d)*(s-1)` and the coarse ambient
threshold.

The S2155 nested-OR family is shown to instantiate the class; a concrete
fan-in-three branching OR-only witness shows the surface is not merely another
nested-OR spine restatement.  No second packed numeric family is introduced.

This is only a restricted OR-only / bounded-shallow package.  It does not
claim arbitrary-class width synthesis, threshold improvement, full B4, PHP
switching, Frege/PHP, NP/circuit lower bounds, P-vs-NP, or Gate A.  AND gates
are excluded by construction.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalBoundedShallowOrOnlyTightBudget

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

/-! ## Restricted nonempty OR-only formula class -/

/-- Restricted OR-only formula trees: constants and literals, closed only under
nonempty OR lists.  AND gates are excluded by construction. -/
inductive OrOnlyFormula {n : Nat} : BDFormula n → Prop where
  | tru : OrOnlyFormula BDFormula.tru
  | fls : OrOnlyFormula BDFormula.fls
  | lit (l : Literal n) : OrOnlyFormula (BDFormula.lit l)
  | or {children : List (BDFormula n)}
      (hne : children ≠ [])
      (hchildren : ∀ child, child ∈ children → OrOnlyFormula child) :
      OrOnlyFormula (BDFormula.or children)

/-! ## Structural simplicity, no empty fanins, syntactic width ≤ 1 -/

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
theorem orOnlyFormula_syntacticFormulaSimpleDNF {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
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

/-- Class members have no empty fanins. -/
theorem orOnlyFormula_noEmptyFanins {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
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

/-- Class membership implies the restricted syntactic-terminal class. -/
theorem orOnlyFormula_syntacticTerminalClass {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
    SyntacticTerminalFormulaClass F :=
  ⟨orOnlyFormula_syntacticFormulaSimpleDNF h, orOnlyFormula_noEmptyFanins h⟩

/-- Syntactic DNF width of `fls` is at most one. -/
theorem widthDNF_fls_syntactic_le_one {n : Nat} :
    widthDNF (syntacticDNF (BDFormula.fls : BDFormula n)) ≤ 1 := by
  have h : widthDNF (syntacticDNF (BDFormula.fls : BDFormula n)) = 0 := by
    simp [syntacticDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
  exact Nat.le_trans (le_of_eq h) (by decide : (0 : Nat) ≤ 1)

/-- Width of a syntactic OR-list is at most one when every disjunct has width
at most one. -/
theorem widthDNF_syntacticOrDNF_of_le_one {n : Nat} :
    ∀ children : List (BDFormula n),
      (∀ G, G ∈ children → widthDNF (syntacticDNF G) ≤ 1) →
        widthDNF (syntacticOrDNF children) ≤ 1
  | [], _ => by
      simp [syntacticOrDNF, FormulaSyntacticDNF.falseDNF, widthDNF]
  | G :: rest, h => by
      have hG : widthDNF (syntacticDNF G) ≤ 1 :=
        h G (List.mem_cons_self G rest)
      have hRest : widthDNF (syntacticOrDNF rest) ≤ 1 :=
        widthDNF_syntacticOrDNF_of_le_one rest
          (fun H hH => h H (List.mem_cons_of_mem G hH))
      simp only [syntacticOrDNF]
      exact widthDNF_orDNF_le hG hRest

/-- Class members have syntactic DNF width at most one. -/
theorem orOnlyFormula_widthDNF_syntactic_le_one {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F) :
    widthDNF (syntacticDNF F) ≤ 1 := by
  induction h with
  | tru =>
      exact widthDNF_tru_syntactic_le_one (n := n)
  | fls =>
      exact widthDNF_fls_syntactic_le_one (n := n)
  | lit l =>
      exact widthDNF_lit_syntactic_le_one l
  | or _ _ ih =>
      change widthDNF (syntacticOrDNF _) ≤ 1
      exact widthDNF_syntacticOrDNF_of_le_one _ ih

/-! ## Top-child and recursive-frontier closure -/

/-- Top children of an OR-only formula remain OR-only. -/
theorem orOnlyFormula_topChildren_closed {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F)
    {G : BDFormula n} (hG : G ∈ topChildren F) :
    OrOnlyFormula G := by
  cases h with
  | tru =>
      simp [topChildren] at hG
  | fls =>
      simp [topChildren] at hG
  | lit l =>
      simp [topChildren] at hG
  | or hne hchildren =>
      simpa [topChildren] using hchildren G hG

/-- Recursive depth-frontier members of an OR-only formula remain OR-only. -/
theorem orOnlyFormula_frontier_closed {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    OrOnlyFormula G := by
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
      exact orOnlyFormula_topChildren_closed (ih hmid) hchild

/-- Every recursive-frontier member of an OR-only formula has syntactic DNF
width at most one. -/
theorem orOnlyFormula_frontier_member_widthDNF_le_one {n : Nat}
    {F : BDFormula n} (h : OrOnlyFormula F)
    (level : Nat) {G : BDFormula n}
    (hG : G ∈ formulaDepthFrontier level F) :
    widthDNF (syntacticDNF G) ≤ 1 :=
  orOnlyFormula_widthDNF_syntactic_le_one (orOnlyFormula_frontier_closed h level hG)

/-! ## Selected GateSpec width ≤ 1 and ≤ bounded-shallow tight budget -/

/-- Intermediate (non-terminal) selected GateSpec DNF width is at most one for
OR-only formulas. -/
theorem orOnlyFormula_intermediate_gate_width_le_one {n : Nat}
    {F : BDFormula n} (hOr : OrOnlyFormula F)
    (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F)
    (level : Nat)
    (_hk : level ≤ depth F)
    (hlevel : level ≠ depth F)
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates) :
    widthDNF g.theDNF ≤ 1 := by
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
  have hwidth : widthDNF (syntacticDNF G.1) ≤ 1 :=
    orOnlyFormula_frontier_member_widthDNF_le_one hOr level G.2
  simpa [hDNF] using hwidth

/-- Every selected syntactic-terminal frontier gate of an OR-only formula of
depth at most `k` has DNF width at most the S2155 bounded-shallow tight
budget (constantly `1`). -/
theorem orOnlyFormula_width_le_boundedShallowTight {n : Nat}
    (k : Nat) {F : BDFormula n} (hOr : OrOnlyFormula F)
    (hShallow : depth F ≤ k)
    (parent : ParentKind)
    (hClass : SyntacticTerminalFormulaClass F)
    (level : Nat)
    (hk : level ≤ depth F)
    (g : GateSpec n)
    (hg : List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates) :
    widthDNF g.theDNF ≤
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level := by
  have hbudget :
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k F level = 1 :=
    boundedShallowTight_eq_one_of_depth_le k F level hShallow
  have hwidth : widthDNF g.theDNF ≤ 1 := by
    by_cases hlevel : level = depth F
    · subst hlevel
      have hg' : List.Mem g (terminalLayerMinimalLayer F parent).gates := by
        simpa [syntacticTerminalFrontierLayer] using hg
      simpa [terminalLayerWidthBudget] using
        terminalLayerMinimalLayer_width_le_budget F parent g hg'
    · exact orOnlyFormula_intermediate_gate_width_le_one hOr parent hClass
        level hk hlevel g hg
  simpa [hbudget] using hwidth

/-! ## Formula-level final-tree routing via S2155 consumers -/

/-- Single-level final-tree route for an OR-only formula of depth ≤ `k`, reusing
the S2155 bounded-shallow consumer under unchanged
`formulaClassDepthTreeBudget`. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnly
    {n : Nat} (k : Nat) (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hOr : OrOnlyFormula F)
    (hDepth : depth F ≤ d)
    (hShallow : depth F ≤ k)
    (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    BoundedShallowTightClassDepthFinalTreeAt k F S d rounds parent
      (orOnlyFormula_syntacticTerminalClass hOr) level := by
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree
      k F S d level rounds parent hDepth hSize
      (orOnlyFormula_syntacticTerminalClass hOr) hk ?hwL hn
  intro g hg
  exact orOnlyFormula_width_le_boundedShallowTight k hOr hShallow parent
    (orOnlyFormula_syntacticTerminalClass hOr) level hk g hg

/-- All-level final-tree route for an OR-only formula of depth ≤ `k`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnly
    {n : Nat} (k : Nat) (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hOr : OrOnlyFormula F)
    (hDepth : depth F ≤ d)
    (hShallow : depth F ≤ k)
    (hSize : formulaSize F ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    ∀ level, level ≤ depth F →
      BoundedShallowTightClassDepthFinalTreeAt k F S d rounds parent
        (orOnlyFormula_syntacticTerminalClass hOr) level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnly
      k F S d level rounds parent hOr hDepth hShallow hSize hk hn

/-! ## Packed-family OR-only / bounded-shallow predicates -/

/-- Every packed formula lies in the restricted OR-only class. -/
def SyntacticTerminalPackedFamilyOrOnly
    (F : SyntacticTerminalPackedFamily) : Prop :=
  ∀ d, OrOnlyFormula (syntacticTerminalPackedFamilyFormula F d)

/-- Bounded-shallow OR-only packed-family package: OR-only members of depth at
most the fixed shallow bound `k`. -/
def SyntacticTerminalPackedFamilyBoundedShallowOrOnly
    (k : Nat) (F : SyntacticTerminalPackedFamily) : Prop :=
  SyntacticTerminalPackedFamilyOrOnly F ∧
    (∀ d, depth (syntacticTerminalPackedFamilyFormula F d) ≤ k)

/-- OR-only packed families are in the syntactic-terminal class. -/
theorem SyntacticTerminalPackedFamilyClass.of_orOnly
    {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyOrOnly F) :
    SyntacticTerminalPackedFamilyClass F :=
  fun d => orOnlyFormula_syntacticTerminalClass (h d)

/-- Bounded-shallow OR-only packed families discharge the S2155 tight width
envelope at `W ≡ 1`. -/
theorem SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope.of_orOnly_boundedShallow
    (k : Nat) {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyBoundedShallowOrOnly k F) :
    SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope k F
      (fun _ => 1) :=
  SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope.of_depth_le_const_one
    k F h.2

/-- All-level gate width ≤ bounded-shallow tight budget for a bounded-shallow
OR-only packed family. -/
theorem orOnlyPackedFamily_width_le_boundedShallowTight
    (k : Nat) {F : SyntacticTerminalPackedFamily}
    (h : SyntacticTerminalPackedFamilyBoundedShallowOrOnly k F)
    (d : Nat) (parent : ParentKind)
    (level : Nat)
    (hk : level ≤ depth (syntacticTerminalPackedFamilyFormula F d))
    (g : GateSpec (syntacticTerminalPackedFamilyArity F d))
    (hg : List.Mem g (syntacticTerminalFrontierLayer
      (syntacticTerminalPackedFamilyFormula F d) level parent
      (orOnlyFormula_syntacticTerminalClass (h.1 d))).gates) :
    widthDNF g.theDNF ≤
      boundedShallowTightSyntacticTerminalFrontierWidthBudget k
        (syntacticTerminalPackedFamilyFormula F d) level :=
  orOnlyFormula_width_le_boundedShallowTight k (h.1 d) (h.2 d) parent
    (orOnlyFormula_syntacticTerminalClass (h.1 d)) level hk g hg

private theorem structuralAmbient_entry
    {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf)
    (d : Nat) :
    2 * (64 * S d) ^ roundsOf d * (64 * S d * S d) ≤
      syntacticTerminalPackedFamilyArity F d := by
  simpa [SyntacticTerminalPackedFamilyStructuralAmbientAdequate,
    syntacticTerminalClassCoarseEntryThreshold] using hAmb d

/-- Packed-family all-level final-tree route under the S2155 bounded-shallow
consumer, for generic families satisfying the OR-only class, depth ≤ `k`,
class-size envelope, depth-index bound, and structural ambient hypotheses.
The class budget remains `t(d,s)=S(d)*(s-1)`. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnlyPacked
    (k : Nat) {F : SyntacticTerminalPackedFamily} {S roundsOf : Nat → Nat}
    (d : Nat) (parent : ParentKind)
    (hOrShallow : SyntacticTerminalPackedFamilyBoundedShallowOrOnly k F)
    (hDepth : SyntacticTerminalPackedFamilyDepthBound F)
    (hSize : SyntacticTerminalPackedFamilyClassSizeEnvelope F S)
    (hAmb : SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
      BoundedShallowTightClassDepthFinalTreeAt k
        (syntacticTerminalPackedFamilyFormula F d) S d (roundsOf d) parent
        (orOnlyFormula_syntacticTerminalClass (hOrShallow.1 d)) level := by
  intro level hk
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnly
      k (syntacticTerminalPackedFamilyFormula F d) S d level (roundsOf d) parent
      (hOrShallow.1 d) (hDepth d) (hOrShallow.2 d) ?hSize hk ?hn
  · simpa [syntacticTerminalPackedFamilySizeCap] using hSize d
  · exact structuralAmbient_entry hAmb d

/-! ## S2155 nested-OR / packed-family instantiate the OR-only class -/

/-- Recursive nested-OR stays in the OR-only class when the base does. -/
theorem nestedOrFormula_orOnly {n : Nat} (base : BDFormula n)
    (hbase : OrOnlyFormula base) (r : Nat) :
    OrOnlyFormula (nestedOrFormula base r) := by
  induction r with
  | zero =>
      simpa [nestedOrFormula] using hbase
  | succ r ih =>
      refine OrOnlyFormula.or (by simp [nestedOrFormula]) ?_
      intro child hchild
      simp [nestedOrFormula] at hchild
      rcases hchild with hchild | hchild
      · subst child
        exact ih
      · subst child
        exact OrOnlyFormula.tru

/-- The S2155 nested-OR packed family is OR-only at every index. -/
theorem boundedShallowTightPackedFamily_orOnly
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyOrOnly
      (boundedShallowTightPackedFamily k roundsOf) := by
  intro d
  simpa [syntacticTerminalPackedFamilyFormula, boundedShallowTightPackedFamily,
    boundedShallowTightFormula, boundedShallowTightLit0] using
    nestedOrFormula_orOnly
      (boundedShallowTightLit0 k roundsOf d)
      (OrOnlyFormula.lit _)
      (min d k)

/-- The S2155 nested-OR packed family is a bounded-shallow OR-only package. -/
theorem boundedShallowTightPackedFamily_boundedShallowOrOnly
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyBoundedShallowOrOnly k
      (boundedShallowTightPackedFamily k roundsOf) :=
  ⟨boundedShallowTightPackedFamily_orOnly k roundsOf,
    boundedShallowTightPackedFamily_depth_le_k k roundsOf⟩

/-- Instantiating the S2155 family through the OR-only class recovers the
syntactic-terminal class already proved in S2155. -/
theorem boundedShallowTightPackedFamily_class_of_orOnly
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyClass
      (boundedShallowTightPackedFamily k roundsOf) :=
  SyntacticTerminalPackedFamilyClass.of_orOnly
    (boundedShallowTightPackedFamily_orOnly k roundsOf)

/-- Instantiating the S2155 family through the OR-only bounded-shallow package
discharges the tight width envelope at `W = 1`. -/
theorem boundedShallowTightPackedFamily_tightWidthEnvelope_one_of_orOnly
    (k : Nat) (roundsOf : Nat → Nat) :
    SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope k
      (boundedShallowTightPackedFamily k roundsOf) (fun _ => 1) :=
  SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope.of_orOnly_boundedShallow
    k (boundedShallowTightPackedFamily_boundedShallowOrOnly k roundsOf)

/-- Final-tree route for the S2155 nested-OR family recovered via the OR-only
class (no second packed numeric family). -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnly_boundedShallow
    (k : Nat) (roundsOf : Nat → Nat) (d : Nat) (parent : ParentKind) :
    ∀ level, level ≤ depth (syntacticTerminalPackedFamilyFormula
        (boundedShallowTightPackedFamily k roundsOf) d) →
      BoundedShallowTightClassDepthFinalTreeAt k
        (syntacticTerminalPackedFamilyFormula
          (boundedShallowTightPackedFamily k roundsOf) d)
        (boundedShallowTightSizeCapIndex k) d (roundsOf d) parent
        (orOnlyFormula_syntacticTerminalClass
          (boundedShallowTightPackedFamily_orOnly k roundsOf d)) level :=
  allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnlyPacked
    k d parent
    (boundedShallowTightPackedFamily_boundedShallowOrOnly k roundsOf)
    (boundedShallowTightPackedFamily_depthBound k roundsOf)
    (boundedShallowTightPackedFamily_classSizeEnvelope k roundsOf)
    (boundedShallowTightPackedFamily_structuralAmbientAdequate k roundsOf)

/-! ## Concrete fan-in-three branching OR-only witness -/

/-- Concrete branching OR-only formula on one variable: a single OR gate with
three children (literal, `tru`, `fls`).  This is not a pure nested-OR spine. -/
def branchingOrOnlyFanInThree : BDFormula 1 :=
  BDFormula.or
    [ BDFormula.lit { var := ⟨0, by decide⟩, sign := true }
    , BDFormula.tru
    , BDFormula.fls ]

/-- The fan-in-three witness is OR-only. -/
theorem branchingOrOnlyFanInThree_orOnly :
    OrOnlyFormula branchingOrOnlyFanInThree := by
  refine OrOnlyFormula.or (List.cons_ne_nil _ _) ?_
  intro child hchild
  have hmem :
      child = BDFormula.lit { var := ⟨0, by decide⟩, sign := true } ∨
        child = BDFormula.tru ∨ child = BDFormula.fls := by
    simpa [branchingOrOnlyFanInThree] using hchild
  rcases hmem with h | h | h
  · subst child
    exact OrOnlyFormula.lit _
  · subst child
    exact OrOnlyFormula.tru
  · subst child
    exact OrOnlyFormula.fls

/-- Top-child count of the fan-in-three witness is three. -/
theorem branchingOrOnlyFanInThree_topChildCount :
    topChildCount branchingOrOnlyFanInThree = 3 := by
  simp [topChildCount, topChildren, branchingOrOnlyFanInThree]

/-- The fan-in-three witness is syntactically terminal. -/
theorem branchingOrOnlyFanInThree_syntacticTerminalClass :
    SyntacticTerminalFormulaClass branchingOrOnlyFanInThree :=
  orOnlyFormula_syntacticTerminalClass branchingOrOnlyFanInThree_orOnly

/-- Syntactic DNF width of the fan-in-three witness is at most one. -/
theorem branchingOrOnlyFanInThree_widthDNF_le_one :
    widthDNF (syntacticDNF branchingOrOnlyFanInThree) ≤ 1 :=
  orOnlyFormula_widthDNF_syntactic_le_one branchingOrOnlyFanInThree_orOnly

/-- Existence package: the OR-only class admits a branching (fan-in-three)
member and recovers the S2155 nested-OR family as a bounded-shallow OR-only
package discharging the tight envelope and final-tree route. -/
theorem exists_orOnlyBoundedShallow_class_dischargesEnvelope_finalTreeRoute
    (k : Nat) (roundsOf : Nat → Nat) :
    OrOnlyFormula branchingOrOnlyFanInThree ∧
      topChildCount branchingOrOnlyFanInThree = 3 ∧
      (∃ F : SyntacticTerminalPackedFamily,
        ∃ S : Nat → Nat,
          ∃ hOr : SyntacticTerminalPackedFamilyBoundedShallowOrOnly k F,
            SyntacticTerminalPackedFamilyClass F ∧
            SyntacticTerminalPackedFamilyDepthBound F ∧
            SyntacticTerminalPackedFamilyClassSizeEnvelope F S ∧
            SyntacticTerminalPackedFamilyBoundedShallowTightWidthEnvelope k F
              (fun _ => 1) ∧
            SyntacticTerminalPackedFamilyStructuralAmbientAdequate F S roundsOf ∧
            (∀ d parent level,
              level ≤ depth (syntacticTerminalPackedFamilyFormula F d) →
                BoundedShallowTightClassDepthFinalTreeAt k
                  (syntacticTerminalPackedFamilyFormula F d) S d (roundsOf d)
                  parent
                  (orOnlyFormula_syntacticTerminalClass (hOr.1 d))
                  level)) := by
  refine ⟨branchingOrOnlyFanInThree_orOnly,
    branchingOrOnlyFanInThree_topChildCount, ?_⟩
  refine ⟨boundedShallowTightPackedFamily k roundsOf,
    boundedShallowTightSizeCapIndex k,
    boundedShallowTightPackedFamily_boundedShallowOrOnly k roundsOf,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact boundedShallowTightPackedFamily_class_of_orOnly k roundsOf
  · exact boundedShallowTightPackedFamily_depthBound k roundsOf
  · exact boundedShallowTightPackedFamily_classSizeEnvelope k roundsOf
  · exact boundedShallowTightPackedFamily_tightWidthEnvelope_one_of_orOnly
      k roundsOf
  · exact boundedShallowTightPackedFamily_structuralAmbientAdequate k roundsOf
  · intro d parent level hk
    exact
      allSyntacticTerminalFrontierLayers_geometricCollapseWithBoundedShallowTightBudget_finalTree_of_orOnly_boundedShallow
        k roundsOf d parent level hk

end FormulaRecursiveSyntacticTerminalBoundedShallowOrOnlyTightBudget
end PvNP
