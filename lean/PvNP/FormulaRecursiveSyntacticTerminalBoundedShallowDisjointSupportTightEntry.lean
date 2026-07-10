import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportUnconditionalInstance

/-!
# Frontier-local tight-entry supplied-width final-tree consumers (S2161)

This module advances Gate B after S2160 by adding TIGHT-ENTRY variants of the
S2155 supplied-width final-tree consumers: the coarse ambient obligation
`2*(64*S d)^rounds*(64*S d*S d) ≤ n` — which over-approximates both the
frontier gate count and the supplied width by the class size envelope `S d` —
is replaced by the frontier-local obligation
`2*(64*frontierLayerGateCount F level)^rounds*
  (64*frontierLayerGateCount F level*W level) ≤ n`,
which is exactly the inequality the S2155 proof actually consumes after its
internal `geometricEntryBound_of_class_envelopes` step.  The hypothesis
`W level ≤ S d` is dropped (it was used only to derive the local bound from
the coarse one); a sanity lemma (`tightEntryBound_of_coarse`) plus a
subsumption corollary re-derive the coarse route from the tight one, so the
tight consumers strictly generalize the coarse consumers without modifying
them.

Disjoint-support wrappers mirror the S2158 wrappers under the class-derived
width schedule `max 1 (formulaRecurrenceWidth F)`, taking the frontier-local
obligation in place of the coarse threshold.

The S2160 AND-of-two-variable-disjoint-ORs witness shape (positive literals
on variables 0,1,2,3; `formulaSize = 7`, `depth = 2`,
`formulaRecurrenceWidth = 2`) is re-instantiated at STRICTLY SMALLER ambients
with STRICTLY MORE rounds than the S2160 instances, with exact per-level
frontier pins (`frontierLayerGateCount` = 1, 2, 4 at levels 0, 1, 2 and
`recurrenceWidthSchedule ≡ 2`):

* `tightWitness20 : BDFormula 1048576` (`2^20 < 2^22`), level 0 at
  `rounds = 2 > 1`: local obligation `2*(64*1)^2*(64*1*2) = 2^20 ≤ 2^20`;
* `tightWitness26 : BDFormula 67108864` (`2^26 < 2^31`), level 0 at
  `rounds = 3 > 2`: local obligation `2*(64*1)^3*(64*1*2) = 2^26 ≤ 2^26`,
  plus an ALL-LEVEL instance at `rounds = 2` (per-level products
  `2^20, 2^23, 2^26` all fit in `2^26`, the last exactly);
* `tightWitness32 : BDFormula 4294967296` (`2^32`), level 0 at `rounds = 4`:
  local obligation `2*(64*1)^4*(64*1*2) = 2^32 ≤ 2^32`.

The corresponding coarse thresholds at class size 7 FAIL at every one of
these ambient/rounds pairs (pinned by explicit `¬ ≤` lemmas), so none of
these instances is reachable through the unchanged coarse consumers with
`S ≡ 7`; the coarse S2155/S2157/S2158 consumers and the S2160 instances
remain valid and untouched.

Boundary: this is a tighter ENTRY CONDITION only — it removes the coarse
over-approximation `frontierLayerGateCount F level, W level → S d` in the
ambient obligation.  It does NOT change switching-lemma constants, stage
budgets (per-stage budget 2), the geometric star schedule, the tree budget
`t(d,s)=S(d)*(s-1)`, or the `SuppliedWidthClassDepthFinalTreeAt` payload,
all of which are unchanged from S2155/S2157/S2158/S2160.  Restricted classes
only; the witnesses are single finite concrete instances, not an asymptotic
family; shared-variable ANDs still require a supplied compatibility proof.
This is not arbitrary-class width synthesis, not threshold improvement of
the switching lemma itself, not full B4, not PHP switching, not Frege/PHP,
not NP/circuit lower bounds, not Gate A, and not P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightEntry

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
open FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget
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

/-! ## Tight-entry supplied-width final-tree consumers

The S2155 consumer uses its coarse hypothesis
`2*(64*S d)^rounds*(64*S d*S d) ≤ n` only to derive the frontier-local
inequality via `geometricEntryBound_of_class_envelopes`; the tight-entry
variant takes that local inequality directly and drops `W level ≤ S d`.
Everything else — payload, budgets, schedule — is byte-for-byte the S2155
route. -/

/-- Single-level supplied-width final-tree consumer under the TIGHT entry
condition: the ambient obligation is the frontier-local inequality
`2*(64*count)^rounds*(64*count*W level) ≤ n` with
`count = frontierLayerGateCount F level`, not the coarse
`2*(64*S d)^rounds*(64*S d*S d) ≤ n` over-approximation.  The hypothesis
`W level ≤ S d` of the coarse consumer is dropped.  The payload
`SuppliedWidthClassDepthFinalTreeAt` and the class budget
`t(d,s)=S(d)*(s-1)` are unchanged. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hk : level ≤ depth F)
    (hwL : ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
      widthDNF g.theDNF ≤ W level)
    (hw1 : 1 ≤ W level)
    (hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * W level) ≤ n) :
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
  have hnLayer' : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * wBudget) ≤ n := by
    simpa [wBudget] using hnLayer
  have hreg : RegimeFrom (frontierLayerGateCount F level) wBudget
      (stars (freeRestriction n)) sched := by
    rw [stars_freeRestriction]
    exact geometric_regime_of_bound hm (by simpa [wBudget] using hw1) rounds hnLayer'
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

/-- All-level tight-entry supplied-width consumer: one frontier-local
obligation per level in place of the single coarse threshold. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    {n : Nat} (F : BDFormula n) (S W : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hClass : SyntacticTerminalFormulaClass F)
    (hwAll : ∀ level, level ≤ depth F →
      ∀ g, List.Mem g (syntacticTerminalFrontierLayer F level parent hClass).gates →
        widthDNF g.theDNF ≤ W level)
    (hwPos : ∀ level, level ≤ depth F → 1 ≤ W level)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level * W level) ≤ n) :
    ∀ level, level ≤ depth F →
      SuppliedWidthClassDepthFinalTreeAt F S W d rounds parent hClass level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
      F S W d level rounds parent hDepth hSize hClass hk (hwAll level hk)
      (hwPos level hk) (hnAll level hk)

/-! ## Sanity: the tight entry condition subsumes the coarse one -/

/-- The coarse ambient threshold implies the frontier-local tight entry
condition (this is exactly the derivation the S2155 consumer performs
internally), so the tight-entry consumers strictly generalize the coarse
consumers.  The coarse consumers themselves are untouched. -/
theorem tightEntryBound_of_coarse {n : Nat} (F : BDFormula n)
    (S W : Nat → Nat) (d level rounds : Nat)
    (hSize : formulaSize F ≤ S d)
    (hwClass : W level ≤ S d)
    (hn : 2 * (64 * S d) ^ rounds * (64 * S d * S d) ≤ n) :
    2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level * W level) ≤ n :=
  geometricEntryBound_of_class_envelopes
    (frontierLayerGateCount_le_classSize F S d level hSize) hwClass hn

/-- Subsumption corollary: the full coarse S2155 consumer statement is
re-derived from the tight-entry consumer plus `tightEntryBound_of_coarse`.
This documents strict generalization at the consumer level without touching
the original S2155 theorem. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_coarse_via_tightEntry
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
    SuppliedWidthClassDepthFinalTreeAt F S W d rounds parent hClass level :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
    F S W d level rounds parent hDepth hSize hClass hk hwL hw1
    (tightEntryBound_of_coarse F S W d level rounds hSize hwClass hn)

/-! ## Disjoint-support tight-entry wrappers (S2158 pattern) -/

/-- Single-level tight-entry route for a disjoint-support formula under the
class-derived width schedule `max 1 (formulaRecurrenceWidth F)`: gate-width
and positivity facts are discharged from class membership exactly as in the
S2158 wrapper; only the ambient obligation is the frontier-local tight
inequality. -/
theorem syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d level rounds : Nat) (parent : ParentKind)
    (hDS : DisjointSupportFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hk : level ≤ depth F)
    (hnLayer : 2 * (64 * frontierLayerGateCount F level) ^ rounds *
      (64 * frontierLayerGateCount F level *
        recurrenceWidthSchedule F level) ≤ n) :
    SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F) d rounds
      parent (disjointSupportFanin_syntacticTerminalClass hDS) level := by
  refine
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry
      F S (recurrenceWidthSchedule F) d level rounds parent hDepth hSize
      (disjointSupportFanin_syntacticTerminalClass hDS) hk ?_
      (recurrenceWidthSchedule_pos F level) hnLayer
  intro g hg
  exact disjointSupportFanin_width_le_recurrenceWidthSchedule hDS parent
    (disjointSupportFanin_syntacticTerminalClass hDS) level hk g hg

/-- All-level tight-entry route for a disjoint-support formula: one
frontier-local obligation per level. -/
theorem allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
    {n : Nat} (F : BDFormula n) (S : Nat → Nat)
    (d rounds : Nat) (parent : ParentKind)
    (hDS : DisjointSupportFaninFormula F)
    (hDepth : depth F ≤ d)
    (hSize : formulaSize F ≤ S d)
    (hnAll : ∀ level, level ≤ depth F →
      2 * (64 * frontierLayerGateCount F level) ^ rounds *
        (64 * frontierLayerGateCount F level *
          recurrenceWidthSchedule F level) ≤ n) :
    ∀ level, level ≤ depth F →
      SuppliedWidthClassDepthFinalTreeAt F S (recurrenceWidthSchedule F) d
        rounds parent (disjointSupportFanin_syntacticTerminalClass hDS)
        level := by
  intro level hk
  exact
    syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
      F S d level rounds parent hDS hDepth hSize hk (hnAll level hk)

/-! ## The S2160 AND-of-two-disjoint-ORs shape, re-created locally

The S2160 helpers are private to that module, so the parametric construction
is re-created here verbatim (same `Fin.val` + `omega` discipline: no `decide`
ever touches a statement quantifying over `Fin N` or `Assignment N`; `decide`
is used only on plain `Nat` comparisons). -/

private def orPairLeft (N : Nat) (h0 : 0 < N) (h1 : 1 < N) : BDFormula N :=
  BDFormula.or
    [ BDFormula.lit { var := ⟨0, h0⟩, sign := true }
    , BDFormula.lit { var := ⟨1, h1⟩, sign := true } ]

private def orPairRight (N : Nat) (h2 : 2 < N) (h3 : 3 < N) : BDFormula N :=
  BDFormula.or
    [ BDFormula.lit { var := ⟨2, h2⟩, sign := true }
    , BDFormula.lit { var := ⟨3, h3⟩, sign := true } ]

private def andOrShape (N : Nat) (h0 : 0 < N) (h1 : 1 < N) (h2 : 2 < N)
    (h3 : 3 < N) : BDFormula N :=
  BDFormula.and [orPairLeft N h0 h1, orPairRight N h2 h3]

private theorem andOrShape_eq (N : Nat) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) :
    andOrShape N h0 h1 h2 h3 =
      BDFormula.and [orPairLeft N h0 h1, orPairRight N h2 h3] := rfl

private theorem orPairLeft_disjointSupportFanin (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) :
    DisjointSupportFaninFormula (orPairLeft N h0 h1) := by
  refine DisjointSupportFaninFormula.or (List.cons_ne_nil _ _) ?_
  intro child hchild
  have hmem : child = BDFormula.lit { var := ⟨0, h0⟩, sign := true } ∨
      child = BDFormula.lit { var := ⟨1, h1⟩, sign := true } := by
    simpa [orPairLeft] using hchild
  rcases hmem with h | h
  · subst child; exact DisjointSupportFaninFormula.lit _
  · subst child; exact DisjointSupportFaninFormula.lit _

private theorem orPairRight_disjointSupportFanin (N : Nat) (h2 : 2 < N)
    (h3 : 3 < N) :
    DisjointSupportFaninFormula (orPairRight N h2 h3) := by
  refine DisjointSupportFaninFormula.or (List.cons_ne_nil _ _) ?_
  intro child hchild
  have hmem : child = BDFormula.lit { var := ⟨2, h2⟩, sign := true } ∨
      child = BDFormula.lit { var := ⟨3, h3⟩, sign := true } := by
    simpa [orPairRight] using hchild
  rcases hmem with h | h
  · subst child; exact DisjointSupportFaninFormula.lit _
  · subst child; exact DisjointSupportFaninFormula.lit _

private theorem formulaVars_orPairLeft (N : Nat) (h0 : 0 < N) (h1 : 1 < N) :
    formulaVars (orPairLeft N h0 h1) = [⟨0, h0⟩, ⟨1, h1⟩] := by
  simp [orPairLeft, formulaVars_or, formulaVars_lit]

private theorem formulaVars_orPairRight (N : Nat) (h2 : 2 < N) (h3 : 3 < N) :
    formulaVars (orPairRight N h2 h3) = [⟨2, h2⟩, ⟨3, h3⟩] := by
  simp [orPairRight, formulaVars_or, formulaVars_lit]

private theorem orPairLeft_orPairRight_disjoint (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) (h2 : 2 < N) (h3 : 3 < N) :
    ∀ v ∈ formulaVars (orPairLeft N h0 h1),
      v ∉ formulaVars (orPairRight N h2 h3) := by
  intro v hv hv'
  rw [formulaVars_orPairLeft] at hv
  rw [formulaVars_orPairRight] at hv'
  have h01 : v = (⟨0, h0⟩ : Fin N) ∨ v = (⟨1, h1⟩ : Fin N) := by
    simpa using hv
  have h23 : v = (⟨2, h2⟩ : Fin N) ∨ v = (⟨3, h3⟩ : Fin N) := by
    simpa using hv'
  have hval01 : v.val = 0 ∨ v.val = 1 := by
    rcases h01 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hval23 : v.val = 2 ∨ v.val = 3 := by
    rcases h23 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hval01 with h | h <;> rcases hval23 with h' | h' <;> omega

private theorem andOrShape_disjointSupportFanin (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) (h2 : 2 < N) (h3 : 3 < N) :
    DisjointSupportFaninFormula (andOrShape N h0 h1 h2 h3) := by
  rw [andOrShape_eq]
  refine DisjointSupportFaninFormula.and (List.cons_ne_nil _ _) ?_ ?_
  · intro child hchild
    have hmem : child = orPairLeft N h0 h1 ∨ child = orPairRight N h2 h3 := by
      simpa using hchild
    rcases hmem with h | h
    · subst child
      exact orPairLeft_disjointSupportFanin N h0 h1
    · subst child
      exact orPairRight_disjointSupportFanin N h2 h3
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
    · intro G hG
      have hG' : G = orPairRight N h2 h3 := by simpa using hG
      subst hG'
      exact orPairLeft_orPairRight_disjoint N h0 h1 h2 h3
    · intro G hG
      cases hG

/-! ## Structural pins of the shape (size 7, depth 2, recurrence width 2) -/

private theorem depth_and_pair {n : Nat} (g0 g1 : BDFormula n) :
    depth (BDFormula.and [g0, g1]) = 1 + max (depth g0) (depth g1) := by
  rw [show depth (BDFormula.and [g0, g1])
        = 1 + ([g0, g1].attach.map
                (fun f => depth f.1)).foldr Nat.max 0 from by rw [depth]]
  rw [List.attach_map_val [g0, g1] (fun f => depth f)]
  simp [Nat.max_comm]

private theorem orPairLeft_formulaSize (N : Nat) (h0 : 0 < N) (h1 : 1 < N) :
    formulaSize (orPairLeft N h0 h1) = 3 := by
  simp [orPairLeft, formulaSize_or, formulaSize_lit]

private theorem orPairRight_formulaSize (N : Nat) (h2 : 2 < N) (h3 : 3 < N) :
    formulaSize (orPairRight N h2 h3) = 3 := by
  simp [orPairRight, formulaSize_or, formulaSize_lit]

private theorem andOrShape_formulaSize (N : Nat) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) :
    formulaSize (andOrShape N h0 h1 h2 h3) = 7 := by
  simp [andOrShape, formulaSize_and, orPairLeft_formulaSize,
    orPairRight_formulaSize]

private theorem orPairLeft_depth (N : Nat) (h0 : 0 < N) (h1 : 1 < N) :
    depth (orPairLeft N h0 h1) = 1 := by
  simp [orPairLeft, depth_or_pair, depth_lit]

private theorem orPairRight_depth (N : Nat) (h2 : 2 < N) (h3 : 3 < N) :
    depth (orPairRight N h2 h3) = 1 := by
  simp [orPairRight, depth_or_pair, depth_lit]

private theorem andOrShape_depth (N : Nat) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) :
    depth (andOrShape N h0 h1 h2 h3) = 2 := by
  simp [andOrShape, depth_and_pair, orPairLeft_depth, orPairRight_depth]

private theorem orPairLeft_recurrenceWidth (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) :
    formulaRecurrenceWidth (orPairLeft N h0 h1) = 1 := by
  simp [orPairLeft, formulaRecurrenceWidth_or, formulaRecurrenceWidth_lit,
    Nat.max_zero, Nat.max_self]

private theorem orPairRight_recurrenceWidth (N : Nat) (h2 : 2 < N)
    (h3 : 3 < N) :
    formulaRecurrenceWidth (orPairRight N h2 h3) = 1 := by
  simp [orPairRight, formulaRecurrenceWidth_or, formulaRecurrenceWidth_lit,
    Nat.max_zero, Nat.max_self]

private theorem andOrShape_recurrenceWidth (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) (h2 : 2 < N) (h3 : 3 < N) :
    formulaRecurrenceWidth (andOrShape N h0 h1 h2 h3) = 2 := by
  simp [andOrShape, formulaRecurrenceWidth_and, orPairLeft_recurrenceWidth,
    orPairRight_recurrenceWidth]

/-! ## Exact per-level frontier pins of the shape

The shape has frontier gate counts 1, 2, 4 at levels 0, 1, 2 and constant
class-derived width schedule `max 1 2 = 2`.  Levels 1 and 2 are computed
through `frontierLayerGateCount_eq_formulaDepthFrontier_length`; the raw
frontier lists are concrete, so the lengths reduce definitionally. -/

private theorem andOrShape_frontierGateCount_one (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) (h2 : 2 < N) (h3 : 3 < N) :
    frontierLayerGateCount (andOrShape N h0 h1 h2 h3) 1 = 2 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

private theorem andOrShape_frontierGateCount_two (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) (h2 : 2 < N) (h3 : 3 < N) :
    frontierLayerGateCount (andOrShape N h0 h1 h2 h3) 2 = 4 := by
  rw [frontierLayerGateCount_eq_formulaDepthFrontier_length]
  rfl

private theorem andOrShape_recurrenceWidthSchedule (N : Nat) (h0 : 0 < N)
    (h1 : 1 < N) (h2 : 2 < N) (h3 : 3 < N) (level : Nat) :
    recurrenceWidthSchedule (andOrShape N h0 h1 h2 h3) level = 2 := by
  show Nat.max 1 (formulaRecurrenceWidth (andOrShape N h0 h1 h2 h3)) = 2
  rw [andOrShape_recurrenceWidth N h0 h1 h2 h3]
  decide

/-! ## The three tight-entry witnesses (strictly smaller ambients, strictly
more rounds than S2160) -/

/-- The S2160 AND-of-two-variable-disjoint-ORs shape in the ambient
`2^20 = 1048576`: strictly smaller than the S2160 `rounds = 1` ambient
`2^22`, reached here at `rounds = 2` through the tight entry condition.
Single finite concrete instance, not a family. -/
def tightWitness20 : BDFormula 1048576 :=
  andOrShape 1048576 (by decide) (by decide) (by decide) (by decide)

/-- The same shape in the ambient `2^26 = 67108864`: strictly smaller than
the S2160 `rounds = 2` ambient `2^31`, reached here at `rounds = 3`.
Single finite concrete instance, not a family. -/
def tightWitness26 : BDFormula 67108864 :=
  andOrShape 67108864 (by decide) (by decide) (by decide) (by decide)

/-- The same shape in the ambient `2^32 = 4294967296`, reached at
`rounds = 4` (a five-stage certificate).  Single finite concrete instance,
not a family. -/
def tightWitness32 : BDFormula 4294967296 :=
  andOrShape 4294967296 (by decide) (by decide) (by decide) (by decide)

/-! ### Structural and frontier pins: `tightWitness20` -/

/-- Exact size pin: `formulaSize tightWitness20 = 7`. -/
theorem tightWitness20_formulaSize : formulaSize tightWitness20 = 7 :=
  andOrShape_formulaSize 1048576 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact depth pin: `depth tightWitness20 = 2`. -/
theorem tightWitness20_depth : depth tightWitness20 = 2 :=
  andOrShape_depth 1048576 (by decide) (by decide) (by decide) (by decide)

/-- Exact recurrence-width pin: `formulaRecurrenceWidth tightWitness20 = 2`. -/
theorem tightWitness20_recurrenceWidth :
    formulaRecurrenceWidth tightWitness20 = 2 :=
  andOrShape_recurrenceWidth 1048576 (by decide) (by decide) (by decide)
    (by decide)

/-- S2158 disjoint-support class membership of `tightWitness20` (supports
`[0,1]` and `[2,3]` pairwise disjoint; no manual `CompatibleDNF` proof). -/
theorem tightWitness20_disjointSupportFanin :
    DisjointSupportFaninFormula tightWitness20 :=
  andOrShape_disjointSupportFanin 1048576 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact level-0 frontier pin: the zero-th frontier is the root alone. -/
theorem tightWitness20_frontierGateCount_zero :
    frontierLayerGateCount tightWitness20 0 = 1 :=
  frontierLayerGateCount_zero tightWitness20

/-- Exact level-1 frontier pin: the two OR children. -/
theorem tightWitness20_frontierGateCount_one :
    frontierLayerGateCount tightWitness20 1 = 2 :=
  andOrShape_frontierGateCount_one 1048576 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact level-2 frontier pin: the four literals. -/
theorem tightWitness20_frontierGateCount_two :
    frontierLayerGateCount tightWitness20 2 = 4 :=
  andOrShape_frontierGateCount_two 1048576 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact width-schedule pin at every level (in particular levels 0, 1, 2):
`recurrenceWidthSchedule tightWitness20 level = max 1 2 = 2`. -/
theorem tightWitness20_recurrenceWidthSchedule (level : Nat) :
    recurrenceWidthSchedule tightWitness20 level = 2 :=
  andOrShape_recurrenceWidthSchedule 1048576 (by decide) (by decide)
    (by decide) (by decide) level

/-! ### Structural and frontier pins: `tightWitness26` -/

/-- Exact size pin: `formulaSize tightWitness26 = 7`. -/
theorem tightWitness26_formulaSize : formulaSize tightWitness26 = 7 :=
  andOrShape_formulaSize 67108864 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact depth pin: `depth tightWitness26 = 2`. -/
theorem tightWitness26_depth : depth tightWitness26 = 2 :=
  andOrShape_depth 67108864 (by decide) (by decide) (by decide) (by decide)

/-- Exact recurrence-width pin: `formulaRecurrenceWidth tightWitness26 = 2`. -/
theorem tightWitness26_recurrenceWidth :
    formulaRecurrenceWidth tightWitness26 = 2 :=
  andOrShape_recurrenceWidth 67108864 (by decide) (by decide) (by decide)
    (by decide)

/-- S2158 disjoint-support class membership of `tightWitness26`. -/
theorem tightWitness26_disjointSupportFanin :
    DisjointSupportFaninFormula tightWitness26 :=
  andOrShape_disjointSupportFanin 67108864 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact level-0 frontier pin. -/
theorem tightWitness26_frontierGateCount_zero :
    frontierLayerGateCount tightWitness26 0 = 1 :=
  frontierLayerGateCount_zero tightWitness26

/-- Exact level-1 frontier pin. -/
theorem tightWitness26_frontierGateCount_one :
    frontierLayerGateCount tightWitness26 1 = 2 :=
  andOrShape_frontierGateCount_one 67108864 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact level-2 frontier pin. -/
theorem tightWitness26_frontierGateCount_two :
    frontierLayerGateCount tightWitness26 2 = 4 :=
  andOrShape_frontierGateCount_two 67108864 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact width-schedule pin at every level (in particular levels 0, 1, 2). -/
theorem tightWitness26_recurrenceWidthSchedule (level : Nat) :
    recurrenceWidthSchedule tightWitness26 level = 2 :=
  andOrShape_recurrenceWidthSchedule 67108864 (by decide) (by decide)
    (by decide) (by decide) level

/-! ### Structural and frontier pins: `tightWitness32` -/

/-- Exact size pin: `formulaSize tightWitness32 = 7`. -/
theorem tightWitness32_formulaSize : formulaSize tightWitness32 = 7 :=
  andOrShape_formulaSize 4294967296 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact depth pin: `depth tightWitness32 = 2`. -/
theorem tightWitness32_depth : depth tightWitness32 = 2 :=
  andOrShape_depth 4294967296 (by decide) (by decide) (by decide) (by decide)

/-- Exact recurrence-width pin: `formulaRecurrenceWidth tightWitness32 = 2`. -/
theorem tightWitness32_recurrenceWidth :
    formulaRecurrenceWidth tightWitness32 = 2 :=
  andOrShape_recurrenceWidth 4294967296 (by decide) (by decide) (by decide)
    (by decide)

/-- S2158 disjoint-support class membership of `tightWitness32`. -/
theorem tightWitness32_disjointSupportFanin :
    DisjointSupportFaninFormula tightWitness32 :=
  andOrShape_disjointSupportFanin 4294967296 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact level-0 frontier pin. -/
theorem tightWitness32_frontierGateCount_zero :
    frontierLayerGateCount tightWitness32 0 = 1 :=
  frontierLayerGateCount_zero tightWitness32

/-- Exact level-1 frontier pin. -/
theorem tightWitness32_frontierGateCount_one :
    frontierLayerGateCount tightWitness32 1 = 2 :=
  andOrShape_frontierGateCount_one 4294967296 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact level-2 frontier pin. -/
theorem tightWitness32_frontierGateCount_two :
    frontierLayerGateCount tightWitness32 2 = 4 :=
  andOrShape_frontierGateCount_two 4294967296 (by decide) (by decide)
    (by decide) (by decide)

/-- Exact width-schedule pin at every level (in particular levels 0, 1, 2). -/
theorem tightWitness32_recurrenceWidthSchedule (level : Nat) :
    recurrenceWidthSchedule tightWitness32 level = 2 :=
  andOrShape_recurrenceWidthSchedule 4294967296 (by decide) (by decide)
    (by decide) (by decide) level

/-! ## Numeric discharge of the tight entry conditions

Plain `Nat` (in)equalities on binary literals; `decide` never touches `Fin`
or `Assignment` types.  All three level-0 products meet their ambient with
EXACT equality. -/

/-- Exact level-0 entry product at `rounds = 2` and width 2:
`2*(64*1)^2*(64*1*2) = 1048576 = 2^20`. -/
theorem tightWitness20_entryProduct_eq :
    2 * (64 * 1) ^ 2 * (64 * 1 * 2) = 1048576 := by decide

/-- Exact level-0 entry product at `rounds = 3` and width 2:
`2*(64*1)^3*(64*1*2) = 67108864 = 2^26`. -/
theorem tightWitness26_entryProduct_eq :
    2 * (64 * 1) ^ 3 * (64 * 1 * 2) = 67108864 := by decide

/-- Exact level-0 entry product at `rounds = 4` and width 2:
`2*(64*1)^4*(64*1*2) = 4294967296 = 2^32`. -/
theorem tightWitness32_entryProduct_eq :
    2 * (64 * 1) ^ 4 * (64 * 1 * 2) = 4294967296 := by decide

/-- Tight entry condition for `tightWitness20` at level 0, `rounds = 2`:
the local product is exactly the ambient `2^20`. -/
theorem tightWitness20_tightEntryThreshold_level0 :
    2 * (64 * frontierLayerGateCount tightWitness20 0) ^ 2 *
      (64 * frontierLayerGateCount tightWitness20 0 *
        recurrenceWidthSchedule tightWitness20 0) ≤ 1048576 := by
  rw [tightWitness20_frontierGateCount_zero,
    tightWitness20_recurrenceWidthSchedule 0]
  decide

/-- Tight entry condition for `tightWitness26` at level 0, `rounds = 3`:
the local product is exactly the ambient `2^26`. -/
theorem tightWitness26_tightEntryThreshold_level0 :
    2 * (64 * frontierLayerGateCount tightWitness26 0) ^ 3 *
      (64 * frontierLayerGateCount tightWitness26 0 *
        recurrenceWidthSchedule tightWitness26 0) ≤ 67108864 := by
  rw [tightWitness26_frontierGateCount_zero,
    tightWitness26_recurrenceWidthSchedule 0]
  decide

/-- Tight entry condition for `tightWitness32` at level 0, `rounds = 4`:
the local product is exactly the ambient `2^32`. -/
theorem tightWitness32_tightEntryThreshold_level0 :
    2 * (64 * frontierLayerGateCount tightWitness32 0) ^ 4 *
      (64 * frontierLayerGateCount tightWitness32 0 *
        recurrenceWidthSchedule tightWitness32 0) ≤ 4294967296 := by
  rw [tightWitness32_frontierGateCount_zero,
    tightWitness32_recurrenceWidthSchedule 0]
  decide

/-! ## Zero-hypothesis tight-entry final-tree instances -/

/-- Zero-hypothesis tight-entry instance at ambient `2^20`, `rounds = 2`
(three-stage certificate), level 0: strictly smaller ambient than the S2160
`largeWitness` (`2^22`) with strictly more rounds (`2 > 1`).  The coarse
threshold at class size 7 fails at this ambient/rounds pair
(`coarseEntry_fails_at_ambient20_rounds2`), so this instance is not
reachable through the unchanged coarse consumers with `S ≡ 7`.  Payload,
budgets, and schedule are unchanged from S2155/S2158/S2160. -/
theorem tightWitness20_finalTree_level0 :
    SuppliedWidthClassDepthFinalTreeAt tightWitness20 (fun _ => 7)
      (recurrenceWidthSchedule tightWitness20) 2 2 ParentKind.and
      (disjointSupportFanin_syntacticTerminalClass
        tightWitness20_disjointSupportFanin) 0 :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
    tightWitness20 (fun _ => 7) 2 0 2 ParentKind.and
    tightWitness20_disjointSupportFanin
    (Nat.le_of_eq tightWitness20_depth)
    (Nat.le_of_eq tightWitness20_formulaSize)
    (Nat.zero_le _)
    tightWitness20_tightEntryThreshold_level0

/-- Zero-hypothesis tight-entry instance at ambient `2^26`, `rounds = 3`
(four-stage certificate), level 0: strictly smaller ambient than the S2160
`hugeWitness` (`2^31`) with strictly more rounds (`3 > 2`).  The coarse
threshold at class size 7 fails at this ambient/rounds pair
(`coarseEntry_fails_at_ambient26_rounds3`). -/
theorem tightWitness26_finalTree_level0 :
    SuppliedWidthClassDepthFinalTreeAt tightWitness26 (fun _ => 7)
      (recurrenceWidthSchedule tightWitness26) 2 3 ParentKind.and
      (disjointSupportFanin_syntacticTerminalClass
        tightWitness26_disjointSupportFanin) 0 :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
    tightWitness26 (fun _ => 7) 2 0 3 ParentKind.and
    tightWitness26_disjointSupportFanin
    (Nat.le_of_eq tightWitness26_depth)
    (Nat.le_of_eq tightWitness26_formulaSize)
    (Nat.zero_le _)
    tightWitness26_tightEntryThreshold_level0

/-- Zero-hypothesis tight-entry instance at ambient `2^32`, `rounds = 4`
(five-stage certificate), level 0.  The coarse threshold at class size 7
fails at this ambient/rounds pair
(`coarseEntry_fails_at_ambient32_rounds4`). -/
theorem tightWitness32_finalTree_level0 :
    SuppliedWidthClassDepthFinalTreeAt tightWitness32 (fun _ => 7)
      (recurrenceWidthSchedule tightWitness32) 2 4 ParentKind.and
      (disjointSupportFanin_syntacticTerminalClass
        tightWitness32_disjointSupportFanin) 0 :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
    tightWitness32 (fun _ => 7) 2 0 4 ParentKind.and
    tightWitness32_disjointSupportFanin
    (Nat.le_of_eq tightWitness32_depth)
    (Nat.le_of_eq tightWitness32_formulaSize)
    (Nat.zero_le _)
    tightWitness32_tightEntryThreshold_level0

/-- Zero-hypothesis ALL-LEVEL tight-entry instance for `tightWitness26` at
`rounds = 2`: the per-level products with counts 1, 2, 4 and width 2 are
`2^20`, `2^23`, and `2^26` at levels 0, 1, 2, all fitting the `2^26` ambient
(the last exactly).  The coarse `rounds = 2` threshold at class size 7 fails
at this ambient (`coarseEntry_fails_at_ambient26_rounds2`), so even this
all-level instance is out of reach of the coarse consumers with `S ≡ 7`. -/
theorem tightWitness26_finalTree_allLevels_rounds2 :
    ∀ level, level ≤ depth tightWitness26 →
      SuppliedWidthClassDepthFinalTreeAt tightWitness26 (fun _ => 7)
        (recurrenceWidthSchedule tightWitness26) 2 2 ParentKind.and
        (disjointSupportFanin_syntacticTerminalClass
          tightWitness26_disjointSupportFanin) level := by
  refine
    allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_tightEntry_of_disjointSupportFanin
      tightWitness26 (fun _ => 7) 2 2 ParentKind.and
      tightWitness26_disjointSupportFanin
      (Nat.le_of_eq tightWitness26_depth)
      (Nat.le_of_eq tightWitness26_formulaSize)
      ?_
  intro level hlevel
  have hd : depth tightWitness26 = 2 := tightWitness26_depth
  have hcase : level = 0 ∨ level = 1 ∨ level = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · rw [tightWitness26_frontierGateCount_zero,
      tightWitness26_recurrenceWidthSchedule 0]
    decide
  · rw [tightWitness26_frontierGateCount_one,
      tightWitness26_recurrenceWidthSchedule 1]
    decide
  · rw [tightWitness26_frontierGateCount_two,
      tightWitness26_recurrenceWidthSchedule 2]
    decide

/-! ## Strict domination of the coarse entry route at these instances

The coarse ambient threshold at the class size envelope `S ≡ 7` FAILS at
every ambient/rounds pair instantiated above, so none of the above instances
is derivable from the unchanged coarse consumers with this envelope; and the
new ambients are strictly smaller than the S2160 ambients while the round
counts are strictly larger. -/

/-- The coarse `rounds = 2` threshold at class size 7 fails in ambient
`2^20`: `2*(64*7)^2*(64*7*7) = 1258815488 > 1048576`. -/
theorem coarseEntry_fails_at_ambient20_rounds2 :
    ¬ (2 * (64 * 7) ^ 2 * (64 * 7 * 7) ≤ 1048576) := by decide

/-- The coarse `rounds = 2` threshold at class size 7 fails in ambient
`2^26`: `2*(64*7)^2*(64*7*7) = 1258815488 > 67108864`. -/
theorem coarseEntry_fails_at_ambient26_rounds2 :
    ¬ (2 * (64 * 7) ^ 2 * (64 * 7 * 7) ≤ 67108864) := by decide

/-- The coarse `rounds = 3` threshold at class size 7 fails in ambient
`2^26`: `2*(64*7)^3*(64*7*7) = 563949338624 > 67108864`. -/
theorem coarseEntry_fails_at_ambient26_rounds3 :
    ¬ (2 * (64 * 7) ^ 3 * (64 * 7 * 7) ≤ 67108864) := by decide

/-- The coarse `rounds = 4` threshold at class size 7 fails in ambient
`2^32`: `2*(64*7)^4*(64*7*7) = 252649303703552 > 4294967296`. -/
theorem coarseEntry_fails_at_ambient32_rounds4 :
    ¬ (2 * (64 * 7) ^ 4 * (64 * 7 * 7) ≤ 4294967296) := by decide

/-- Ambient domination pin: the tight-entry ambients are strictly smaller
than the corresponding S2160 coarse ambients (`2^20 < 2^22` with rounds
`2 > 1`, and `2^26 < 2^31` with rounds `3 > 2`). -/
theorem tightWitness_ambient_domination :
    1048576 < 4194304 ∧ 67108864 < 2147483648 ∧ 1 < 2 ∧ 2 < 3 := by decide

end FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightEntry
end PvNP
