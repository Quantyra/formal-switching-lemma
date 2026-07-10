import PvNP.FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportTightBudget

/-!
# Numerically-discharged supplied-width final-tree instances (S2160)

This module gives unconditional instantiations of the Gate B supplied-width
final-tree route in which the coarse ambient threshold
`2*(64*S d)^rounds*(64*S d*S d) ≤ n` is discharged NUMERICALLY (`decide` on
plain `Nat` literals) at fixed power-of-two ambients, yielding
`SuppliedWidthClassDepthFinalTreeAt` instances with zero open side
conditions.

Priority scope (stated precisely): zero-hypothesis supplied-width final-tree
instances already exist — the S2155/S2156 bounded-shallow packed families
conclude `BoundedShallowTightClassDepthFinalTreeAt`, definitionally a
`SuppliedWidthClassDepthFinalTreeAt`, for pure nested-OR spines of width 1
whose ambient arity is threshold-defined (the coarse entry product times
two), so the ambient inequality holds by construction.  What is new here is
(a) the threshold is discharged numerically at fixed ambients chosen
independently of the threshold shape, for a GIVEN formula rather than a
family with threshold-defined arity, and (b) the witness is AND-bearing with
recurrence width 2 under the class-derived width schedule
`max 1 (formulaRecurrenceWidth F)` — the first unconditional instances on
the S2157/S2158 recurrence-width route, all of whose prior consumers carry
the coarse ambient-threshold hypothesis (named `hn` on the formula-level
consumers and folded into the packed-family ambient-adequacy hypothesis).

The witnesses are two copies of one fixed AND-of-two-variable-disjoint-ORs
shape (all positive literals on variables 0,1,2,3; `formulaSize = 7`,
`depth = 2`, `formulaRecurrenceWidth = 2`):

* `largeWitness : BDFormula 4194304` (ambient `2^22`), routed at `rounds = 1`
  (two-stage certificate): threshold `2*(64*7)^1*(64*7*7) = 2809856 ≤ 2^22`;
* `hugeWitness : BDFormula 2147483648` (ambient `2^31`), routed at
  `rounds = 2` (three-stage certificate): threshold
  `2*(64*7)^2*(64*7*7) = 1258815488 ≤ 2^31`.

Class membership is the S2158 disjoint-support certification (supports
`[0,1]` and `[2,3]` are pairwise disjoint; no manual `CompatibleDNF` proof),
replayed at the large ambients with `Fin`-val reasoning in place of any
`Fin`-enumeration.  Everything else — the `formulaClassDepthTreeBudget`
class budget `t(d,s)=S(d)*(s-1)`, the geometric star schedule, the per-stage
budget 2, the class-derived width schedule `max 1 (formulaRecurrenceWidth F)`,
and the coarse ambient threshold shape — is unchanged from S2155/S2157/S2158.

Boundary: these are two single finite concrete instances, not an asymptotic
family.  The caveat recorded in the S2158 closeout (attributing the
conditionality to the S2155–S2157 increments as well) — that the concrete
S2156–S2158 small-ambient witnesses' final-tree payloads (`n = 1, 2, 4`)
were hypothesis-conditional route shapes — is closed for THESE instances only,
not in general: arbitrary formulas still owe depth/size/class/threshold
facts.  The witnesses inherit the S2158 limitation unchanged: the
disjoint-support synthesis covers variable-disjoint ANDs only, and
shared-variable ANDs still require a supplied compatibility proof.  This
is not threshold improvement, not arbitrary-class width synthesis, not full
B4, not PHP switching, not Frege/PHP, not NP/circuit lower bounds, not
Gate A, and not P-vs-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportUnconditionalInstance

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

/-! ## The AND-of-two-disjoint-ORs shape at an arbitrary ambient with room
for variables 0,1,2,3

The shape is the S2158 `andOfTwoDisjointOrs` witness verbatim, parameterized
only by the ambient bound proofs so the same certification replays at both
large ambients.  No `decide` (and no `Decidable` instance) is ever evaluated
on a statement quantifying over `Fin N` or `Assignment N`; all `Fin`
disequalities go through `Fin.val` and `omega`. -/

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

/-! ## Class membership of the shape (S2158 pattern, `Fin`-val reasoning) -/

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

/-- Support disjointness of the two ORs, by `Fin.val` arithmetic only —
never by `decide` over `Fin N` (the ambients below are far too large to
enumerate). -/
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

/-! ## The two concrete large-ambient witnesses -/

/-- Concrete AND of two variable-disjoint ORs (all positive literals on
variables 0,1,2,3) in the ambient `2^22 = 4194304`: the ambient is large
enough for the `rounds = 1` coarse threshold at class size 7 to be
discharged numerically.  Single finite concrete instance, not a family. -/
def largeWitness : BDFormula 4194304 :=
  andOrShape 4194304 (by decide) (by decide) (by decide) (by decide)

/-- The same shape in the ambient `2^31 = 2147483648`: large enough for the
`rounds = 2` coarse threshold at class size 7.  Single finite concrete
instance, not a family. -/
def hugeWitness : BDFormula 2147483648 :=
  andOrShape 2147483648 (by decide) (by decide) (by decide) (by decide)

/-- Exact size pin: `formulaSize largeWitness = 7`. -/
theorem largeWitness_formulaSize : formulaSize largeWitness = 7 :=
  andOrShape_formulaSize 4194304 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact depth pin: `depth largeWitness = 2`. -/
theorem largeWitness_depth : depth largeWitness = 2 :=
  andOrShape_depth 4194304 (by decide) (by decide) (by decide) (by decide)

/-- Exact recurrence-width pin: `formulaRecurrenceWidth largeWitness = 2`. -/
theorem largeWitness_recurrenceWidth :
    formulaRecurrenceWidth largeWitness = 2 :=
  andOrShape_recurrenceWidth 4194304 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact size pin: `formulaSize hugeWitness = 7`. -/
theorem hugeWitness_formulaSize : formulaSize hugeWitness = 7 :=
  andOrShape_formulaSize 2147483648 (by decide) (by decide) (by decide)
    (by decide)

/-- Exact depth pin: `depth hugeWitness = 2`. -/
theorem hugeWitness_depth : depth hugeWitness = 2 :=
  andOrShape_depth 2147483648 (by decide) (by decide) (by decide) (by decide)

/-- Exact recurrence-width pin: `formulaRecurrenceWidth hugeWitness = 2`. -/
theorem hugeWitness_recurrenceWidth :
    formulaRecurrenceWidth hugeWitness = 2 :=
  andOrShape_recurrenceWidth 2147483648 (by decide) (by decide) (by decide)
    (by decide)

/-- S2158 disjoint-support class membership of the large witness (supports
`[0,1]` and `[2,3]` pairwise disjoint; no manual `CompatibleDNF` proof). -/
theorem largeWitness_disjointSupportFanin :
    DisjointSupportFaninFormula largeWitness :=
  andOrShape_disjointSupportFanin 4194304 (by decide) (by decide) (by decide)
    (by decide)

/-- S2158 disjoint-support class membership of the huge witness. -/
theorem hugeWitness_disjointSupportFanin :
    DisjointSupportFaninFormula hugeWitness :=
  andOrShape_disjointSupportFanin 2147483648 (by decide) (by decide)
    (by decide) (by decide)

/-! ## Numeric discharge of the coarse ambient thresholds

Plain `Nat` inequalities on binary literals: `decide` here never touches
`Fin` or `Assignment` types. -/

/-- `rounds = 1` coarse threshold at class size 7 in ambient `2^22`:
`2*(64*7)^1*(64*7*7) = 2809856 ≤ 4194304`. -/
theorem largeAmbientThreshold :
    2 * (64 * 7) ^ 1 * (64 * 7 * 7) ≤ 4194304 := by decide

/-- `rounds = 2` coarse threshold at class size 7 in ambient `2^31`:
`2*(64*7)^2*(64*7*7) = 1258815488 ≤ 2147483648`. -/
theorem hugeAmbientThreshold :
    2 * (64 * 7) ^ 2 * (64 * 7 * 7) ≤ 2147483648 := by decide

/-! ## Unconditional final-tree instances (zero open side conditions) -/

/-- Unconditional supplied-width final-tree instance with a numerically
discharged threshold: the level-0 route payload for `largeWitness` at
`S ≡ 7`, `d = 2`, `rounds = 1` (two-stage certificate), with every
hypothesis of the S2158 route discharged concretely — class membership by
the disjoint-support certification, depth and size by the exact pins, and
the coarse ambient threshold by `decide` on `Nat` literals.  First
unconditional instance on the recurrence-width route (see the module
docstring for the precise priority scope relative to the zero-hypothesis
S2155/S2156 nested-OR instances).  Single finite instance; budgets,
thresholds, and schedules unchanged. -/
theorem largeWitness_finalTree_level0 :
    SuppliedWidthClassDepthFinalTreeAt largeWitness (fun _ => 7)
      (recurrenceWidthSchedule largeWitness) 2 1 ParentKind.and
      (disjointSupportFanin_syntacticTerminalClass
        largeWitness_disjointSupportFanin) 0 :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
    largeWitness (fun _ => 7) 2 0 1 ParentKind.and
    largeWitness_disjointSupportFanin
    (Nat.le_of_eq largeWitness_depth)
    (Nat.le_of_eq largeWitness_formulaSize)
    (Nat.zero_le _)
    largeAmbientThreshold

/-- All recursive frontier levels of `largeWitness` (levels 0, 1, 2) carry
the unconditional supplied-width final-tree payload at `rounds = 1`. -/
theorem largeWitness_finalTree_allLevels :
    ∀ level, level ≤ depth largeWitness →
      SuppliedWidthClassDepthFinalTreeAt largeWitness (fun _ => 7)
        (recurrenceWidthSchedule largeWitness) 2 1 ParentKind.and
        (disjointSupportFanin_syntacticTerminalClass
          largeWitness_disjointSupportFanin) level :=
  allSyntacticTerminalFrontierLayers_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
    largeWitness (fun _ => 7) 2 1 ParentKind.and
    largeWitness_disjointSupportFanin
    (Nat.le_of_eq largeWitness_depth)
    (Nat.le_of_eq largeWitness_formulaSize)
    largeAmbientThreshold

/-- Unconditional level-0 instance at `rounds = 2` (three-stage certificate)
in the ambient `2^31`.  Same fixed shape, same unchanged budgets and
schedules; only the numerically discharged ambient threshold grows. -/
theorem hugeWitness_finalTree_level0 :
    SuppliedWidthClassDepthFinalTreeAt hugeWitness (fun _ => 7)
      (recurrenceWidthSchedule hugeWitness) 2 2 ParentKind.and
      (disjointSupportFanin_syntacticTerminalClass
        hugeWitness_disjointSupportFanin) 0 :=
  syntacticTerminalFrontierLayer_geometricCollapseWithSuppliedWidth_finalTree_of_disjointSupportFanin
    hugeWitness (fun _ => 7) 2 0 2 ParentKind.and
    hugeWitness_disjointSupportFanin
    (Nat.le_of_eq hugeWitness_depth)
    (Nat.le_of_eq hugeWitness_formulaSize)
    (Nat.zero_le _)
    hugeAmbientThreshold

/-! ## Legible extraction of the unconditional content -/

/-- Extraction corollary of `largeWitness_finalTree_level0` exposing the
final-tree conjuncts of the payload (the stage-shape conjuncts —
`stageGateCounts`/`stageBudgets`/`stageStarCounts`/`TreeBudgetFrom` — remain
in the full instance theorem): there EXIST a two-stage refined iterated
certificate over the free restriction and a decision tree `T` in the `2^22`
ambient such that `T` is the certificate's recorded last stage (which ties
the star count `s` to the certificate rather than leaving it free), `T`
computes the certificate's final formula semantically, `dtDepth T` obeys the
unchanged class budget `t(2,s) = 7*(s-1)` at level 0, and `T` agrees with the
restricted original frontier formula on every assignment extending the
certificate's composed restriction.  No hypotheses remain. -/
theorem largeWitness_finalTree_exists :
    ∃ cert : GeneratedRefinedIteratedCertificate 4194304 (freeRestriction 4194304)
        (syntacticTerminalFrontierLayer largeWitness 0 ParentKind.and
          (disjointSupportFanin_syntacticTerminalClass
            largeWitness_disjointSupportFanin)).originalFormula
        (geometricSchedule (frontierLayerGateCount largeWitness 0)
          (4194304 / (64 * frontierLayerGateCount largeWitness 0 *
            recurrenceWidthSchedule largeWitness 0)) 2).length,
      ∃ T : DTree 4194304, ∃ s : Nat,
        cert.lastStage = some (T, frontierLayerGateCount largeWitness 0, s) ∧
        (∀ a : Assignment 4194304, dtEval a T = eval a cert.finalFormula) ∧
        dtDepth T ≤ formulaClassDepthTreeBudget (fun _ => 7) 2 0 s ∧
        (∀ a : Assignment 4194304, Agree cert.finalComposed a →
          dtEval a T = eval a (restrict cert.finalComposed
            (syntacticTerminalFrontierLayer largeWitness 0 ParentKind.and
              (disjointSupportFanin_syntacticTerminalClass
                largeWitness_disjointSupportFanin)).originalFormula)) := by
  obtain ⟨-, cert, -, -, -, -, T, s, hLast, hEval, hDepthT, hAgree⟩ :=
    largeWitness_finalTree_level0
  exact ⟨cert, T, s, hLast, hEval, hDepthT, hAgree⟩

/-! ## Non-degeneracy -/

/-- The level-0 frontier of the large witness is nonempty, so the
unconditional certificate is over a nonempty frontier layer (the payload is
not vacuous packaging of an empty gate list). -/
theorem largeWitness_frontierGateCount_pos :
    1 ≤ frontierLayerGateCount largeWitness 0 :=
  frontierLayerGateCount_nonempty_of_noEmptyFanins largeWitness 0
    (disjointSupportFanin_noEmptyFanins largeWitness_disjointSupportFanin)
    (Nat.zero_le _)

/-- The level-0 frontier of the huge witness is likewise nonempty, so the
`rounds = 2` three-stage certificate is also over a nonempty frontier. -/
theorem hugeWitness_frontierGateCount_pos :
    1 ≤ frontierLayerGateCount hugeWitness 0 :=
  frontierLayerGateCount_nonempty_of_noEmptyFanins hugeWitness 0
    (disjointSupportFanin_noEmptyFanins hugeWitness_disjointSupportFanin)
    (Nat.zero_le _)

end FormulaRecursiveSyntacticTerminalBoundedShallowDisjointSupportUnconditionalInstance
end PvNP
