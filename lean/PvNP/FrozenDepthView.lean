import PvNP.MixedFormulaFamilyCollapse

set_option linter.dupNamespace false

/-!
# Frozen depth views: the structural B4 interface

The formula-family modules now synthesize bottom-layer `GateSpec.dnf` and
`GateSpec.cnf` children from raw syntax. Full frozen-form B4 still needs a
genuinely structural input: a depth-`d` view of a real formula, not just a
bottom-layer class whose syntax already exposes the layer.

This module introduces that explicit interface and proves the first consumer
theorem. A `FrozenDepthView n F d` packages a real `BDFormula n`, an explicit
start layer, an equality saying the layer is the formula, and a depth bound
`depth F <= d`. From such a view, the existing ratio-form geometric schedule
theorem yields a generated refined certificate plus an actual last-stage
decision tree bounded by the global budget

  `frozenGlobalTreeBudget V _ s = V.gateCount * (s - 1)`.

## HONEST SCOPE STATEMENT (read this)

* This is an interface/consumer theorem for EXPLICIT depth views. It does not
  automatically decompose arbitrary `BDFormula` or AC0 syntax into a
  `FrozenDepthView`.
* The bottom-layer constructor `mixedBottomFrozenDepthView` shows that the
  already-proved mixed raw DNF/CNF class inhabits the new interface at its own
  computed depth. It is not a decomposition theorem for deeper formulas.
* The global `t` theorem here is for the supplied view's generated route:
  `t(d,s) = gateCount * (s - 1)`. It does not synthesize a sharper or
  formula-independent product-bound family for arbitrary formulas.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma (Gate A rung 4 remains open), NOT an
  NP/circuit lower bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FrozenDepthView

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open FrozenProductSchedule
open FrozenProductScheduleRatio
open MixedFormulaFamilyCollapse
open SwitchingEncodeConstruct
open SwitchingLemmaStatement

/-- An explicit frozen depth view of a real bounded-depth formula.

The structure records the currently available start layer and the fact that it
is exactly the formula being collapsed. The depth field is deliberately a
bound, because this module consumes supplied views; it does not yet derive
them from arbitrary formula syntax. -/
structure FrozenDepthView (n : Nat) (F : BDFormula n) (d : Nat) where
  layer : MinimalLayeredFormula n
  originalFormula_eq : layer.originalFormula = F
  depth_bound : depth F <= d

namespace FrozenDepthView

/-- The bottom-layer gate count of a frozen view. -/
def gateCount {n d : Nat} {F : BDFormula n} (V : FrozenDepthView n F d) : Nat :=
  V.layer.gates.length

end FrozenDepthView

/-- The explicit global tree-budget function carried by the current frozen
depth-view consumer route. -/
def frozenGlobalTreeBudget {n d : Nat} {F : BDFormula n}
    (V : FrozenDepthView n F d) (_depth s : Nat) : Nat :=
  V.gateCount * (s - 1)

/-- The geometric schedule satisfies the explicit global budget
`t(d,s) = gateCount * (s - 1)` for every stage, since every geometric stage has
budget `s = 2`. -/
theorem geometricSchedule_frozenGlobalTreeBudget {n d : Nat} {F : BDFormula n}
    (V : FrozenDepthView n F d) (q : Nat) :
    forall (k l depth : Nat),
      TreeBudgetFrom (frozenGlobalTreeBudget V) V.gateCount depth
        (geometricSchedule q l k)
  | 0, _, _ => trivial
  | k + 1, l, depth => by
      refine ⟨?_, geometricSchedule_frozenGlobalTreeBudget V q k
        (l / (64 * q)) (depth - 1)⟩
      simp [StageTreeBudget, frozenGlobalTreeBudget, stageS]

/-- If every recorded stage gate count is the same value `m`, then the `m`
stored in the final combined decision tree is that same value. -/
theorem lastStage_gateCount_of_stageGateCounts_replicate {n : Nat}
    {base : Restriction n} {F : BDFormula n} :
    forall {d : Nat} (cert : GeneratedRefinedIteratedCertificate n base F d)
      {m : Nat},
      cert.stageGateCounts = List.replicate d m ->
      forall T : DTree n, forall m' s : Nat,
        cert.lastStage = some (T, m', s) -> m' = m
  | 0, .done _base _F, _m, _hgc, T, m', s, hlast => by
      simp [GeneratedRefinedIteratedCertificate.lastStage] at hlast
  | d + 1, .step I C _href rest, m, hgc, T, m', s, hlast => by
      simp only [GeneratedRefinedIteratedCertificate.stageGateCounts,
        List.replicate_succ] at hgc
      injection hgc with hhead htail
      simp only [GeneratedRefinedIteratedCertificate.lastStage] at hlast
      cases hrest : rest.lastStage with
      | some x =>
          rw [hrest] at hlast
          simp only [Option.some.injEq] at hlast
          subst x
          exact lastStage_gateCount_of_stageGateCounts_replicate rest htail
            T m' s hrest
      | none =>
          rw [hrest] at hlast
          simp only [Option.some.injEq, Prod.mk.injEq] at hlast
          obtain ⟨_hT, hm, _hs⟩ := hlast
          exact hm.symm.trans hhead

open GeneratedRefinedIteratedCertificate

/-- **Frozen-depth-view geometric collapse with a global last-tree budget.**
Given an explicit depth-`d` view, a uniform width bound on its bottom gates,
and the same geometric entry bound used by the universal-layer theorem, the
viewed formula admits a generated refined certificate. In addition to the
usual schedule bookkeeping, the theorem returns the final combined decision
tree with the global budget `t(d,s) = V.gateCount * (s - 1)`.

This is the structural consumer for supplied frozen depth views; it is not an
automatic decomposition theorem for arbitrary formulas. -/
theorem frozenDepthView_geometricCollapseWithGlobalTreeBudget
    (k w : Nat) {n d : Nat} {F : BDFormula n}
    (V : FrozenDepthView n F d)
    (hm : 1 <= V.gateCount) (hw1 : 1 <= w)
    (hw : forall g, g ∈ V.layer.gates -> widthDNF g.theDNF <= w)
    (hn : 2 * (64 * V.gateCount) ^ k * (64 * V.gateCount * w) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        F (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) V.gateCount /\
      cert.stageBudgets = List.replicate (k + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule V.gateCount
          (n / (64 * V.gateCount * w)) (k + 1)).map stageStars /\
      TreeBudgetFrom (frozenGlobalTreeBudget V) V.gateCount (k + 1)
        (geometricSchedule V.gateCount
          (n / (64 * V.gateCount * w)) (k + 1)) /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, V.gateCount, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= frozenGlobalTreeBudget V d s /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed F)) := by
  cases V with
  | mk layer hform hdepthBound =>
  subst F
  simp only [FrozenDepthView.gateCount, frozenGlobalTreeBudget] at hm hn ⊢
  obtain ⟨cert, hgc, hb, hsc, _ht⟩ :=
    geometricFamilyCollapse_universal k w layer hm hw1 hw hn
  have ht : TreeBudgetFrom (fun depth s => layer.gates.length * (s - 1))
      layer.gates.length (k + 1)
      (geometricSchedule layer.gates.length
        (n / (64 * layer.gates.length * w)) (k + 1)) :=
    geometricSchedule_frozenGlobalTreeBudget
      ({ layer := layer
         originalFormula_eq := rfl
         depth_bound := Nat.le_refl _ } : FrozenDepthView n layer.originalFormula
          (depth layer.originalFormula))
      layer.gates.length (k + 1) (n / (64 * layer.gates.length * w)) (k + 1)
  have hsome := lastStage_isSome cert (Nat.succ_pos k)
  cases hlast : cert.lastStage with
  | none =>
      rw [hlast] at hsome
      simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      have hmLast : m = layer.gates.length :=
        lastStage_gateCount_of_stageGateCounts_replicate cert
          hgc T m s hlast
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      subst hmLast
      refine ⟨cert, hgc, hb, hsc, ?_, T, s, hlast, heval, ?_, ?_⟩
      · exact ht
      · exact hdepth
      · intro a ha
        rw [heval a, finalFormula_restrict_eval cert a ha]

/-- Bottom-layer mixed raw DNF/CNF formulas inhabit the frozen depth-view
interface at their computed formula depth. This is a constructor for the
already-exposed bottom layer, not an arbitrary deeper decomposition. -/
def mixedBottomFrozenDepthView {n : Nat} (p : ParentKind)
    (gs : List (RawGate n)) (hgs : forall g, g ∈ gs -> RawGate.Simple g) :
    FrozenDepthView n (p.merge (gs.map RawGate.toBD))
      (depth (p.merge (gs.map RawGate.toBD))) where
  layer := mixedSynthLayer p gs hgs
  originalFormula_eq := mixedSynthLayer_originalFormula p gs hgs
  depth_bound := Nat.le_refl _

open GeneratedRefinedIteratedCertificate in
/-- Mixed bottom-layer formulas, routed through the new frozen depth-view
interface, inherit the global last-tree budget. This upgrades the raw
`GateSpec` bottom-layer family with a real final-tree depth bound while still
staying inside the explicitly synthesized bottom-layer class. -/
theorem mixedBottomFrozenDepthView_geometricCollapseWithGlobalTreeBudget
    (k w : Nat) {n : Nat} (p : ParentKind)
    (gs : List (RawGate n))
    (hgs : forall g, g ∈ gs -> RawGate.Simple g)
    (hm : 1 <= gs.length) (hw1 : 1 <= w)
    (hw : forall g, g ∈ gs -> widthDNF g.raw <= w)
    (hn : 2 * (64 * gs.length) ^ k * (64 * gs.length * w) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (p.merge (gs.map RawGate.toBD)) (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) gs.length /\
      cert.stageBudgets = List.replicate (k + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule gs.length
          (n / (64 * gs.length * w)) (k + 1)).map stageStars /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, gs.length, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= gs.length * (s - 1) /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a
            (restrict cert.finalComposed (p.merge (gs.map RawGate.toBD)))) := by
  let V := mixedBottomFrozenDepthView p gs hgs
  have hlen : V.gateCount = gs.length := by
    simp [V, mixedBottomFrozenDepthView, FrozenDepthView.gateCount,
      mixedSynthLayer, mixedSynthGates_length]
  have hmV : 1 <= V.gateCount := by
    rw [hlen]
    exact hm
  have hwV : forall g, g ∈ V.layer.gates -> widthDNF g.theDNF <= w := by
    simpa [V, mixedBottomFrozenDepthView, mixedSynthLayer] using
      mixedSynthGates_width w gs hgs hw
  have hnV : 2 * (64 * V.gateCount) ^ k * (64 * V.gateCount * w) <= n := by
    rw [hlen]
    exact hn
  obtain ⟨cert, hgc, hb, hsc, _ht, T, s, hlast, heval, hdepth, hsem⟩ :=
    frozenDepthView_geometricCollapseWithGlobalTreeBudget k w V hmV hw1 hwV hnV
  refine ⟨cert, ?_, hb, ?_, T, s, ?_, heval, ?_, hsem⟩
  · rw [hgc, hlen]
  · rw [hsc, hlen]
  · rw [hlen] at hlast
    exact hlast
  · rw [frozenGlobalTreeBudget] at hdepth
    rw [hlen] at hdepth
    exact hdepth

end FrozenDepthView
end PvNP
