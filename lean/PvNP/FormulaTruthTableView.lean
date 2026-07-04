import PvNP.FrozenDepthView

/-!
# Truth-table formula views for top-connective frozen depth views

`FrozenDepthView` consumes an explicit start layer.  The mixed formula-family
modules synthesize such layers from raw bottom DNF/CNF syntax.  This module
adds a deliberately broad but deliberately expensive fallback: every formula
can be given a semantic DNF view by querying all variables in a full decision
tree and then re-viewing that tree as a path DNF.

The resulting view is useful as a structural bridge for formulas whose top
constructor is already an `and` or `or`: each immediate child can be turned into
a `GateSpec.dnf`, so the exact raw top formula `p.merge children` receives a
`FrozenDepthView` automatically.

## HONEST SCOPE STATEMENT (read this)

* The constructed DNF view is a truth-table/path view.  Its width is bounded by
  `n`, not by the syntactic AC0 bottom fan-in.  This is therefore not the
  efficient layered decomposition needed to close full frozen-form B4.
* The top-connective collapse theorem is conditional on a caller-supplied width
  bound for these constructed child views plus the usual geometric entry
  hypothesis.  It is a real consumer theorem, but those hypotheses may be too
  strong for the truth-table fallback in nontrivial regimes.
* The module covers exact top-level `and`/`or` formulas.  It does not introduce
  an identity parent for leaves and does not recursively synthesize efficient
  depth-`d` AC0 layers.
* The positive-depth raw-formula theorem below simply pattern-matches a real
  `BDFormula` to expose its top `and`/`or` constructor, then uses the same
  truth-table child views.  Leaves and constants still have no exact identity
  parent in `MinimalLayeredFormula`.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaTruthTableView

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open FrozenProductSchedule
open FrozenProductScheduleRatio
open FrozenDepthView
open SwitchingLemmaStatement
open TreePathViews

/-! ## A generic full decision tree for Boolean functions -/

/-- Update an accumulated assignment at one queried variable. -/
def updateAssignment {n : Nat} (acc : Assignment n) (v : Fin n) (b : Bool) :
    Assignment n :=
  fun u => if u = v then b else acc u

/-- Build a decision tree computing an arbitrary Boolean function by querying
the listed variables in order and evaluating the function at the accumulated
leaf assignment. -/
def dtOfFun {n : Nat} (f : Assignment n -> Bool) :
    List (Fin n) -> Assignment n -> DTree n
  | [], acc => DTree.leaf (f acc)
  | v :: rest, acc =>
      DTree.node v (dtOfFun f rest (updateAssignment acc v false))
        (dtOfFun f rest (updateAssignment acc v true))

theorem mem_allVars (n : Nat) (v : Fin n) : v ∈ allVars n := by
  rw [allVars, List.mem_pmap]
  exact ⟨v.val, List.mem_range.mpr v.isLt, rfl⟩

theorem allVars_length (n : Nat) : (allVars n).length = n := by
  rw [allVars, List.length_pmap, List.length_range]

/-- The full tree computes `f` once every variable not already fixed in the
accumulator appears somewhere in the remaining query order. -/
theorem dtOfFun_eval {n : Nat} (f : Assignment n -> Bool)
    (a : Assignment n) :
    forall (order : List (Fin n)) (acc : Assignment n),
      (forall v : Fin n, v ∈ order \/ acc v = a v) ->
      dtEval a (dtOfFun f order acc) = f a
  | [], acc, hinv => by
      show f acc = f a
      congr 1
      funext v
      rcases hinv v with hmem | hacc
      · exact absurd hmem (List.not_mem_nil v)
      · exact hacc
  | v :: rest, acc, hinv => by
      have hstep : forall b : Bool, a v = b ->
          dtEval a (dtOfFun f rest (updateAssignment acc v b)) = f a := by
        intro b hb
        apply dtOfFun_eval
        intro u
        by_cases huv : u = v
        · right
          subst huv
          simp [updateAssignment, hb]
        · rcases hinv u with hmem | hacc
          · rcases List.mem_cons.mp hmem with hveq | hrest
            · exact absurd hveq huv
            · exact Or.inl hrest
          · right
            simpa [updateAssignment, huv] using hacc
      cases hav : a v with
      | false =>
          have := hstep false hav
          simpa [dtOfFun, dtEval, hav] using this
      | true =>
          have := hstep true hav
          simpa [dtOfFun, dtEval, hav] using this

theorem dtOfFun_depth {n : Nat} (f : Assignment n -> Bool) :
    forall (order : List (Fin n)) (acc : Assignment n),
      dtDepth (dtOfFun f order acc) = order.length
  | [], _ => rfl
  | _v :: rest, acc => by
      simp [dtOfFun, dtDepth, dtOfFun_depth f rest, Nat.max_self,
        Nat.add_comm]

/-! ## Arbitrary formulas as semantic DNF views -/

/-- Full truth-table decision tree for a real bounded-depth formula. -/
def formulaDecisionTree {n : Nat} (F : BDFormula n) : DTree n :=
  dtOfFun (fun a => eval a F) (allVars n) (fun _ => false)

theorem formulaDecisionTree_eval {n : Nat} (F : BDFormula n)
    (a : Assignment n) :
    dtEval a (formulaDecisionTree F) = eval a F := by
  unfold formulaDecisionTree
  apply dtOfFun_eval
  intro v
  exact Or.inl (mem_allVars n v)

theorem formulaDecisionTree_depth {n : Nat} (F : BDFormula n) :
    dtDepth (formulaDecisionTree F) = n := by
  rw [formulaDecisionTree, dtOfFun_depth, allVars_length]

/-- Every formula has a semantic simple DNF view via its full decision tree.
The view is broad but expensive; see `widthDNF_formulaDNFView_le`. -/
def formulaDNFView {n : Nat} (F : BDFormula n) : DNFView F :=
  let T := formulaDecisionTree F
  { D := (treeDNFView T).D
    sem_eq := fun a => by
      calc
        eval a F = dtEval a T := (formulaDecisionTree_eval F a).symm
        _ = eval a (treeToFormula T) := (eval_treeToFormula a T).symm
        _ = dnfEval a (treeDNFView T).D := (treeDNFView T).sem_eq a
    simple := (treeDNFView T).simple }

/-- The truth-table/path DNF view has width at most the number of variables. -/
theorem widthDNF_formulaDNFView_le {n : Nat} (F : BDFormula n) :
    widthDNF (formulaDNFView F).D <= n := by
  change widthDNF (treeDNFView (formulaDecisionTree F)).D <= n
  have h := widthDNF_treeDNFView_le (formulaDecisionTree F)
  rw [formulaDecisionTree_depth] at h
  exact h

/-! ## Top-connective layers from raw formula children -/

/-- A formula child packaged as a `GateSpec.dnf` using the truth-table view. -/
def formulaGate {n : Nat} (F : BDFormula n) : GateSpec n :=
  GateSpec.dnf F (formulaDNFView F)

theorem formulaGate_formula {n : Nat} (F : BDFormula n) :
    (formulaGate F).formula = F := rfl

theorem formulaGate_width_le_vars {n : Nat} (F : BDFormula n) :
    widthDNF (formulaGate F).theDNF <= n :=
  widthDNF_formulaDNFView_le F

/-- The exact top-connective layer for `p.merge children`. -/
def topConnectiveLayer {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) : MinimalLayeredFormula n where
  parent := p
  gates := children.map formulaGate

theorem topConnectiveLayer_gateCount {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) :
    (topConnectiveLayer p children).gates.length = children.length := by
  simp [topConnectiveLayer]

theorem map_formulaGate_formula {n : Nat} :
    forall children : List (BDFormula n),
      (children.map formulaGate).map GateSpec.formula = children
  | [] => rfl
  | F :: rest => by
      simp [formulaGate, GateSpec.formula, map_formulaGate_formula rest]

theorem topConnectiveLayer_originalFormula {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) :
    (topConnectiveLayer p children).originalFormula = p.merge children := by
  show p.merge ((children.map formulaGate).map GateSpec.formula) =
    p.merge children
  rw [map_formulaGate_formula]

theorem topConnectiveLayer_width_le_vars {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) :
    forall g, g ∈ (topConnectiveLayer p children).gates ->
      widthDNF g.theDNF <= n := by
  intro g hg
  rw [topConnectiveLayer] at hg
  rcases List.mem_map.mp hg with ⟨F, _hF, rfl⟩
  exact formulaGate_width_le_vars F

/-- An automatically synthesized `FrozenDepthView` for exact raw top-level
`and`/`or` formulas. -/
def topConnectiveFrozenDepthView {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) :
    FrozenDepthView n (p.merge children) (depth (p.merge children)) where
  layer := topConnectiveLayer p children
  originalFormula_eq := topConnectiveLayer_originalFormula p children
  depth_bound := Nat.le_refl _

theorem topConnectiveFrozenDepthView_gateCount {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) :
    (topConnectiveFrozenDepthView p children).gateCount = children.length := by
  simp [topConnectiveFrozenDepthView, FrozenDepthView.gateCount,
    topConnectiveLayer]

theorem topConnectiveFrozenDepthView_width_le_vars {n : Nat} (p : ParentKind)
    (children : List (BDFormula n)) :
    forall g, g ∈ (topConnectiveFrozenDepthView p children).layer.gates ->
      widthDNF g.theDNF <= n := by
  simpa [topConnectiveFrozenDepthView] using
    topConnectiveLayer_width_le_vars p children

open GeneratedRefinedIteratedCertificate in
/-- **Top-connective formula collapse through truth-table child views.**
For any raw top-level `and`/`or` formula `p.merge children`, the start layer is
constructed automatically from the immediate child formulas.  The theorem then
applies the supplied-view global-budget consumer.

The width hypothesis is intentionally explicit: the constructed child views are
truth-table/path DNFs, with only the general bound `<= n` provided by this
module.  This theorem therefore advances the structural view-synthesis surface
without claiming efficient arbitrary depth-`d` AC0 decomposition. -/
theorem topConnectiveFormula_geometricCollapseWithGlobalTreeBudget
    (k w : Nat) {n : Nat} (p : ParentKind)
    (children : List (BDFormula n))
    (hm : 1 <= children.length) (hw1 : 1 <= w)
    (hw : forall F, F ∈ children -> widthDNF (formulaDNFView F).D <= w)
    (hn : 2 * (64 * children.length) ^ k *
        (64 * children.length * w) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (p.merge children) (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) children.length /\
      cert.stageBudgets = List.replicate (k + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule children.length
          (n / (64 * children.length * w)) (k + 1)).map stageStars /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, children.length, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= children.length * (s - 1) /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed
            (p.merge children))) := by
  let V := topConnectiveFrozenDepthView p children
  have hlen : V.gateCount = children.length := by
    simp [V, topConnectiveFrozenDepthView, FrozenDepthView.gateCount,
      topConnectiveLayer]
  have hmV : 1 <= V.gateCount := by
    rw [hlen]
    exact hm
  have hwV : forall g, g ∈ V.layer.gates -> widthDNF g.theDNF <= w := by
    intro g hg
    change g ∈ children.map formulaGate at hg
    rcases List.mem_map.mp hg with ⟨F, hF, rfl⟩
    exact hw F hF
  have hnV : 2 * (64 * V.gateCount) ^ k *
      (64 * V.gateCount * w) <= n := by
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

/-! ## Raw positive-depth formulas -/

/-- The immediate children of a raw formula when its top constructor is
`and`/`or`; leaves and constants expose no top-connective children. -/
def topChildren {n : Nat} : BDFormula n -> List (BDFormula n)
  | BDFormula.and children => children
  | BDFormula.or children => children
  | _ => []

/-- The number of immediate top-connective children of a raw formula. -/
def topChildCount {n : Nat} (F : BDFormula n) : Nat :=
  (topChildren F).length

/-- Every positive-depth raw formula has an automatically synthesized
`FrozenDepthView` through its top `and`/`or` constructor and truth-table child
views.  This is exact for non-leaf syntax, but it is still the broad
truth-table fallback, not an efficient AC0 decomposition. -/
def positiveDepthFrozenDepthView {n : Nat} (F : BDFormula n)
    (hpos : 0 < depth F) : FrozenDepthView n F (depth F) := by
  cases F with
  | tru =>
      simp [depth] at hpos
  | fls =>
      simp [depth] at hpos
  | lit l =>
      simp [depth] at hpos
  | and children =>
      exact topConnectiveFrozenDepthView ParentKind.and children
  | or children =>
      exact topConnectiveFrozenDepthView ParentKind.or children

theorem positiveDepthFrozenDepthView_gateCount {n : Nat} (F : BDFormula n)
    (hpos : 0 < depth F) :
    (positiveDepthFrozenDepthView F hpos).gateCount = topChildCount F := by
  cases F with
  | tru =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | fls =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | lit l =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | and children =>
      simp [positiveDepthFrozenDepthView, topChildCount, topChildren,
        topConnectiveFrozenDepthView_gateCount]
  | or children =>
      simp [positiveDepthFrozenDepthView, topChildCount, topChildren,
        topConnectiveFrozenDepthView_gateCount]

theorem positiveDepthFrozenDepthView_width_le_vars {n : Nat} (F : BDFormula n)
    (hpos : 0 < depth F) :
    forall g, g ∈ (positiveDepthFrozenDepthView F hpos).layer.gates ->
      widthDNF g.theDNF <= n := by
  cases F with
  | tru =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | fls =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | lit l =>
      simp [positiveDepthFrozenDepthView, depth] at hpos
  | and children =>
      simpa [positiveDepthFrozenDepthView] using
        topConnectiveFrozenDepthView_width_le_vars ParentKind.and children
  | or children =>
      simpa [positiveDepthFrozenDepthView] using
        topConnectiveFrozenDepthView_width_le_vars ParentKind.or children

open GeneratedRefinedIteratedCertificate in
/-- **Positive-depth raw formula collapse through truth-table child views.**
For any real raw formula with positive `depth`, this theorem exposes the top
`and`/`or` constructor automatically and applies the top-connective
truth-table `FrozenDepthView` route.

The width hypothesis remains explicit over the exposed immediate children.
The generic fallback bound available in this module is only `<= n`, so this is
not an efficient arbitrary depth-`d` AC0 decomposition or full B4 closure. -/
theorem positiveDepthFormula_geometricCollapseWithGlobalTreeBudget
    (k w : Nat) {n : Nat} (F : BDFormula n)
    (hpos : 0 < depth F)
    (hm : 1 <= topChildCount F) (hw1 : 1 <= w)
    (hw : forall child, child ∈ topChildren F ->
      widthDNF (formulaDNFView child).D <= w)
    (hn : 2 * (64 * topChildCount F) ^ k *
        (64 * topChildCount F * w) <= n) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        F (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) (topChildCount F) /\
      cert.stageBudgets = List.replicate (k + 1) 2 /\
      cert.stageStarCounts =
        (geometricSchedule (topChildCount F)
          (n / (64 * topChildCount F * w)) (k + 1)).map stageStars /\
      exists T : DTree n, exists s : Nat,
        cert.lastStage = some (T, topChildCount F, s) /\
        (forall a : Assignment n, dtEval a T = eval a cert.finalFormula) /\
        dtDepth T <= topChildCount F * (s - 1) /\
        (forall a : Assignment n, Agree cert.finalComposed a ->
          dtEval a T = eval a (restrict cert.finalComposed F)) := by
  cases F with
  | tru =>
      simp [depth] at hpos
  | fls =>
      simp [depth] at hpos
  | lit l =>
      simp [depth] at hpos
  | and children =>
      simpa [topChildren, topChildCount, ParentKind.merge] using
        topConnectiveFormula_geometricCollapseWithGlobalTreeBudget
          k w ParentKind.and children hm hw1 hw hn
  | or children =>
      simpa [topChildren, topChildCount, ParentKind.merge] using
        topConnectiveFormula_geometricCollapseWithGlobalTreeBudget
          k w ParentKind.or children hm hw1 hw hn

end FormulaTruthTableView
end PvNP
