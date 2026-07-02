import PvNP.GeneratedOneStepDepthReduction
import PvNP.RestrictionComposition

/-!
# Gate B / B4: the final generated iterated-collapse theorem

This module iterates the B3 one-step generated depth reduction.  A
`GeneratedCollapsePlan` supplies, for each stage, a minimal layered view of the
current formula together with a counting hypothesis against the subspace of
restrictions CONSISTENT with everything generated so far; the plan's later
stages may depend on the certificates generated at earlier stages (that is the
`next` function).  The theorem `generatedIteratedCollapse` then produces:

* one counting-generated restriction per stage, each consistent with the
  composition of all earlier ones (`ConsistentSeq`), with per-stage star counts
  pinned in the FULL `n`-variable star space;
* the first-wins composition of the whole sequence, which always has a total
  extension, and under any agreeing assignment every stage restriction is
  simultaneously respected;
* semantic preservation: the final rewritten formula evaluates exactly as the
  (fully restricted) original on every assignment agreeing with the composed
  restriction;
* per-stage depth AND size accounting for every rewritten stage output
  (`depth ≤ 1 + (2(s-1)+1)`, `formulaSize ≤ 1 + m·6·2^(s-1)`);
* a single decision tree of depth `≤ m_last · (s_last - 1)` computing the final
  rewritten formula on ALL assignments, hence computing the fully restricted
  original formula on all assignments agreeing with the composed restriction.

## HONEST SCOPE STATEMENT (read this)

* The per-stage layered views are SUPPLIED by the plan, exactly as in B3.  This
  module does NOT decompose arbitrary `BDFormula`/AC0 formulas into layered
  views, and does NOT convert generated decision trees back into DNF/CNF views
  for re-switching; a caller who wants a nonempty second stage must supply that
  view through the plan's `next` function.
* The per-stage counting hypotheses (`beat` fields) are supplied against the
  consistent-subspace cardinalities.  The closed form is proved for the FULL
  star space (`RestrictionComposition.restrictionsWithStars_card`); no closed
  form is claimed for consistent subspaces with a nonfree base.
* KNOWN SATISFIABILITY GAP: each stage's `beat` compares a bad-set count over
  the FULL `n`-variable star space against the consistent-subspace cardinality.
  After any variable-fixing stage the consistent subspace is exponentially
  smaller than the full space; no plan with nonempty (width `≥ 1`) gates at two
  or more stages is exhibited here, and back-of-envelope counting suggests none
  exists for these beat shapes.  A consistent-subspace-relative (free-subcube
  renormalized) bad-set bound is the open ingredient for genuine nontrivial
  iteration.  The frozen B4 goal statement in the `GeneratedGoodRestriction`
  docstring (single upfront depth-`d` layered view, single product-of-stages
  hypothesis `B(m, w, s, d)`, `t(d, s)` tree bound) is NOT discharged by this
  module.
* Per-stage star counts are pinned in the full `n`-variable star space; a stage
  restriction may star or re-fix variables already fixed by the accumulated
  base (first-wins composition discards such re-fixings).  No bound is proved
  on the free-variable count of the composed restriction, and no textbook
  renormalization (stars among remaining free variables, widths re-measured
  after restriction) is performed.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower bound,
  NOT an NP/circuit lower bound, NOT a statement about P vs NP.  Gate A rung 4
  remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace GeneratedIteratedCollapseFinal

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open GeneratedOneStepDepthReduction
open RestrictionComposition

/-! ## Formula size -/

/-- Gate/leaf count of a bounded-depth formula (every constant, literal, and
gate contributes `1`). -/
def formulaSize {n : Nat} : BDFormula n → Nat
  | .tru => 1
  | .fls => 1
  | .lit _ => 1
  | .and l => 1 + (l.attach.map (fun f => formulaSize f.1)).foldr (· + ·) 0
  | .or  l => 1 + (l.attach.map (fun f => formulaSize f.1)).foldr (· + ·) 0
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

theorem formulaSize_lit {n : Nat} (l : Literal n) :
    formulaSize (BDFormula.lit l) = 1 := by simp only [formulaSize]

/-- `and` size with the `attach` erased. -/
theorem formulaSize_and {n : Nat} (l : List (BDFormula n)) :
    formulaSize (BDFormula.and l) =
      1 + (l.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
  rw [show formulaSize (BDFormula.and l)
        = 1 + (l.attach.map (fun f => formulaSize f.1)).foldr (· + ·) 0 from by
      rw [formulaSize]]
  rw [List.attach_map_val l (fun f => formulaSize f)]

/-- `or` size with the `attach` erased. -/
theorem formulaSize_or {n : Nat} (l : List (BDFormula n)) :
    formulaSize (BDFormula.or l) =
      1 + (l.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
  rw [show formulaSize (BDFormula.or l)
        = 1 + (l.attach.map (fun f => formulaSize f.1)).foldr (· + ·) 0 from by
      rw [formulaSize]]
  rw [List.attach_map_val l (fun f => formulaSize f)]

theorem formulaSize_and_lit_pair {n : Nat} (l : Literal n) (g : BDFormula n) :
    formulaSize (BDFormula.and [BDFormula.lit l, g]) = 2 + formulaSize g := by
  rw [formulaSize_and]
  simp [formulaSize_lit]
  omega

theorem formulaSize_or_pair {n : Nat} (g0 g1 : BDFormula n) :
    formulaSize (BDFormula.or [g0, g1]) =
      1 + (formulaSize g0 + formulaSize g1) := by
  rw [formulaSize_or]
  simp

/-- Tree-to-formula size, exponential in the tree depth (with the exact
constant of the two-level `or`/`and`/literal encoding). -/
theorem formulaSize_treeToFormula_add_five {n : Nat} (t : DTree n) :
    formulaSize (treeToFormula t) + 5 ≤ 6 * 2 ^ dtDepth t := by
  induction t with
  | leaf b =>
      cases b <;> simp [treeToFormula, formulaSize]
  | node v t0 t1 ih0 ih1 =>
      have hsize : formulaSize (treeToFormula (DTree.node v t0 t1)) =
          5 + (formulaSize (treeToFormula t0) + formulaSize (treeToFormula t1)) := by
        show formulaSize (BDFormula.or
          [ BDFormula.and [BDFormula.lit ⟨v, false⟩, treeToFormula t0]
          , BDFormula.and [BDFormula.lit ⟨v, true⟩,  treeToFormula t1] ]) = _
        rw [formulaSize_or_pair, formulaSize_and_lit_pair, formulaSize_and_lit_pair]
        omega
      rw [hsize, dtDepth_node]
      have h0 : (2:Nat) ^ dtDepth t0 ≤ 2 ^ max (dtDepth t0) (dtDepth t1) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
      have h1 : (2:Nat) ^ dtDepth t1 ≤ 2 ^ max (dtDepth t0) (dtDepth t1) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      have hpow : (2:Nat) ^ (1 + max (dtDepth t0) (dtDepth t1)) =
          2 * 2 ^ max (dtDepth t0) (dtDepth t1) := by
        rw [Nat.pow_add, Nat.pow_one]
      omega

theorem formulaSize_treeToFormula_le {n : Nat} (t : DTree n) :
    formulaSize (treeToFormula t) ≤ 6 * 2 ^ dtDepth t := by
  have := formulaSize_treeToFormula_add_five t
  omega

private theorem foldr_add_le_of_all {xs : List Nat} {B : Nat}
    (h : ∀ x ∈ xs, x ≤ B) : xs.foldr (· + ·) 0 ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldr_cons, List.length_cons]
      have hx := h x (List.mem_cons_self x xs)
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      calc x + xs.foldr (· + ·) 0 ≤ B + xs.length * B := Nat.add_le_add hx hxs
        _ = (xs.length + 1) * B := by rw [Nat.succ_mul, Nat.add_comm]

private theorem formulaSize_merge_le {n : Nat} (k : ParentKind)
    (children : List (BDFormula n)) {B : Nat}
    (hB : ∀ F ∈ children, formulaSize F ≤ B) :
    formulaSize (k.merge children) ≤ 1 + children.length * B := by
  have hfold : (children.map (fun f => formulaSize f)).foldr (· + ·) 0 ≤
      children.length * B := by
    have := foldr_add_le_of_all (xs := children.map (fun f => formulaSize f))
      (B := B) (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨f, hf, rfl⟩
        exact hB f hf)
    rw [List.length_map] at this
    exact this
  cases k
  · rw [ParentKind.merge, formulaSize_and]
    omega
  · rw [ParentKind.merge, formulaSize_or]
    omega

/-- **B4 per-stage size accounting.**  The B3 rewritten formula has size at most
`1 + m · 6 · 2^(s-1)` for `m` bottom gates and stage budget `s`. -/
theorem reducedFormula_size_le {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    formulaSize C.reducedFormula ≤
      1 + I.layer.gates.length * (6 * 2 ^ (I.s - 1)) := by
  have hchild : ∀ F ∈ C.reducedChildren, formulaSize F ≤ 6 * 2 ^ (I.s - 1) := by
    intro F hF
    rw [GeneratedOneStepCertificate.reducedChildren] at hF
    rcases List.mem_map.mp hF with ⟨g, _hg, rfl⟩
    have hdt := C.treeDepth g.1 g.2
    calc formulaSize (treeToFormula (C.treeOf g.1 g.2))
        ≤ 6 * 2 ^ dtDepth (C.treeOf g.1 g.2) :=
          formulaSize_treeToFormula_le _
      _ ≤ 6 * 2 ^ (I.s - 1) :=
          Nat.mul_le_mul (Nat.le_refl 6)
            (Nat.pow_le_pow_right (by omega) (by omega))
  have hmerge := formulaSize_merge_le I.layer.parent C.reducedChildren hchild
  rw [C.reducedChildCount] at hmerge
  exact hmerge

/-! ## Combining the generated stage trees into one decision tree -/

/-- Continue every leaf of a tree with a follow-up tree chosen by the leaf's
value. -/
def graft {n : Nat} : DTree n → (Bool → DTree n) → DTree n
  | .leaf b, k => k b
  | .node v t0 t1, k => .node v (graft t0 k) (graft t1 k)

theorem dtEval_graft {n : Nat} (a : Assignment n) (t : DTree n)
    (k : Bool → DTree n) :
    dtEval a (graft t k) = dtEval a (k (dtEval a t)) := by
  induction t with
  | leaf b => rfl
  | node v t0 t1 ih0 ih1 =>
      simp only [graft, dtEval_node]
      cases ha : a v <;> simp [ha, ih0, ih1]

theorem dtDepth_graft_le {n : Nat} (t : DTree n) (k : Bool → DTree n) :
    dtDepth (graft t k) ≤
      dtDepth t + max (dtDepth (k true)) (dtDepth (k false)) := by
  induction t with
  | leaf b =>
      cases b
      · simp [graft]
      · simp [graft]
  | node v t0 t1 ih0 ih1 =>
      simp only [graft, dtDepth_node]
      omega

/-- Sequential conjunction tree: evaluate each listed tree in order, exiting
`false` early. -/
def andTree {n : Nat} : List (DTree n) → DTree n
  | [] => .leaf true
  | t :: ts => graft t (fun b => if b then andTree ts else .leaf false)

theorem dtEval_andTree {n : Nat} (a : Assignment n) (ts : List (DTree n)) :
    dtEval a (andTree ts) = (ts.map (fun t => dtEval a t)).all id := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [andTree]
      rw [dtEval_graft]
      cases hb : dtEval a t
      · simp [hb]
      · simp [hb, ih]

theorem dtDepth_andTree_le {n : Nat} (ts : List (DTree n)) :
    dtDepth (andTree ts) ≤ (ts.map (fun t => dtDepth t)).foldr (· + ·) 0 := by
  induction ts with
  | nil => simp [andTree]
  | cons t ts ih =>
      simp only [List.map_cons, List.foldr_cons]
      have hg := dtDepth_graft_le t (fun b => if b then andTree ts else .leaf false)
      simp only [if_true, Bool.false_eq_true, if_false, dtDepth_leaf] at hg
      have hstep : dtDepth (andTree (t :: ts)) =
          dtDepth (graft t (fun b => if b then andTree ts else .leaf false)) := by
        rw [andTree]
      rw [hstep]
      omega

/-- Sequential disjunction tree: evaluate each listed tree in order, exiting
`true` early. -/
def orTree {n : Nat} : List (DTree n) → DTree n
  | [] => .leaf false
  | t :: ts => graft t (fun b => if b then .leaf true else orTree ts)

theorem dtEval_orTree {n : Nat} (a : Assignment n) (ts : List (DTree n)) :
    dtEval a (orTree ts) = (ts.map (fun t => dtEval a t)).any id := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [orTree]
      rw [dtEval_graft]
      cases hb : dtEval a t
      · simp [hb, ih]
      · simp [hb]

theorem dtDepth_orTree_le {n : Nat} (ts : List (DTree n)) :
    dtDepth (orTree ts) ≤ (ts.map (fun t => dtDepth t)).foldr (· + ·) 0 := by
  induction ts with
  | nil => simp [orTree]
  | cons t ts ih =>
      simp only [List.map_cons, List.foldr_cons]
      have hg := dtDepth_graft_le t (fun b => if b then .leaf true else orTree ts)
      simp only [if_true, Bool.false_eq_true, if_false, dtDepth_leaf] at hg
      have hstep : dtDepth (orTree (t :: ts)) =
          dtDepth (graft t (fun b => if b then .leaf true else orTree ts)) := by
        rw [orTree]
      rw [hstep]
      omega

/-- Combine child trees under the parent kind. -/
def parentTree {n : Nat} : ParentKind → List (DTree n) → DTree n
  | ParentKind.and, ts => andTree ts
  | ParentKind.or, ts => orTree ts

theorem dtEval_parentTree {n : Nat} (a : Assignment n) (k : ParentKind)
    (ts : List (DTree n)) :
    dtEval a (parentTree k ts) = k.evalList (ts.map (fun t => dtEval a t)) := by
  cases k
  · exact dtEval_andTree a ts
  · exact dtEval_orTree a ts

theorem dtDepth_parentTree_le {n : Nat} (k : ParentKind) (ts : List (DTree n)) :
    dtDepth (parentTree k ts) ≤ (ts.map (fun t => dtDepth t)).foldr (· + ·) 0 := by
  cases k
  · exact dtDepth_andTree_le ts
  · exact dtDepth_orTree_le ts

/-- The generated per-gate trees of a B3 certificate, in gate order. -/
def certTrees {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) : List (DTree n) :=
  I.layer.gates.attach.map (fun g => C.treeOf g.1 g.2)

/-- One decision tree computing a B3 certificate's rewritten formula: the
parent aggregation of the generated per-gate trees. -/
def certTree {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) : DTree n :=
  parentTree I.layer.parent (certTrees C)

theorem dtEval_certTree {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) (a : Assignment n) :
    dtEval a (certTree C) = eval a C.reducedFormula := by
  rw [certTree, dtEval_parentTree]
  rw [show C.reducedFormula = I.layer.parent.merge C.reducedChildren from rfl]
  rw [ParentKind.eval_merge]
  congr 1
  rw [certTrees, GeneratedOneStepCertificate.reducedChildren,
    List.map_map, List.map_map]
  apply List.map_congr_left
  intro g _
  simp only [Function.comp]
  exact (eval_treeToFormula a (C.treeOf g.1 g.2)).symm

theorem dtDepth_certTree_le {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    dtDepth (certTree C) ≤ I.layer.gates.length * (I.s - 1) := by
  calc dtDepth (certTree C)
      ≤ ((certTrees C).map (fun t => dtDepth t)).foldr (· + ·) 0 :=
        dtDepth_parentTree_le _ _
    _ ≤ ((certTrees C).map (fun t => dtDepth t)).length * (I.s - 1) :=
        foldr_add_le_of_all (by
          intro x hx
          rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
          rw [certTrees] at ht
          rcases List.mem_map.mp ht with ⟨g, _, rfl⟩
          have := C.treeDepth g.1 g.2
          omega)
    _ = I.layer.gates.length * (I.s - 1) := by
        rw [List.length_map, certTrees, List.length_map, List.length_attach]

/-! ## Consistent generated one-step inputs -/

/-- A B4 stage input: the B3 data with the counting beat stated against the
subspace of restrictions consistent with an accumulated base restriction. -/
structure GeneratedConsistentStepInput (n : Nat) (base : Restriction n) where
  layer : MinimalLayeredFormula n
  w : Nat
  s : Nat
  ℓ : Nat
  width : ∀ g ∈ layer.gates, widthDNF g.theDNF ≤ w
  beat : layer.gates.length *
      ((restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s) <
    (consistentSubspace base ℓ).card

namespace GeneratedConsistentStepInput

/-- Forget the consistency refinement: the consistent subspace is contained in
the full star space, so the B3 full-space beat follows. -/
def toPlain {n : Nat} {base : Restriction n}
    (I : GeneratedConsistentStepInput n base) : GeneratedOneStepInput n where
  layer := I.layer
  w := I.w
  s := I.s
  ℓ := I.ℓ
  width := I.width
  beat := Nat.lt_of_lt_of_le I.beat
    (Finset.card_le_card (consistentSubspace_subset base I.ℓ))

end GeneratedConsistentStepInput

/-- **B4 stage theorem.**  A consistent stage input generates a full B3
certificate whose restriction is in addition consistent with the base. -/
theorem generatedConsistentOneStep_exists {n : Nat} {base : Restriction n}
    (I : GeneratedConsistentStepInput n base) :
    ∃ C : GeneratedOneStepCertificate I.toPlain, ConsistentWith base C.ρ := by
  classical
  obtain ⟨ρ, hstars, hcons, hcollapse⟩ :=
    simultaneousCollapse_exists_consistent base I.layer.gates I.w I.s I.ℓ
      I.width I.beat
  exact ⟨{
    ρ := ρ
    stars := hstars
    treeOf := fun g hg => Classical.choose (hcollapse g hg)
    treeDepth := fun g hg => (Classical.choose_spec (hcollapse g hg)).1
    treeSemantics := fun g hg a ha =>
      (Classical.choose_spec (hcollapse g hg)).2 a ha
  }, hcons⟩

/-! ## Iteration plans and certificates -/

/-- A generated collapse plan of depth `d` rooted at a formula: each stage
supplies a layered view of the CURRENT formula plus a consistent-subspace beat,
and the following stages may depend on the certificate generated at this stage
(the `next` function receives it).  The plan supplies views; it never supplies
restrictions — those are generated by counting at every stage. -/
inductive GeneratedCollapsePlan (n : Nat) :
    Restriction n → BDFormula n → Nat → Type where
  | done (base : Restriction n) (F : BDFormula n) :
      GeneratedCollapsePlan n base F 0
  | step {d : Nat} {base : Restriction n}
      (I : GeneratedConsistentStepInput n base)
      (next : (C : GeneratedOneStepCertificate I.toPlain) →
        ConsistentWith base C.ρ →
        GeneratedCollapsePlan n (compose base C.ρ) C.reducedFormula d) :
      GeneratedCollapsePlan n base I.layer.originalFormula (d + 1)

/-- A generated iterated-collapse certificate: one B3 certificate per stage,
each restriction consistent with the composition of all earlier ones, with the
next stage rooted at the current stage's rewritten formula. -/
inductive GeneratedIteratedCertificate (n : Nat) :
    Restriction n → BDFormula n → Nat → Type where
  | done (base : Restriction n) (F : BDFormula n) :
      GeneratedIteratedCertificate n base F 0
  | step {d : Nat} {base : Restriction n}
      (I : GeneratedConsistentStepInput n base)
      (C : GeneratedOneStepCertificate I.toPlain)
      (hcons : ConsistentWith base C.ρ)
      (rest : GeneratedIteratedCertificate n (compose base C.ρ)
        C.reducedFormula d) :
      GeneratedIteratedCertificate n base I.layer.originalFormula (d + 1)

namespace GeneratedIteratedCertificate

/-- The final rewritten formula (the root formula if there are no stages). -/
def finalFormula {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedIteratedCertificate n base F d → BDFormula n
  | .done _ F => F
  | .step _ _ _ rest => rest.finalFormula

/-- The base composed with every generated stage restriction, first-wins, in
stage order. -/
def finalComposed {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedIteratedCertificate n base F d → Restriction n
  | .done base _ => base
  | .step _ _ _ rest => rest.finalComposed

/-- The generated stage restrictions in stage order. -/
def stageRestrictions {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} : GeneratedIteratedCertificate n base F d → List (Restriction n)
  | .done _ _ => []
  | .step _ C _ rest => C.ρ :: rest.stageRestrictions

/-- The stage budgets `s`, in stage order. -/
def stageBudgets {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedIteratedCertificate n base F d → List Nat
  | .done _ _ => []
  | .step I _ _ rest => I.s :: rest.stageBudgets

/-- The stage star counts `ℓ`, in stage order. -/
def stageStarCounts {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} : GeneratedIteratedCertificate n base F d → List Nat
  | .done _ _ => []
  | .step I _ _ rest => I.ℓ :: rest.stageStarCounts

/-- The stage bottom-gate counts, in stage order. -/
def stageGateCounts {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} : GeneratedIteratedCertificate n base F d → List Nat
  | .done _ _ => []
  | .step I _ _ rest => I.layer.gates.length :: rest.stageGateCounts

/-- The rewritten formula after each stage, in stage order. -/
def stageOutputs {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedIteratedCertificate n base F d → List (BDFormula n)
  | .done _ _ => []
  | .step _ C _ rest => C.reducedFormula :: rest.stageOutputs

/-- The last stage's combined decision tree together with its gate count and
budget (`none` when there are no stages). -/
def lastStage {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedIteratedCertificate n base F d → Option (DTree n × Nat × Nat)
  | .done _ _ => none
  | .step I C _ rest =>
      match rest.lastStage with
      | some x => some x
      | none => some (certTree C, I.layer.gates.length, I.s)

theorem stageRestrictions_length {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    cert.stageRestrictions.length = d := by
  induction cert with
  | done _base _F => rfl
  | step _I _C _hcons rest ih => simp [stageRestrictions, ih]

theorem agree_finalComposed_base {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a → Agree base a := by
  induction cert with
  | done base F =>
      intro a h
      exact h
  | step I C hcons rest ih =>
      intro a h
      simp only [finalComposed] at h
      exact agree_compose_left (ih a h)

theorem agree_finalComposed_stages {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a →
      ∀ ρ ∈ cert.stageRestrictions, Agree ρ a := by
  induction cert with
  | done base F =>
      intro a _ ρ hρ
      simp [stageRestrictions] at hρ
  | step I C hcons rest ih =>
      intro a h ρ hρ
      simp only [finalComposed] at h
      simp only [stageRestrictions, List.mem_cons] at hρ
      rcases hρ with rfl | hρ
      · exact agree_compose_right hcons (agree_finalComposed_base rest a h)
      · exact ih a h ρ hρ

/-- **Iterated semantic preservation.**  Under any assignment agreeing with the
composed restriction, the final rewritten formula evaluates exactly as the
original root formula. -/
theorem finalFormula_eval {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a →
      eval a cert.finalFormula = eval a F := by
  induction cert with
  | done base F =>
      intro a _
      rfl
  | step I C hcons rest ih =>
      intro a h
      simp only [finalComposed] at h
      have hcomp := agree_finalComposed_base rest a h
      have hρ : Agree C.ρ a := agree_compose_right hcons hcomp
      simp only [finalFormula]
      calc eval a rest.finalFormula
          = eval a C.reducedFormula := ih a h
        _ = eval a (restrict C.ρ I.toPlain.originalFormula) :=
            C.semantic_preservation a hρ
        _ = eval a I.layer.originalFormula := eval_restrict C.ρ a _ hρ

theorem finalFormula_restrict_eval {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a →
      eval a cert.finalFormula = eval a (restrict cert.finalComposed F) := by
  intro a h
  rw [finalFormula_eval cert a h, eval_restrict cert.finalComposed a F h]

/-- The composed restriction always has a total extension, so the semantic
conclusions above are never vacuous. -/
theorem finalComposed_extension {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    ∃ a : Assignment n, Agree cert.finalComposed a :=
  restriction_has_extension cert.finalComposed

theorem finalComposed_eq_foldl {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    cert.finalComposed = cert.stageRestrictions.foldl compose base := by
  induction cert with
  | done base F => rfl
  | step I C hcons rest ih =>
      simp only [finalComposed, stageRestrictions, List.foldl_cons]
      exact ih

/-- Sequential consistency of a restriction list against an accumulating base. -/
def ConsistentSeq {n : Nat} : Restriction n → List (Restriction n) → Prop
  | _, [] => True
  | base, ρ :: rest => ConsistentWith base ρ ∧ ConsistentSeq (compose base ρ) rest

theorem stageRestrictions_consistentSeq {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    ConsistentSeq base cert.stageRestrictions := by
  induction cert with
  | done _base _F => trivial
  | step _I _C hcons rest ih => exact ⟨hcons, ih⟩

theorem stageRestrictions_stars {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d) :
    List.Forall₂ (fun (ρ : Restriction n) (ℓ : Nat) =>
        ρ ∈ restrictionsWithStars n ℓ)
      cert.stageRestrictions cert.stageStarCounts := by
  induction cert with
  | done _base _F => exact List.Forall₂.nil
  | step _I C _hcons rest ih => exact List.Forall₂.cons C.stars ih

/-- **Per-stage depth accounting.**  Every stage output obeys the B3 one-step
depth bound at that stage's budget. -/
theorem stageOutputs_depth {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedIteratedCertificate n base F d) :
    List.Forall₂ (fun (out : BDFormula n) (s : Nat) =>
        depth out ≤ 1 + (2 * (s - 1) + 1))
      cert.stageOutputs cert.stageBudgets := by
  induction cert with
  | done _base _F => exact List.Forall₂.nil
  | step _I C _hcons rest ih =>
      exact List.Forall₂.cons C.reducedFormula_depth_bound ih

/-- **Per-stage size accounting.**  Every stage output obeys the one-step size
bound at that stage's gate count and budget. -/
theorem stageOutputs_size {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedIteratedCertificate n base F d) :
    List.Forall₂ (fun (out : BDFormula n) (p : Nat × Nat) =>
        formulaSize out ≤ 1 + p.1 * (6 * 2 ^ (p.2 - 1)))
      cert.stageOutputs (cert.stageGateCounts.zip cert.stageBudgets) := by
  induction cert with
  | done _base _F => exact List.Forall₂.nil
  | step _I C _hcons rest ih =>
      simp only [stageOutputs, stageGateCounts, stageBudgets, List.zip_cons_cons]
      exact List.Forall₂.cons (reducedFormula_size_le C) ih

theorem lastStage_isSome {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedIteratedCertificate n base F d) (hd : 0 < d) :
    cert.lastStage.isSome := by
  induction cert with
  | done _base _F => omega
  | step _I _C _hcons rest _ih =>
      simp only [lastStage]
      cases rest.lastStage with
      | some x => simp
      | none => simp

theorem finalFormula_of_lastStage_none {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedIteratedCertificate n base F d)
    (h : cert.lastStage = none) : cert.finalFormula = F := by
  induction cert with
  | done _base _F => rfl
  | step _I _C _hcons rest _ih =>
      simp only [lastStage] at h
      cases hlast : rest.lastStage with
      | some x => rw [hlast] at h; simp at h
      | none => rw [hlast] at h; simp at h

/-- **Final tree specification.**  The recorded last-stage tree computes the
final rewritten formula on EVERY assignment, with depth at most the last
stage's gate count times its budget minus one. -/
theorem lastStage_spec {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedIteratedCertificate n base F d) :
    ∀ T : DTree n, ∀ m s : Nat, cert.lastStage = some (T, m, s) →
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
        dtDepth T ≤ m * (s - 1) := by
  induction cert with
  | done base F =>
      intro T m s h
      simp [lastStage] at h
  | step I C hcons rest ih =>
      intro T m s h
      simp only [lastStage] at h
      cases hlast : rest.lastStage with
      | some x =>
          rw [hlast] at h
          simp only [Option.some.injEq] at h
          subst h
          have hrest := ih T m s hlast
          simp only [finalFormula]
          exact hrest
      | none =>
          rw [hlast] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hfin : rest.finalFormula = C.reducedFormula :=
            finalFormula_of_lastStage_none rest hlast
          constructor
          · intro a
            simp only [finalFormula]
            rw [hfin]
            exact dtEval_certTree C a
          · exact dtDepth_certTree_le C

end GeneratedIteratedCertificate

open GeneratedIteratedCertificate

/-! ## Running a plan -/

/-- Every plan runs: each stage's restriction is generated by the consistent
counting theorem, and the plan's `next` function supplies the following stage's
view of the generated rewritten formula. -/
theorem generatedIteratedCertificate_exists {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat} (P : GeneratedCollapsePlan n base F d) :
    Nonempty (GeneratedIteratedCertificate n base F d) := by
  induction P with
  | done base F => exact ⟨.done base F⟩
  | step I _next ih =>
      obtain ⟨C, hcons⟩ := generatedConsistentOneStep_exists I
      obtain ⟨rest⟩ := ih C hcons
      exact ⟨.step I C hcons rest⟩

/-! ## The final generated iterated-collapse theorem -/

/-- **Gate B / B4: the final generated iterated-collapse theorem
(plan-supplied per-stage views; see the HONEST SCOPE STATEMENT above).**  For
any generated collapse plan — which supplies each stage's layered view and
consistent-subspace counting hypothesis — of positive depth rooted at `F` over
the free base,
there is an iterated certificate whose stage restrictions are counting-generated
(one per stage, star counts pinned), sequentially consistent, and composed
first-wins into a single restriction that always has a total extension; on every
assignment agreeing with the composed restriction, the final rewritten formula
evaluates exactly as (the fully restricted) `F`; every stage output satisfies
the per-stage depth and size accounting; and the last stage's combined decision
tree computes the final rewritten formula on all assignments with depth at most
`m_last * (s_last - 1)`. -/
theorem generatedIteratedCollapse {n d : Nat} {F : BDFormula n}
    (P : GeneratedCollapsePlan n (freeRestriction n) F d) (hd : 0 < d) :
    ∃ cert : GeneratedIteratedCertificate n (freeRestriction n) F d,
      cert.stageRestrictions.length = d ∧
      ConsistentSeq (freeRestriction n) cert.stageRestrictions ∧
      cert.finalComposed =
        cert.stageRestrictions.foldl compose (freeRestriction n) ∧
      List.Forall₂ (fun (ρ : Restriction n) (ℓ : Nat) =>
          ρ ∈ restrictionsWithStars n ℓ)
        cert.stageRestrictions cert.stageStarCounts ∧
      (∃ a : Assignment n, Agree cert.finalComposed a) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        ∀ ρ ∈ cert.stageRestrictions, Agree ρ a) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        eval a cert.finalFormula = eval a (restrict cert.finalComposed F)) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        eval a cert.finalFormula = eval a F) ∧
      List.Forall₂ (fun (out : BDFormula n) (s : Nat) =>
          depth out ≤ 1 + (2 * (s - 1) + 1))
        cert.stageOutputs cert.stageBudgets ∧
      List.Forall₂ (fun (out : BDFormula n) (p : Nat × Nat) =>
          formulaSize out ≤ 1 + p.1 * (6 * 2 ^ (p.2 - 1)))
        cert.stageOutputs (cert.stageGateCounts.zip cert.stageBudgets) ∧
      ∃ (T : DTree n) (m s : Nat),
        cert.lastStage = some (T, m, s) ∧
        (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
        dtDepth T ≤ m * (s - 1) ∧
        (∀ a : Assignment n, Agree cert.finalComposed a →
          dtEval a T = eval a (restrict cert.finalComposed F)) := by
  obtain ⟨cert⟩ := generatedIteratedCertificate_exists P
  have hsome := lastStage_isSome cert hd
  cases hlast : cert.lastStage with
  | none => rw [hlast] at hsome; simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      refine ⟨cert, stageRestrictions_length cert,
        stageRestrictions_consistentSeq cert,
        finalComposed_eq_foldl cert, stageRestrictions_stars cert,
        finalComposed_extension cert, agree_finalComposed_stages cert,
        finalFormula_restrict_eval cert, finalFormula_eval cert,
        stageOutputs_depth cert, stageOutputs_size cert,
        T, m, s, hlast, heval, hdepth, ?_⟩
      intro a ha
      rw [heval a, finalFormula_restrict_eval cert a ha]

/-! ## Concrete non-vacuity -/

/-- The B3 singleton empty-DNF `or` layer as a consistent stage input over the
free base (the consistent subspace IS the full star space there). -/
def singletonEmptyDNFOrConsistentInput (n : Nat) (hn : 1 ≤ n) :
    GeneratedConsistentStepInput n (freeRestriction n) where
  layer := {
    parent := ParentKind.or
    gates := [GateSpec.dnf (BDFormula.or []) (emptyGateView n)]
  }
  w := 0
  s := 1
  ℓ := 1
  width := by
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [GateSpec.theDNF, emptyGateView]
  beat := by
    rw [consistentSubspace_freeRestriction]
    have hpos : 0 < (restrictionsWithStars n 1).card :=
      Finset.card_pos.mpr (restrictionsWithStars_nonempty hn)
    simpa using hpos

/-- A depth-`1` plan with a NONEMPTY bottom layer: the B3 singleton gate. -/
def singletonPlan (n : Nat) (hn : 1 ≤ n) :
    GeneratedCollapsePlan n (freeRestriction n)
      (singletonEmptyDNFOrConsistentInput n hn).layer.originalFormula 1 :=
  .step (singletonEmptyDNFOrConsistentInput n hn) (fun _C _hcons => .done _ _)

/-- Non-vacuity of the final theorem at a depth-`1` plan with one bottom gate. -/
theorem generatedIteratedCollapse_singleton_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    ∃ cert : GeneratedIteratedCertificate n (freeRestriction n)
        (singletonEmptyDNFOrConsistentInput n hn).layer.originalFormula 1,
      cert.stageRestrictions.length = 1 ∧
      (∃ a : Assignment n, Agree cert.finalComposed a) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        eval a cert.finalFormula = eval a (restrict cert.finalComposed
          (singletonEmptyDNFOrConsistentInput n hn).layer.originalFormula)) := by
  obtain ⟨cert, hlen, _hseq, _hfold, _hstars, hext, _hagree, hrestrict, _hevalF,
    _hdepth, _hsize, _htree⟩ :=
    generatedIteratedCollapse (singletonPlan n hn) (by omega)
  exact ⟨cert, hlen, hext, hrestrict⟩

/-- An empty `or` layer over ANY base restriction (zero bottom gates, so the
beat is just nonemptiness of the consistent subspace). -/
def emptyOrLayerConsistentInput (n : Nat) (hn : 1 ≤ n) (base : Restriction n) :
    GeneratedConsistentStepInput n base where
  layer := { parent := ParentKind.or, gates := [] }
  w := 0
  s := 1
  ℓ := 1
  width := by
    intro g hg
    exact absurd hg (List.not_mem_nil g)
  beat := by
    have hpos : 0 < (consistentSubspace base 1).card :=
      Finset.card_pos.mpr (consistentSubspace_nonempty base hn)
    simpa using hpos

/-- A structurally iterated (depth-`2`) plan with degenerate EMPTY gate lists:
two generated stages, the second stage's beat stated against the subspace
consistent with the first generated restriction.  This witnesses the iterated
route shape, not gate collapse. -/
def emptyTwoStagePlan (n : Nat) (hn : 1 ≤ n) :
    GeneratedCollapsePlan n (freeRestriction n)
      (BDFormula.or ([] : List (BDFormula n))) 2 :=
  .step (emptyOrLayerConsistentInput n hn (freeRestriction n))
    (fun C _hcons =>
      .step (emptyOrLayerConsistentInput n hn (compose (freeRestriction n) C.ρ))
        (fun _C' _hcons' => .done _ _))

/-- Non-vacuity of the final theorem at a structurally iterated depth-`2` plan
(degenerate empty gate lists; witnesses the iterated route shape, not gate
collapse): two counting-generated, sequentially consistent restrictions are
produced and composed, and the final semantics hold on the (existing) common
extensions. -/
theorem generatedIteratedCollapse_twoStage_nonvacuous (n : Nat) (hn : 1 ≤ n) :
    ∃ cert : GeneratedIteratedCertificate n (freeRestriction n)
        (BDFormula.or ([] : List (BDFormula n))) 2,
      cert.stageRestrictions.length = 2 ∧
      ConsistentSeq (freeRestriction n) cert.stageRestrictions ∧
      (∃ a : Assignment n, Agree cert.finalComposed a) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        eval a cert.finalFormula =
          eval a (BDFormula.or ([] : List (BDFormula n)))) := by
  obtain ⟨cert, hlen, hseq, _hfold, _hstars, hext, _hagree, _hrestrict, hevalF,
    _hdepth, _hsize, _htree⟩ :=
    generatedIteratedCollapse (emptyTwoStagePlan n hn) (by omega)
  exact ⟨cert, hlen, hseq, hext, hevalF⟩

end GeneratedIteratedCollapseFinal
end PvNP
