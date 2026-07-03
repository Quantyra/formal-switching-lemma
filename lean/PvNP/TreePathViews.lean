import PvNP.GeneratedOneStepDepthReduction

/-!
# General tree-to-DNF/CNF re-viewing (path DNFs with built-in pruning)

Every decision tree re-views as a simple DNF (its accepted paths) and a simple
CNF (dually, via `notTree`), with width bounded by the TREE DEPTH:

* `treePathDNF` walks the tree carrying a context restriction of the variables
  already queried on the current path; re-queried variables are pruned by
  following the recorded branch, so every emitted path term automatically has
  pairwise-distinct variables (simplicity is structural, not an assumption);
* `treeDNFView : DNFView (treeToFormula T)` with
  `widthDNF (treeDNFView T).D ≤ dtDepth T`;
* `treeCNFView : CNFView (treeToFormula T)` by dualizing the path DNF of
  `notTree T`, with `widthDNF (cnfDualDNF (treeCNFView T).C) ≤ dtDepth T`.

This is the general re-viewing that the depth-`≤ 1` special case
(`RefinedTwoStageInstance.depthOneDNFView`) previewed: generated stage trees can
now be re-viewed as next-stage gates.  This removes the representation-layer
blocker for deeper generated trees, but does not by itself close frozen-form B4
or prove automatic many-round iteration.

## HONEST SCOPE STATEMENT (read this)

* Representation-layer conversion only: no counting, no probability, no lower
  bound.  Frozen-form B4 remains OPEN.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.
  Gate A rung 4 remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace TreePathViews

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement

/-! ## Boolean bookkeeping -/

theorem termEval_append {n : Nat} (a : Assignment n) (s t : Term n) :
    termEval a (s ++ t) = (termEval a s && termEval a t) := by
  simp [termEval, List.all_append]

theorem termEval_reverse {n : Nat} (a : Assignment n) (t : Term n) :
    termEval a t.reverse = termEval a t := by
  simp [termEval, List.all_reverse]

theorem dnfEval_append {n : Nat} (a : Assignment n) (D1 D2 : DNF n) :
    dnfEval a (D1 ++ D2) = (dnfEval a D1 || dnfEval a D2) := by
  simp [dnfEval, List.any_append]

/-! ## The pruning path walk -/

/-- Update a restriction at one variable. -/
def updateR {n : Nat} (ρ : Restriction n) (v : Fin n) (b : Bool) :
    Restriction n :=
  fun u => if u = v then some b else ρ u

theorem updateR_self {n : Nat} (ρ : Restriction n) (v : Fin n) (b : Bool) :
    updateR ρ v b v = some b := by
  simp [updateR]

theorem updateR_other {n : Nat} (ρ : Restriction n) (v u : Fin n) (b : Bool)
    (h : u ≠ v) : updateR ρ v b u = ρ u := by
  simp [updateR, h]

theorem agree_updateR {n : Nat} {ρ : Restriction n} {a : Assignment n}
    (h : Agree ρ a) (v : Fin n) (hv : ρ v = none) :
    Agree (updateR ρ v (a v)) a := by
  intro u b hu
  by_cases huv : u = v
  · subst huv
    rw [updateR_self] at hu
    exact Option.some.inj hu
  · rw [updateR_other ρ v u _ huv] at hu
    exact h u b hu

/-- Collect the accepted paths of a tree as a DNF, pruning re-queried
variables against the context restriction `ρ` and accumulating the current
path literals in `acc` (in reverse order). -/
def treePathDNF {n : Nat} : DTree n → Restriction n → Term n → DNF n
  | .leaf true, _, acc => [acc.reverse]
  | .leaf false, _, _ => []
  | .node v t0 t1, ρ, acc =>
      match ρ v with
      | some false => treePathDNF t0 ρ acc
      | some true => treePathDNF t1 ρ acc
      | none =>
          treePathDNF t0 (updateR ρ v false) (⟨v, false⟩ :: acc) ++
          treePathDNF t1 (updateR ρ v true) (⟨v, true⟩ :: acc)

/-- Every emitted term extends the accumulated path prefix. -/
theorem treePathDNF_shape {n : Nat} :
    ∀ (T : DTree n) (ρ : Restriction n) (acc t : Term n),
      t ∈ treePathDNF T ρ acc → ∃ ext : Term n, t = acc.reverse ++ ext := by
  intro T
  induction T with
  | leaf b =>
      intro ρ acc t ht
      cases b with
      | false => cases ht
      | true =>
          rw [show treePathDNF (.leaf true) ρ acc = [acc.reverse] from rfl] at ht
          rw [List.mem_singleton] at ht
          subst ht
          exact ⟨[], (List.append_nil _).symm⟩
  | node v t0 t1 ih0 ih1 =>
      intro ρ acc t ht
      rw [show treePathDNF (.node v t0 t1) ρ acc
            = (match ρ v with
                | some false => treePathDNF t0 ρ acc
                | some true => treePathDNF t1 ρ acc
                | none =>
                    treePathDNF t0 (updateR ρ v false) (⟨v, false⟩ :: acc) ++
                    treePathDNF t1 (updateR ρ v true) (⟨v, true⟩ :: acc))
          from rfl] at ht
      cases hv : ρ v with
      | some b =>
          rw [hv] at ht
          cases b with
          | false => exact ih0 ρ acc t ht
          | true => exact ih1 ρ acc t ht
      | none =>
          rw [hv] at ht
          rw [List.mem_append] at ht
          rcases ht with ht | ht
          · obtain ⟨ext, hext⟩ :=
              ih0 (updateR ρ v false) (⟨v, false⟩ :: acc) t ht
            refine ⟨⟨v, false⟩ :: ext, ?_⟩
            rw [hext, List.reverse_cons, List.append_assoc,
              List.singleton_append]
          · obtain ⟨ext, hext⟩ :=
              ih1 (updateR ρ v true) (⟨v, true⟩ :: acc) t ht
            refine ⟨⟨v, true⟩ :: ext, ?_⟩
            rw [hext, List.reverse_cons, List.append_assoc,
              List.singleton_append]

/-- A falsified path prefix kills every emitted term. -/
theorem dnfEval_treePathDNF_of_acc_false {n : Nat} (T : DTree n)
    (ρ : Restriction n) (acc : Term n) (a : Assignment n)
    (hacc : termEval a acc = false) :
    dnfEval a (treePathDNF T ρ acc) = false := by
  rw [show dnfEval a (treePathDNF T ρ acc)
        = (treePathDNF T ρ acc).any (fun t => termEval a t) from rfl]
  rw [List.any_eq_false]
  intro t ht
  obtain ⟨ext, hext⟩ := treePathDNF_shape T ρ acc t ht
  subst hext
  simp [termEval_append, termEval_reverse, hacc]

/-- **Path-DNF semantics.**  Under any assignment agreeing with the context,
the collected DNF evaluates to the path prefix conjoined with the tree. -/
theorem dnfEval_treePathDNF {n : Nat} :
    ∀ (T : DTree n) (ρ : Restriction n) (acc : Term n) (a : Assignment n),
      Agree ρ a →
      dnfEval a (treePathDNF T ρ acc) = (termEval a acc && dtEval a T) := by
  intro T
  induction T with
  | leaf b =>
      intro ρ acc a _
      cases b with
      | false => simp [treePathDNF, dnfEval]
      | true =>
          rw [show treePathDNF (.leaf true) ρ acc = [acc.reverse] from rfl]
          simp [dnfEval, termEval_reverse]
  | node v t0 t1 ih0 ih1 =>
      intro ρ acc a ha
      rw [show treePathDNF (.node v t0 t1) ρ acc
            = (match ρ v with
                | some false => treePathDNF t0 ρ acc
                | some true => treePathDNF t1 ρ acc
                | none =>
                    treePathDNF t0 (updateR ρ v false) (⟨v, false⟩ :: acc) ++
                    treePathDNF t1 (updateR ρ v true) (⟨v, true⟩ :: acc))
          from rfl]
      cases hv : ρ v with
      | some b =>
          have hav : a v = b := ha v b hv
          cases b with
          | false =>
              rw [ih0 ρ acc a ha, dtEval_node, hav]
              simp
          | true =>
              rw [ih1 ρ acc a ha, dtEval_node, hav]
              simp
      | none =>
          rw [dnfEval_append]
          cases hav : a v with
          | false =>
              have ha0 : Agree (updateR ρ v false) a := by
                have := agree_updateR ha v hv
                rw [hav] at this
                exact this
              rw [ih0 (updateR ρ v false) (⟨v, false⟩ :: acc) a ha0]
              have hkill : termEval a (⟨v, true⟩ :: acc) = false := by
                simp [termEval, litEval, hav]
              rw [dnfEval_treePathDNF_of_acc_false t1 _ _ a hkill]
              rw [dtEval_node, hav]
              simp [termEval, litEval, hav, Bool.and_assoc]
          | true =>
              have ha1 : Agree (updateR ρ v true) a := by
                have := agree_updateR ha v hv
                rw [hav] at this
                exact this
              rw [ih1 (updateR ρ v true) (⟨v, true⟩ :: acc) a ha1]
              have hkill : termEval a (⟨v, false⟩ :: acc) = false := by
                simp [termEval, litEval, hav]
              rw [dnfEval_treePathDNF_of_acc_false t0 _ _ a hkill]
              rw [dtEval_node, hav]
              simp [termEval, litEval, hav, Bool.and_assoc]

/-! ## Simplicity (structural, from pruning) -/

/-- The accumulated path literals are fixed by the context. -/
def AccFixed {n : Nat} (ρ : Restriction n) (acc : Term n) : Prop :=
  ∀ l ∈ acc, ρ l.var = some l.sign

theorem treePathDNF_simple {n : Nat} :
    ∀ (T : DTree n) (ρ : Restriction n) (acc : Term n),
      (acc.map (·.var)).Nodup → AccFixed ρ acc →
      SimpleDNF (treePathDNF T ρ acc) := by
  intro T
  induction T with
  | leaf b =>
      intro ρ acc hnodup _ t ht
      cases b with
      | false => cases ht
      | true =>
          rw [show treePathDNF (.leaf true) ρ acc = [acc.reverse] from rfl,
            List.mem_singleton] at ht
          subst ht
          show ((acc.reverse).map (·.var)).Nodup
          rw [List.map_reverse]
          exact List.nodup_reverse.mpr hnodup
  | node v t0 t1 ih0 ih1 =>
      intro ρ acc hnodup hfixed t ht
      rw [show treePathDNF (.node v t0 t1) ρ acc
            = (match ρ v with
                | some false => treePathDNF t0 ρ acc
                | some true => treePathDNF t1 ρ acc
                | none =>
                    treePathDNF t0 (updateR ρ v false) (⟨v, false⟩ :: acc) ++
                    treePathDNF t1 (updateR ρ v true) (⟨v, true⟩ :: acc))
          from rfl] at ht
      cases hv : ρ v with
      | some b =>
          rw [hv] at ht
          cases b with
          | false => exact ih0 ρ acc hnodup hfixed t ht
          | true => exact ih1 ρ acc hnodup hfixed t ht
      | none =>
          rw [hv, List.mem_append] at ht
          have hvfresh : v ∉ acc.map (·.var) := by
            intro hcontra
            rw [List.mem_map] at hcontra
            obtain ⟨l, hl, hlv⟩ := hcontra
            have := hfixed l hl
            rw [hlv, hv] at this
            cases this
          rcases ht with ht | ht
          · refine ih0 (updateR ρ v false) (⟨v, false⟩ :: acc) ?_ ?_ t ht
            · exact List.Nodup.cons hvfresh hnodup
            · intro l hl
              rcases List.mem_cons.mp hl with rfl | hl
              · exact updateR_self ρ v false
              · have hne : l.var ≠ v := by
                  intro hcontra
                  exact hvfresh (List.mem_map.mpr ⟨l, hl, hcontra⟩)
                rw [updateR_other ρ v l.var false hne]
                exact hfixed l hl
          · refine ih1 (updateR ρ v true) (⟨v, true⟩ :: acc) ?_ ?_ t ht
            · exact List.Nodup.cons hvfresh hnodup
            · intro l hl
              rcases List.mem_cons.mp hl with rfl | hl
              · exact updateR_self ρ v true
              · have hne : l.var ≠ v := by
                  intro hcontra
                  exact hvfresh (List.mem_map.mpr ⟨l, hl, hcontra⟩)
                rw [updateR_other ρ v l.var true hne]
                exact hfixed l hl

/-! ## Width -/

theorem treePathDNF_termWidth_le {n : Nat} :
    ∀ (T : DTree n) (ρ : Restriction n) (acc t : Term n),
      t ∈ treePathDNF T ρ acc → t.length ≤ acc.length + dtDepth T := by
  intro T
  induction T with
  | leaf b =>
      intro ρ acc t ht
      cases b with
      | false => cases ht
      | true =>
          rw [show treePathDNF (.leaf true) ρ acc = [acc.reverse] from rfl,
            List.mem_singleton] at ht
          subst ht
          rw [List.length_reverse]
          omega
  | node v t0 t1 ih0 ih1 =>
      intro ρ acc t ht
      rw [show treePathDNF (.node v t0 t1) ρ acc
            = (match ρ v with
                | some false => treePathDNF t0 ρ acc
                | some true => treePathDNF t1 ρ acc
                | none =>
                    treePathDNF t0 (updateR ρ v false) (⟨v, false⟩ :: acc) ++
                    treePathDNF t1 (updateR ρ v true) (⟨v, true⟩ :: acc))
          from rfl] at ht
      cases hv : ρ v with
      | some b =>
          rw [hv] at ht
          cases b with
          | false =>
              have := ih0 ρ acc t ht
              rw [dtDepth_node]
              omega
          | true =>
              have := ih1 ρ acc t ht
              rw [dtDepth_node]
              omega
      | none =>
          rw [hv, List.mem_append] at ht
          rcases ht with ht | ht
          · have := ih0 (updateR ρ v false) (⟨v, false⟩ :: acc) t ht
            rw [List.length_cons] at this
            rw [dtDepth_node]
            omega
          · have := ih1 (updateR ρ v true) (⟨v, true⟩ :: acc) t ht
            rw [List.length_cons] at this
            rw [dtDepth_node]
            omega

private theorem foldr_max_le_of_all {xs : List Nat} {B : Nat}
    (h : ∀ x ∈ xs, x ≤ B) : xs.foldr Nat.max 0 ≤ B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact (Nat.max_le).2 ⟨h x (List.mem_cons_self x xs),
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

/-! ## The general DNF view -/

/-- The top-level path DNF of a tree (free context, empty path). -/
def treePathDNF₀ {n : Nat} (T : DTree n) : DNF n :=
  treePathDNF T (freeRestriction n) []

theorem dnfEval_treePathDNF₀ {n : Nat} (T : DTree n) (a : Assignment n) :
    dnfEval a (treePathDNF₀ T) = dtEval a T := by
  have h := dnfEval_treePathDNF T (freeRestriction n) [] a
    (agree_freeRestriction a)
  simpa [termEval] using h

theorem treePathDNF₀_simple {n : Nat} (T : DTree n) :
    SimpleDNF (treePathDNF₀ T) := by
  apply treePathDNF_simple T (freeRestriction n) []
  · simp
  · intro l hl
    cases hl

theorem widthDNF_treePathDNF₀_le {n : Nat} (T : DTree n) :
    widthDNF (treePathDNF₀ T) ≤ dtDepth T := by
  rw [widthDNF]
  apply foldr_max_le_of_all
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have := treePathDNF_termWidth_le T (freeRestriction n) [] t ht
  simpa [termWidth] using this

/-- **General tree-to-DNF re-viewing.**  Any decision tree's formula carries a
simple DNF view of width at most the tree depth. -/
def treeDNFView {n : Nat} (T : DTree n) : DNFView (treeToFormula T) where
  D := treePathDNF₀ T
  sem_eq := fun a => by
    rw [eval_treeToFormula]
    exact (dnfEval_treePathDNF₀ T a).symm
  simple := treePathDNF₀_simple T

theorem widthDNF_treeDNFView_le {n : Nat} (T : DTree n) :
    widthDNF (treeDNFView T).D ≤ dtDepth T :=
  widthDNF_treePathDNF₀_le T

/-! ## The general CNF view (via `notTree` duality) -/

theorem clauseEval_clauseDualTerm {n : Nat} (a : Assignment n) (t : Term n) :
    clauseEval a (clauseDualTerm t) = !(termEval a t) := by
  induction t with
  | nil => simp [clauseDualTerm, clauseEval, termEval]
  | cons l t ih =>
      simp only [clauseDualTerm, List.map_cons] at *
      simp only [clauseEval, List.any_cons, termEval, List.all_cons] at *
      rw [litEval_negLit, ih]
      cases hl : litEval a l <;> simp [hl]

theorem cnfEval_map_clauseDualTerm {n : Nat} (a : Assignment n) (D : DNF n) :
    cnfEval a (D.map clauseDualTerm) = !(dnfEval a D) := by
  induction D with
  | nil => simp [cnfEval, dnfEval]
  | cons t D ih =>
      simp only [List.map_cons, cnfEval, List.all_cons, dnfEval,
        List.any_cons] at *
      rw [clauseEval_clauseDualTerm, ih]
      cases termEval a t <;> simp

/-- The general path CNF: dualize the accepted paths of `notTree T`. -/
def treePathCNF₀ {n : Nat} (T : DTree n) :
    BoundedDepthIteratedCollapse.CNF n :=
  (treePathDNF₀ (notTree T)).map clauseDualTerm

theorem cnfEval_treePathCNF₀ {n : Nat} (T : DTree n) (a : Assignment n) :
    cnfEval a (treePathCNF₀ T) = dtEval a T := by
  unfold treePathCNF₀
  rw [cnfEval_map_clauseDualTerm, dnfEval_treePathDNF₀,
    dtEval_notTree, Bool.not_not]

theorem negLit_negLit {n : Nat} (l : Literal n) : negLit (negLit l) = l := by
  cases l with
  | mk v s => simp [negLit]

theorem clauseDualTerm_clauseDualTerm {n : Nat} (t : Term n) :
    clauseDualTerm (clauseDualTerm t) = t := by
  rw [clauseDualTerm, clauseDualTerm, List.map_map]
  rw [show List.map (negLit ∘ negLit) t = List.map id t from
    List.map_congr_left (fun l _ => negLit_negLit l)]
  exact List.map_id t

theorem treePathCNF₀_simple {n : Nat} (T : DTree n) :
    SimpleCNF (treePathCNF₀ T) := by
  intro c hc
  unfold treePathCNF₀ at hc
  rw [List.mem_map] at hc
  obtain ⟨t, ht, rfl⟩ := hc
  show ((clauseDualTerm t).map (·.var)).Nodup
  have hvar : (clauseDualTerm t).map (·.var) = t.map (·.var) := by
    simp [clauseDualTerm, List.map_map, Function.comp_def, negLit]
  rw [hvar]
  exact treePathDNF₀_simple (notTree T) t ht

theorem cnfDualDNF_treePathCNF₀ {n : Nat} (T : DTree n) :
    cnfDualDNF (treePathCNF₀ T) = treePathDNF₀ (notTree T) := by
  unfold treePathCNF₀ cnfDualDNF
  rw [List.map_map]
  rw [show List.map (clauseDualTerm ∘ clauseDualTerm)
        (treePathDNF₀ (notTree T)) = List.map id (treePathDNF₀ (notTree T))
    from List.map_congr_left (fun t _ => clauseDualTerm_clauseDualTerm t)]
  exact List.map_id _

/-- The switching-relevant width of the general CNF view is bounded by the
tree depth. -/
theorem widthDNF_cnfDualDNF_treePathCNF₀_le {n : Nat} (T : DTree n) :
    widthDNF (cnfDualDNF (treePathCNF₀ T)) ≤ dtDepth T := by
  rw [cnfDualDNF_treePathCNF₀]
  have h := widthDNF_treePathDNF₀_le (notTree T)
  rw [dtDepth_notTree] at h
  exact h

/-- **General tree-to-CNF re-viewing.**  Any decision tree's formula carries a
simple CNF view whose dual-DNF width is at most the tree depth. -/
def treeCNFView {n : Nat} (T : DTree n) : CNFView (treeToFormula T) where
  C := treePathCNF₀ T
  sem_eq := fun a => by
    rw [eval_treeToFormula]
    exact (cnfEval_treePathCNF₀ T a).symm
  simple := treePathCNF₀_simple T

end TreePathViews
end PvNP
