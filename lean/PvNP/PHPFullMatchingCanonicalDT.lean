import PvNP.PHPFullMatchingDNFBound
import PvNP.SwitchingTermCanonicalDT

/-!
# Canonical decision-tree skeleton for restricted PHP DNFs

This module connects the full-square matching PHP DNF surface from
`PHPFullMatchingDNFBound` to the existing deterministic term-canonical DNF
decision tree from `SwitchingTermCanonicalDT`.

It proves only a structural skeleton:

* `phpDNFAsDNF` translates the PHP DNF list representation into the generic
  `DNF (Nat.succ (h * h))` representation.
* `canonicalRestrictedDNFTree h tvs P` is the term-canonical tree of the DNF
  after applying the full matching restriction `fullRestrictionOf P`.
* `canonicalRestrictedDNFTree_correct` proves that this tree computes the
  restricted bounded-depth formula under assignments agreeing with the
  restriction.
* `treeVarsIn_canonicalRestrictedDNFTree` proves that every decision-node
  variable queried by the tree is one of the original PHP DNF literal
  variables.
* `canonicalRestrictedDNFTree_depth_le_total` and
  `canonicalRestrictedDNFTree_path_length_le_total` give the deterministic
  worst-case depth/path bound by the total literal-occurrence count
  `tvs.join.length`.

HONEST SCOPE STATEMENT: this is deterministic infrastructure only.  It is not
a PHP switching lemma, not a collapse-probability bound, not a bad-set
encoding/counting argument, not a rectangular `p > h` result, not a Frege/PHP
lower bound, not an NP/circuit lower bound, and not a P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingCanonicalDT

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPBooleanDepthFloor
open PHPFullMatchingDistribution
open PHPFullMatchingCollapseBound
open PHPFullMatchingDNFBound
open BoundedDepthCanonicalDT
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT

/-! ## PHP DNF as the generic DNF representation -/

/-- Translate one PHP literal datum into the generic `Literal` type. -/
def phpLit (h : Nat) (e : Fin h × Fin h × Bool) :
    Literal (Nat.succ (h * h)) :=
  { var := phpVar h h e.1 e.2.1, sign := e.2.2 }

/-- Translate one PHP term into the generic DNF-term representation. -/
def phpTermAsTerm (h : Nat) (tv : List (Fin h × Fin h × Bool)) :
    Term (Nat.succ (h * h)) :=
  tv.map (phpLit h)

/-- Translate a PHP DNF list into the generic `DNF` representation. -/
def phpDNFAsDNF (h : Nat) (tvs : List (List (Fin h × Fin h × Bool))) :
    DNF (Nat.succ (h * h)) :=
  tvs.map (phpTermAsTerm h)

/-- The finite set of variable indices appearing in the original PHP DNF,
with duplicate literal occurrences collapsed by `toFinset`. -/
def phpDNFVarSet (h : Nat) (tvs : List (List (Fin h × Fin h × Bool))) :
    Finset (Fin (Nat.succ (h * h))) :=
  (tvs.join.map (fun e => phpVar h h e.1 e.2.1)).toFinset

theorem eval_phpTermLit_eq_litEval {h : Nat}
    (a : Assignment (Nat.succ (h * h))) (e : Fin h × Fin h × Bool) :
    eval a (phpTermLit h e) = litEval a (phpLit h e) := by
  unfold phpTermLit phpLit
  rw [eval_lit]

/-- The generic term semantics and the existing bounded-depth PHP term formula
semantics agree. -/
theorem eval_phpTermFormula_eq_termEval {h : Nat}
    (a : Assignment (Nat.succ (h * h)))
    (tv : List (Fin h × Fin h × Bool)) :
    eval a (phpTermFormula h tv) = termEval a (phpTermAsTerm h tv) := by
  unfold phpTermFormula phpTermAsTerm termEval
  rw [eval_and]
  induction tv with
  | nil => rfl
  | cons e rest ih =>
      simp [phpLit, phpTermLit, eval_lit, ih]

/-- The generic DNF semantics and the existing bounded-depth PHP DNF formula
semantics agree. -/
theorem eval_phpDNFFormula_eq_dnfEval {h : Nat}
    (a : Assignment (Nat.succ (h * h)))
    (tvs : List (List (Fin h × Fin h × Bool))) :
    eval a (phpDNFFormula h tvs) = dnfEval a (phpDNFAsDNF h tvs) := by
  unfold phpDNFFormula phpDNFAsDNF dnfEval
  rw [eval_or]
  induction tvs with
  | nil => rfl
  | cons tv rest ih =>
      simp [eval_phpTermFormula_eq_termEval, ih]

/-- Semantic bridge after a full matching restriction: evaluating the restricted
PHP formula agrees with evaluating the generically restricted DNF. -/
theorem eval_restrict_phpDNFFormula_eq_dnfRestrict {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (a : Assignment (Nat.succ (h * h)))
    (tvs : List (List (Fin h × Fin h × Bool)))
    (ha : Agree (fullRestrictionOf P) a) :
    eval a (restrict (fullRestrictionOf P) (phpDNFFormula h tvs)) =
      dnfEval a (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs)) := by
  calc
    eval a (restrict (fullRestrictionOf P) (phpDNFFormula h tvs))
        = eval a (phpDNFFormula h tvs) := by
          exact eval_restrict (fullRestrictionOf P) a (phpDNFFormula h tvs) ha
    _ = dnfEval a (phpDNFAsDNF h tvs) := by
          exact eval_phpDNFFormula_eq_dnfEval a tvs
    _ = dnfEval a (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs)) := by
          exact (dnfEval_dnfRestrict (fullRestrictionOf P) a ha
            (phpDNFAsDNF h tvs)).symm

/-! ## The restricted canonical tree and semantic correctness -/

/-- The deterministic term-canonical decision tree of the PHP DNF after the
full matching restriction `P`. -/
def canonicalRestrictedDNFTree (h : Nat)
    (tvs : List (List (Fin h × Fin h × Bool)))
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    DTree (Nat.succ (h * h)) :=
  termCanonicalDT (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs))

/-- The restricted canonical tree computes the restricted PHP DNF formula under
every assignment that agrees with the full matching restriction. -/
theorem canonicalRestrictedDNFTree_correct {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool)))
    (a : Assignment (Nat.succ (h * h)))
    (ha : Agree (fullRestrictionOf P) a) :
    dtEval a (canonicalRestrictedDNFTree h tvs P) =
      eval a (restrict (fullRestrictionOf P) (phpDNFFormula h tvs)) := by
  unfold canonicalRestrictedDNFTree
  rw [dtEval_termCanonicalDT]
  exact (eval_restrict_phpDNFFormula_eq_dnfRestrict P a tvs ha).symm

/-! ## Query-variable containment -/

/-- Every decision-node variable of a tree is contained in the finite support
set `S`. -/
def TreeVarsIn {n : Nat} : DTree n -> Finset (Fin n) -> Prop
  | .leaf _, _ => True
  | .node v t0 t1, S => v ∈ S ∧ TreeVarsIn t0 S ∧ TreeVarsIn t1 S

/-- Every variable of a DNF is contained in `S`. -/
def DNFVarsIn {n : Nat} (D : DNF n) (S : Finset (Fin n)) : Prop :=
  forall t, t ∈ D -> forall l, l ∈ t -> l.var ∈ S

theorem termRestrict_mem_of_mem {n : Nat} (rho : Restriction n) :
    forall (t t' : Term n), termRestrict rho t = some t' ->
      forall l, l ∈ t' -> l ∈ t
  | [], t', h, l, hl => by
      simp only [termRestrict, Option.some.injEq] at h
      subst h
      exact absurd hl (List.not_mem_nil l)
  | m :: t, t', h, l, hl => by
      simp only [termRestrict] at h
      cases hrho : rho m.var with
      | none =>
          simp only [hrho] at h
          cases hrec : termRestrict rho t with
          | some t'' =>
              simp only [hrec, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hl with hhead | htail
              · subst hhead
                exact List.mem_cons_self l t
              · exact List.mem_cons_of_mem m
                  (termRestrict_mem_of_mem rho t t'' hrec l htail)
          | none =>
              simp only [hrec] at h
              exact absurd h (by simp)
      | some b =>
          simp only [hrho] at h
          by_cases hb : b = m.sign
          · simp only [if_pos hb] at h
            exact List.mem_cons_of_mem m
              (termRestrict_mem_of_mem rho t t' h l hl)
          · simp only [if_neg hb] at h
            exact absurd h (by simp)

theorem dnfVarsIn_assignVar {n : Nat} {D : DNF n} {S : Finset (Fin n)}
    (hD : DNFVarsIn D S) (v : Fin n) (b : Bool) :
    DNFVarsIn (assignVar v b D) S := by
  intro t ht l hl
  unfold assignVar at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, ht0, hres⟩ := ht
  exact hD t0 ht0 l (assignTerm_mem_of_mem v b t0 t hres l hl)

theorem dnfVarsIn_dnfRestrict {n : Nat} {D : DNF n} {S : Finset (Fin n)}
    (hD : DNFVarsIn D S) (rho : Restriction n) :
    DNFVarsIn (dnfRestrict rho D) S := by
  intro t ht l hl
  unfold dnfRestrict at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, ht0, hres⟩ := ht
  exact hD t0 ht0 l (termRestrict_mem_of_mem rho t0 t hres l hl)

mutual
theorem treeVarsIn_queryTerm {n : Nat} {S : Finset (Fin n)} :
    forall (vars : Term n) (D : DNF n),
      (forall l, l ∈ vars -> l.var ∈ S) ->
      DNFVarsIn D S ->
      TreeVarsIn (queryTerm vars D) S
  | [], D, _hvars, hD => by
      rw [queryTerm_nil]
      exact treeVarsIn_termCanonicalDT D hD
  | l :: vs, D, hvars, hD => by
      rw [queryTerm_cons]
      refine ⟨hvars l (List.mem_cons_self l vs), ?_, ?_⟩
      · exact treeVarsIn_queryTerm vs (assignVar l.var false D)
          (fun m hm => hvars m (List.mem_cons_of_mem l hm))
          (dnfVarsIn_assignVar hD l.var false)
      · exact treeVarsIn_queryTerm vs (assignVar l.var true D)
          (fun m hm => hvars m (List.mem_cons_of_mem l hm))
          (dnfVarsIn_assignVar hD l.var true)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

theorem treeVarsIn_termCanonicalDT {n : Nat} {S : Finset (Fin n)} :
    forall (D : DNF n), DNFVarsIn D S -> TreeVarsIn (termCanonicalDT D) S
  | [], _hD => by simp [termCanonicalDT, TreeVarsIn]
  | [] :: _, _hD => by simp [termCanonicalDT, TreeVarsIn]
  | (l :: t) :: D, hD => by
      rw [termCanonicalDT_cons_cons]
      have hterm : forall m, m ∈ (l :: t) -> m.var ∈ S :=
        fun m hm => hD (l :: t) (List.mem_cons_self _ _) m hm
      refine ⟨hterm l (List.mem_cons_self l t), ?_, ?_⟩
      · exact treeVarsIn_queryTerm t
          (assignVar l.var false ((l :: t) :: D))
          (fun m hm => hterm m (List.mem_cons_of_mem l hm))
          (dnfVarsIn_assignVar hD l.var false)
      · exact treeVarsIn_queryTerm t
          (assignVar l.var true ((l :: t) :: D))
          (fun m hm => hterm m (List.mem_cons_of_mem l hm))
          (dnfVarsIn_assignVar hD l.var true)
  termination_by D => (dnfSize D, 0)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
end

theorem dnfVarsIn_phpDNFAsDNF {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    DNFVarsIn (phpDNFAsDNF h tvs) (phpDNFVarSet h tvs) := by
  intro t ht l hl
  unfold phpDNFAsDNF at ht
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp ht
  unfold phpTermAsTerm at hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
  unfold phpLit phpDNFVarSet
  rw [List.mem_toFinset]
  exact List.mem_map.mpr
    ⟨e, List.mem_join.mpr ⟨tv, htv, he⟩, rfl⟩

/-- Every variable queried anywhere in the restricted canonical tree is one of
the variables appearing in the original PHP DNF. -/
theorem treeVarsIn_canonicalRestrictedDNFTree {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool))) :
    TreeVarsIn (canonicalRestrictedDNFTree h tvs P) (phpDNFVarSet h tvs) := by
  unfold canonicalRestrictedDNFTree
  exact treeVarsIn_termCanonicalDT
    (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs))
    (dnfVarsIn_dnfRestrict (dnfVarsIn_phpDNFAsDNF tvs) (fullRestrictionOf P))

/-! ## Deterministic depth and path-length bounds -/

theorem length_phpTermAsTerm {h : Nat} (tv : List (Fin h × Fin h × Bool)) :
    (phpTermAsTerm h tv).length = tv.length := by
  unfold phpTermAsTerm
  rw [List.length_map]

/-- Length of a flattened list of lists, in the form used by `dnfSize`. -/
theorem list_join_length_eq_sum_lengths {α : Type _} :
    forall L : List (List α), L.join.length = (L.map List.length).sum
  | [] => rfl
  | x :: xs => by
      simp [list_join_length_eq_sum_lengths xs]

theorem dnfSize_phpDNFAsDNF_sum {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    dnfSize (phpDNFAsDNF h tvs) = (tvs.map List.length).sum := by
  induction tvs with
  | nil =>
      rfl
  | cons tv rest ih =>
      change (phpTermAsTerm h tv).length + dnfSize (phpDNFAsDNF h rest) =
        tv.length + (rest.map List.length).sum
      rw [length_phpTermAsTerm, ih]

theorem dnfSize_phpDNFAsDNF {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    dnfSize (phpDNFAsDNF h tvs) = tvs.join.length := by
  rw [dnfSize_phpDNFAsDNF_sum, list_join_length_eq_sum_lengths]

theorem dnfSize_dnfRestrict_le {n : Nat} (rho : Restriction n) :
    forall D : DNF n, dnfSize (dnfRestrict rho D) <= dnfSize D
  | [] => by simp [dnfRestrict]
  | t :: D => by
      rw [show dnfRestrict rho (t :: D)
            = (match termRestrict rho t with
                | some t' => t' :: dnfRestrict rho D
                | none => dnfRestrict rho D) by
            simp only [dnfRestrict, List.filterMap_cons]
            cases termRestrict rho t <;> rfl]
      cases hrec : termRestrict rho t with
      | some t' =>
          simp only [hrec, dnfSize_cons]
          have hlen := length_termRestrict_le rho t t' hrec
          have htail := dnfSize_dnfRestrict_le rho D
          omega
      | none =>
          simp only [hrec, dnfSize_cons]
          have htail := dnfSize_dnfRestrict_le rho D
          omega

/-- The restricted canonical tree has depth at most the size of the restricted
generic DNF. -/
theorem canonicalRestrictedDNFTree_depth_le_restricted_size {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool))) :
    dtDepth (canonicalRestrictedDNFTree h tvs P) <=
      dnfSize (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs)) := by
  unfold canonicalRestrictedDNFTree
  exact dtDepth_termCanonicalDT_le _

/-- Deterministic worst-case depth bound: the restricted canonical tree has
depth at most the total number of literal occurrences in the original PHP DNF.
This is not a probabilistic or geometric bound. -/
theorem canonicalRestrictedDNFTree_depth_le_total {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool))) :
    dtDepth (canonicalRestrictedDNFTree h tvs P) <= tvs.join.length := by
  calc
    dtDepth (canonicalRestrictedDNFTree h tvs P)
        <= dnfSize (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs)) := by
          exact canonicalRestrictedDNFTree_depth_le_restricted_size P tvs
    _ <= dnfSize (phpDNFAsDNF h tvs) := by
          exact dnfSize_dnfRestrict_le (fullRestrictionOf P) (phpDNFAsDNF h tvs)
    _ = tvs.join.length := by
          exact dnfSize_phpDNFAsDNF tvs

/-- Every assignment path through the restricted canonical tree has at most the
original total literal-occurrence count many queries. -/
theorem canonicalRestrictedDNFTree_path_length_le_total {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool)))
    (a : Assignment (Nat.succ (h * h))) :
    (dtPathVars a (canonicalRestrictedDNFTree h tvs P)).length <=
      tvs.join.length := by
  exact Nat.le_trans
    (dtPathVars_length_le_depth a (canonicalRestrictedDNFTree h tvs P))
    (canonicalRestrictedDNFTree_depth_le_total P tvs)

end PHPFullMatchingCanonicalDT
end PvNP
