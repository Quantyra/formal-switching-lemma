/-
# The Razborov injective encoding for the (term-canonical) switching lemma

This file CONSTRUCTS the Razborov encode/decode for the term-canonical decision
tree and PROVES the injectivity that yields the counting form of the switching
lemma `SwitchingLemmaTerm n`.

We work with the TERM-canonical decision tree `termCanonicalDT` (one block per
term, each block of ≤ `widthDNF D` variables), as required to land the code in
`Fin w` per position.  The bad set is

  `badSetTerm D s ℓ := {ρ : ℓ stars | s ≤ dtDepth (termCanonicalDT (D|ρ))}`.

For each bad `ρ` we read the first `s` decisions of the *deepest path* of
`termCanonicalDT (D|ρ)`; these query `s` variables `Y` that are all FREE in `ρ`
(because `D|ρ` only mentions free variables), and we set them to their path
directions to obtain `σ = encode₁ ρ`, which has exactly `ℓ - s` stars.  The code
`encode₂ ρ : Fin s → Fin w × Bool` records, per touched variable, its position
inside its term block and its path direction.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Anything
not fully closed is isolated as a `def : Prop` (NOT an axiom) and everything
around it is proved green.  NOT a lower bound, NOT P≠NP.
-/
import PvNP.SwitchingTermCanonicalDT
import PvNP.SwitchingDeepPath
import PvNP.SwitchingCardLemma

namespace PvNP
namespace SwitchingEncodeConstruct

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingCardLemma
open Classical

/-! ## 1. The term-canonical bad set and the term switching lemma statement -/

open Classical in
/-- The **term bad set**: restrictions with exactly `ℓ` stars whose restricted DNF
has a *term-canonical* decision tree of depth `≥ s`.  This is the genuine target
of the Razborov encoding (the term-canonical tree gives the `Fin w` code). -/
noncomputable def badSetTerm {n : Nat} (D : DNF n) (s ℓ : Nat) :
    Finset (Restriction n) :=
  (restrictionsWithStars n ℓ).filter
    (fun ρ => s ≤ dtDepth (termCanonicalDT (dnfRestrict ρ D)))

open Classical in
theorem mem_badSetTerm {n : Nat} {D : DNF n} {s ℓ : Nat} (ρ : Restriction n) :
    ρ ∈ badSetTerm D s ℓ ↔
      stars ρ = ℓ ∧ s ≤ dtDepth (termCanonicalDT (dnfRestrict ρ D)) := by
  unfold badSetTerm
  rw [Finset.mem_filter, mem_restrictionsWithStars]

open Classical in
theorem badSetTerm_subset {n : Nat} (D : DNF n) (s ℓ : Nat) :
    badSetTerm D s ℓ ⊆ restrictionsWithStars n ℓ := by
  unfold badSetTerm; exact Finset.filter_subset _ _

/-- The switching lemma in counting form, for the term-canonical tree. -/
def SwitchingLemmaTerm (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat), widthDNF D ≤ w →
    (badSetTerm D s ℓ).card ≤ (restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s

/-! ## 2. The reduction: an injective encoding ⟹ `SwitchingLemmaTerm` -/

/-- The isolated assembly hypothesis for the term version: a width-respecting,
injective Razborov encoding of the term bad set.  Identical shape to
`SwitchingReduction.HasInjectiveEncoding`, but for `badSetTerm`. -/
def HasInjectiveEncodingTerm (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat), widthDNF D ≤ w →
    ∃ enc : Restriction n → Restriction n × (Fin s → Fin w × Bool),
      (∀ ρ ∈ badSetTerm D s ℓ, (enc ρ).1 ∈ restrictionsWithStars n (ℓ - s)) ∧
      Set.InjOn enc ↑(badSetTerm D s ℓ)

/-- **The reduction (PROVED).** An injective Razborov encoding discharges the term
switching lemma, via the injection cardinality backbone and `(2w)^s ≤ (8w)^s`. -/
theorem switchingLemmaTerm_of_hasEncoding {n : Nat}
    (h : HasInjectiveEncodingTerm n) : SwitchingLemmaTerm n := by
  intro D w s ℓ hw
  obtain ⟨enc, hmem, hinj⟩ := h D w s ℓ hw
  have hc : (badSetTerm D s ℓ).card
      ≤ (restrictionsWithStars n (ℓ - s)).card * (2 * w) ^ s :=
    card_le_mul_pow_of_injOn (badSetTerm D s ℓ) (restrictionsWithStars n (ℓ - s))
      w s enc hmem hinj
  refine le_trans hc ?_
  apply Nat.mul_le_mul (le_refl _)
  exact Nat.pow_le_pow_left (by omega) s

/-! ## 3. Restricted DNFs mention only free variables

Every literal surviving `termRestrict ρ t` has `ρ l.var = none` (the only branch
that keeps a literal is the `none` branch).  Hence every variable appearing in
`dnfRestrict ρ D`, and in particular every variable QUERIED by
`termCanonicalDT (dnfRestrict ρ D)` along any path, is a *star* of `ρ`. -/

/-- Every literal surviving `termRestrict ρ t` has a free variable in `ρ`. -/
theorem termRestrict_var_free {n : Nat} (ρ : Restriction n) :
    ∀ (t t' : Term n), termRestrict ρ t = some t' → ∀ l ∈ t', ρ l.var = none
  | [], t', h, l, hl => by
      simp only [termRestrict, Option.some.injEq] at h; subst h
      exact absurd hl (List.not_mem_nil l)
  | (m :: t), t', h, l, hl => by
      simp only [termRestrict] at h
      cases hρ : ρ m.var with
      | none =>
          simp only [hρ] at h
          cases hrec : termRestrict ρ t with
          | some t'' =>
              simp only [hrec, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hl with h' | h'
              · subst h'; exact hρ
              · exact termRestrict_var_free ρ t t'' hrec l h'
          | none => simp only [hrec] at h; exact absurd h (by simp)
      | some b =>
          simp only [hρ] at h
          by_cases hbs : b = m.sign
          · simp only [if_pos hbs] at h
            exact termRestrict_var_free ρ t t' h l hl
          · simp only [if_neg hbs] at h; exact absurd h (by simp)

/-- Every literal appearing in `dnfRestrict ρ D` has a free variable in `ρ`. -/
theorem dnfRestrict_var_free {n : Nat} (ρ : Restriction n) (D : DNF n) :
    ∀ t ∈ dnfRestrict ρ D, ∀ l ∈ t, ρ l.var = none := by
  intro t ht l hl
  unfold dnfRestrict at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, _ht0, hres⟩ := ht
  exact termRestrict_var_free ρ t0 t hres l hl

/-! ### Queried variables of `termCanonicalDT` / `queryTerm` are free

We track the predicate "all variables of `D` satisfy `P`" through the recursion.
`assignVar` never introduces a new variable, so it preserves the predicate; and
the queried head variables are variables of `D`, hence satisfy `P`.  Applied with
`P v := ρ v = none` and `D := dnfRestrict ρ D₀`, every queried variable along any
path of `termCanonicalDT (D|ρ)` is a star of `ρ`. -/

/-- "All variables occurring in `D` satisfy `P`." -/
def AllVars {n : Nat} (P : Fin n → Prop) (D : DNF n) : Prop :=
  ∀ t ∈ D, ∀ l ∈ t, P l.var

/-- `assignVar` preserves `AllVars P` (it never introduces a new variable). -/
theorem allVars_assignVar {n : Nat} {P : Fin n → Prop} {D : DNF n}
    (h : AllVars P D) (v : Fin n) (b : Bool) : AllVars P (assignVar v b D) := by
  intro t ht l hl
  unfold assignVar at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, ht0, hres⟩ := ht
  exact h t0 ht0 l (assignTerm_mem_of_mem v b t0 t hres l hl)

/-! ### Node variables of a tree, and that deep-path vars are node vars

To transfer "all queried variables are free" to the deep path (which is not driven
by an assignment), we use the predicate `NodeVars P t` = "every `node` label of
`t` satisfies `P`".  The deepest path's variables are all node variables; and we
show `termCanonicalDT (D|ρ)` has all node variables free. -/

/-- "Every decision-node variable of the tree `t` satisfies `P`." -/
def NodeVars {n : Nat} (P : Fin n → Prop) : DTree n → Prop
  | .leaf _ => True
  | .node v t0 t1 => P v ∧ NodeVars P t0 ∧ NodeVars P t1

/-- The deepest path queries only node variables of the tree. -/
theorem deepestPath_nodeVars {n : Nat} {P : Fin n → Prop} :
    ∀ (t : DTree n), NodeVars P t → ∀ vd ∈ deepestPath t, P vd.1
  | .leaf _, _, vd, hvd => by simp [deepestPath] at hvd
  | .node v t0 t1, hnode, vd, hvd => by
      obtain ⟨hv, h0, h1⟩ := hnode
      rw [deepestPath] at hvd
      split at hvd
      · rcases List.mem_cons.mp hvd with h | h
        · subst h; exact hv
        · exact deepestPath_nodeVars t1 h1 vd h
      · rcases List.mem_cons.mp hvd with h | h
        · subst h; exact hv
        · exact deepestPath_nodeVars t0 h0 vd h

/-! ### `termCanonicalDT (D)` has all node variables among the variables of `D`

We prove `NodeVars P (termCanonicalDT D)` whenever `AllVars P D`, by the same
recursion.  We need the `queryTerm` companion. -/

mutual
theorem nodeVars_queryTerm {n : Nat} {P : Fin n → Prop} :
    ∀ (vars : Term n) (D : DNF n),
      (∀ l ∈ vars, P l.var) → AllVars P D → NodeVars P (queryTerm vars D)
  | [], D, _hvars, hD => by
      rw [queryTerm_nil]; exact nodeVars_termCanonicalDT D hD
  | l :: vs, D, hvars, hD => by
      rw [queryTerm_cons]
      refine ⟨hvars l (List.mem_cons_self l vs), ?_, ?_⟩
      · exact nodeVars_queryTerm vs (assignVar l.var false D)
          (fun m hm => hvars m (List.mem_cons_of_mem l hm))
          (allVars_assignVar hD l.var false)
      · exact nodeVars_queryTerm vs (assignVar l.var true D)
          (fun m hm => hvars m (List.mem_cons_of_mem l hm))
          (allVars_assignVar hD l.var true)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

theorem nodeVars_termCanonicalDT {n : Nat} {P : Fin n → Prop} :
    ∀ (D : DNF n), AllVars P D → NodeVars P (termCanonicalDT D)
  | [], _hD => by simp [termCanonicalDT, NodeVars]
  | [] :: _, _hD => by simp [termCanonicalDT, NodeVars]
  | (l :: t) :: D, hD => by
      rw [termCanonicalDT_cons_cons]
      have hlt : ∀ m ∈ (l :: t), P m.var :=
        fun m hm => hD (l :: t) (List.mem_cons_self _ _) m hm
      refine ⟨hlt l (List.mem_cons_self l t), ?_, ?_⟩
      · exact nodeVars_queryTerm t (assignVar l.var false ((l :: t) :: D))
          (fun m hm => hlt m (List.mem_cons_of_mem l hm))
          (allVars_assignVar hD l.var false)
      · exact nodeVars_queryTerm t (assignVar l.var true ((l :: t) :: D))
          (fun m hm => hlt m (List.mem_cons_of_mem l hm))
          (allVars_assignVar hD l.var true)
  termination_by D => (dnfSize D, 0)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
end

/-- **Deep-path variables of `termCanonicalDT (D|ρ)` are stars of `ρ`.**
Every variable on the deepest path of the term-canonical tree of the restricted
DNF is free in `ρ`. -/
theorem deepestPath_var_free {n : Nat} (ρ : Restriction n) (D : DNF n) :
    ∀ vd ∈ deepestPath (termCanonicalDT (dnfRestrict ρ D)), ρ vd.1 = none := by
  have hAll : AllVars (fun v => ρ v = none) (dnfRestrict ρ D) :=
    dnfRestrict_var_free ρ D
  exact deepestPath_nodeVars (termCanonicalDT (dnfRestrict ρ D))
    (nodeVars_termCanonicalDT (dnfRestrict ρ D) hAll)

/-! ## 4. Distinctness of the deep-path variables (under `SimpleDNF`)

The deepest path may query a variable twice if a term repeats a variable (e.g. the
DNF `[[x, x]]` queries `x` twice along a dead branch).  Under the standard
hypothesis that every term is a *proper conjunction* — its variables are pairwise
distinct, `SimpleDNF` — this cannot happen: every query removes its variable from
the residual, so it never recurs downstream, and the deep-path variables are
distinct.  Distinctness is what makes the σ-construction fix exactly `s` *new*
variables, giving the exact `ℓ - s` star count. -/

/-- A term is *simple* if its variables are pairwise distinct. -/
def SimpleTerm {n : Nat} (t : Term n) : Prop := (t.map (·.var)).Nodup

/-- A DNF is *simple* if every term is a proper conjunction (distinct variables). -/
def SimpleDNF {n : Nat} (D : DNF n) : Prop := ∀ t ∈ D, SimpleTerm t

/-- `assignTerm` produces a simple term from a simple term (it drops literals, and
a sublist of a `Nodup` list of variables is `Nodup`). -/
theorem simpleTerm_assignTerm {n : Nat} (v : Fin n) (b : Bool)
    (t t' : Term n) (h : assignTerm v b t = some t') (hs : SimpleTerm t) :
    SimpleTerm t' := by
  unfold SimpleTerm at *
  -- t'.map var is a sublist of t.map var via Sublist; Nodup of a sublist holds.
  have hsub : (t'.map (·.var)).Sublist (t.map (·.var)) := by
    have : t'.Sublist t := by
      -- assignTerm only ever keeps original literals in order
      clear hs
      induction t generalizing t' with
      | nil =>
          simp only [assignTerm, Option.some.injEq] at h; subst h; exact List.Sublist.refl _
      | cons l t ih =>
          simp only [assignTerm] at h
          by_cases hlv : l.var = v
          · by_cases hls : l.sign = b
            · simp only [if_pos hlv, if_pos hls] at h
              exact (ih t' h).trans (List.sublist_cons_self l t)
            · simp only [if_pos hlv, if_neg hls] at h; exact absurd h (by simp)
          · simp only [if_neg hlv] at h
            cases hrec : assignTerm v b t with
            | some t'' =>
                simp only [hrec, Option.some.injEq] at h
                subst h
                exact (ih t'' hrec).cons₂ l
            | none => simp only [hrec] at h; exact absurd h (by simp)
    exact this.map (·.var)
  exact hsub.nodup hs

/-- `assignVar` preserves `SimpleDNF`. -/
theorem simpleDNF_assignVar {n : Nat} {D : DNF n} (hD : SimpleDNF D)
    (v : Fin n) (b : Bool) : SimpleDNF (assignVar v b D) := by
  intro t ht
  unfold assignVar at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, ht0, hres⟩ := ht
  exact simpleTerm_assignTerm v b t0 t hres (hD t0 ht0)

/-- `dnfRestrict` preserves `SimpleDNF` (each restricted term is a sublist). -/
theorem simpleDNF_dnfRestrict {n : Nat} {D : DNF n} (hD : SimpleDNF D)
    (ρ : Restriction n) : SimpleDNF (dnfRestrict ρ D) := by
  intro t ht
  unfold dnfRestrict at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, ht0, hres⟩ := ht
  -- termRestrict, like assignTerm, only keeps original literals in order.
  unfold SimpleTerm
  have hsub : t.Sublist t0 := by
    clear ht0
    induction t0 generalizing t with
    | nil =>
        simp only [termRestrict, Option.some.injEq] at hres; subst hres
        exact List.Sublist.refl _
    | cons l t0 ih =>
        simp only [termRestrict] at hres
        cases hρ : ρ l.var with
        | none =>
            simp only [hρ] at hres
            cases hrec : termRestrict ρ t0 with
            | some t'' =>
                simp only [hrec, Option.some.injEq] at hres
                subst hres
                exact (ih t'' hrec).cons₂ l
            | none => simp only [hrec] at hres; exact absurd hres (by simp)
        | some bb =>
            simp only [hρ] at hres
            by_cases hbs : bb = l.sign
            · simp only [if_pos hbs] at hres
              exact (ih t hres).trans (List.sublist_cons_self l t0)
            · simp only [if_neg hbs] at hres; exact absurd hres (by simp)
  have h0 : (t0.map (·.var)).Nodup := hD t0 ht0
  exact (hsub.map (·.var)).nodup h0

/-! ### `AllVars (· ≠ v)` after residualizing by `v` -/

/-- `assignVar v b D` mentions no `v` (every `v`-literal is removed/decided). -/
theorem allVars_ne_assignVar {n : Nat} (v : Fin n) (b : Bool) (D : DNF n) :
    AllVars (fun w => w ≠ v) (assignVar v b D) := by
  intro t ht l hl
  unfold assignVar at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, _ht0, hres⟩ := ht
  exact assignTerm_var_ne v b t0 t hres l hl

/-! ### `NodeVars` monotonicity -/

/-- `NodeVars` weakens along implication of the predicate. -/
theorem nodeVars_mono {n : Nat} {P Q : Fin n → Prop} (hPQ : ∀ v, P v → Q v) :
    ∀ (t : DTree n), NodeVars P t → NodeVars Q t
  | .leaf _, _ => trivial
  | .node v t0 t1, ⟨hv, h0, h1⟩ =>
      ⟨hPQ v hv, nodeVars_mono hPQ t0 h0, nodeVars_mono hPQ t1 h1⟩

/-! ### The `DistinctPaths` invariant

`DistinctPaths t` says: at every node querying `v`, the queried variable `v` is
absent from both subtrees (`NodeVars (· ≠ v)`), recursively.  This is exactly what
forces every root-to-leaf path to have distinct variables. -/

/-- At every node `v`, the variable `v` does not occur as a node variable in either
subtree, recursively. -/
def DistinctPaths {n : Nat} : DTree n → Prop
  | .leaf _ => True
  | .node v t0 t1 =>
      NodeVars (· ≠ v) t0 ∧ NodeVars (· ≠ v) t1 ∧
      DistinctPaths t0 ∧ DistinctPaths t1

mutual
/-- `queryTerm vars D` has `DistinctPaths` when `vars` is a simple term: each query
removes its variable from both the residual DNF and (by simplicity) the remaining
`vars`, so it never recurs downstream. -/
theorem distinctPaths_queryTerm {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), SimpleTerm vars → SimpleDNF D →
      DistinctPaths (queryTerm vars D)
  | [], D, _, hD => by rw [queryTerm_nil]; exact distinctPaths_termCanonicalDT D hD
  | l :: vs, D, hs, hD => by
      rw [queryTerm_cons]
      -- l.var ∉ vs's vars, from SimpleTerm (l :: vs)
      have hnd : (l.var) ∉ vs.map (·.var) := by
        unfold SimpleTerm at hs
        simp only [List.map_cons, List.nodup_cons] at hs
        exact hs.1
      have hvs_ne : ∀ m ∈ vs, m.var ≠ l.var := by
        intro m hm hcon
        exact hnd (by rw [← hcon]; exact List.mem_map_of_mem (·.var) hm)
      have hsvs : SimpleTerm vs := by
        unfold SimpleTerm at hs ⊢
        simp only [List.map_cons, List.nodup_cons] at hs
        exact hs.2
      refine ⟨?_, ?_,
              distinctPaths_queryTerm vs (assignVar l.var false D) hsvs
                (simpleDNF_assignVar hD l.var false),
              distinctPaths_queryTerm vs (assignVar l.var true D) hsvs
                (simpleDNF_assignVar hD l.var true)⟩
      · exact nodeVars_queryTerm vs (assignVar l.var false D) hvs_ne
          (allVars_ne_assignVar l.var false D)
      · exact nodeVars_queryTerm vs (assignVar l.var true D) hvs_ne
          (allVars_ne_assignVar l.var true D)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

/-- `termCanonicalDT D` has `DistinctPaths` when `D` is a simple DNF. -/
theorem distinctPaths_termCanonicalDT {n : Nat} :
    ∀ (D : DNF n), SimpleDNF D → DistinctPaths (termCanonicalDT D)
  | [], _ => by simp [termCanonicalDT, DistinctPaths]
  | [] :: _, _ => by simp [termCanonicalDT, DistinctPaths]
  | (l :: t) :: D, hD => by
      rw [termCanonicalDT_cons_cons]
      have hst : SimpleTerm (l :: t) := hD (l :: t) (List.mem_cons_self _ _)
      have hnd : (l.var) ∉ t.map (·.var) := by
        unfold SimpleTerm at hst
        simp only [List.map_cons, List.nodup_cons] at hst
        exact hst.1
      have ht_ne : ∀ m ∈ t, m.var ≠ l.var := by
        intro m hm hcon
        exact hnd (by rw [← hcon]; exact List.mem_map_of_mem (·.var) hm)
      have hstt : SimpleTerm t := by
        unfold SimpleTerm at hst ⊢
        simp only [List.map_cons, List.nodup_cons] at hst
        exact hst.2
      have hSf : SimpleDNF (assignVar l.var false ((l :: t) :: D)) :=
        simpleDNF_assignVar hD l.var false
      have hSt : SimpleDNF (assignVar l.var true ((l :: t) :: D)) :=
        simpleDNF_assignVar hD l.var true
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact nodeVars_queryTerm t (assignVar l.var false ((l :: t) :: D)) ht_ne
          (allVars_ne_assignVar l.var false ((l :: t) :: D))
      · exact nodeVars_queryTerm t (assignVar l.var true ((l :: t) :: D)) ht_ne
          (allVars_ne_assignVar l.var true ((l :: t) :: D))
      · exact distinctPaths_queryTerm t (assignVar l.var false ((l :: t) :: D)) hstt hSf
      · exact distinctPaths_queryTerm t (assignVar l.var true ((l :: t) :: D)) hstt hSt
  termination_by D => (dnfSize D, 0)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
end

/-! ### From `DistinctPaths` to `Nodup` of the deepest path's variables -/

/-- If `NodeVars (· ≠ w) t` then `w` is not a variable of any deepest-path entry. -/
theorem deepestPath_not_mem_of_nodeVars {n : Nat} {w : Fin n} :
    ∀ (t : DTree n), NodeVars (· ≠ w) t →
      w ∉ (deepestPath t).map Prod.fst := by
  intro t hnode hmem
  rw [List.mem_map] at hmem
  obtain ⟨vd, hvd, hw⟩ := hmem
  have := deepestPath_nodeVars (P := (· ≠ w)) t hnode vd hvd
  exact this (hw ▸ rfl)

/-- **Deepest path has distinct variables.**  Under `DistinctPaths t`, the list of
variables read along the deepest path is `Nodup`. -/
theorem deepestPath_nodup {n : Nat} :
    ∀ (t : DTree n), DistinctPaths t → ((deepestPath t).map Prod.fst).Nodup
  | .leaf _, _ => by simp [deepestPath]
  | .node v t0 t1, hdp => by
      obtain ⟨h0, h1, hd0, hd1⟩ := hdp
      rw [deepestPath]
      split
      · -- descend into t1
        rw [List.map_cons, List.nodup_cons]
        refine ⟨deepestPath_not_mem_of_nodeVars t1 h1, deepestPath_nodup t1 hd1⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨deepestPath_not_mem_of_nodeVars t0 h0, deepestPath_nodup t0 hd0⟩

/-- **The deep-path variables of `termCanonicalDT (D|ρ)` are distinct**, for a
simple DNF `D` (hence a simple `D|ρ`). -/
theorem deepestPath_var_nodup {n : Nat} {D : DNF n} (hD : SimpleDNF D)
    (ρ : Restriction n) :
    ((deepestPath (termCanonicalDT (dnfRestrict ρ D))).map Prod.fst).Nodup :=
  deepestPath_nodup _ (distinctPaths_termCanonicalDT _ (simpleDNF_dnfRestrict hD ρ))

/-! ### The deep path equals the σ-selected path on `termCanonicalDT (D|ρ)`

A genuine, fully-proved structural bridge between the *depth-driven* `deepestPath`
(which descends into the deeper child) and the *assignment-driven* `pathVars`
(which descends along an assignment).  If a total assignment `a` chooses, at every
node on the deepest path, exactly the deep-path direction recorded there, then the
path `a` selects coincides (variable for variable) with the deepest path.  This is
the bridge the Razborov replay uses: `σ = encode₁ ρ` is *defined* to follow the
deep-path directions on the (first `s`) touched variables, so it re-traces the
deep path through them. -/
theorem pathVars_eq_deepestPath_of_follows {n : Nat} (a : Assignment n) :
    ∀ (t : DTree n), (∀ vd ∈ deepestPath t, a vd.1 = vd.2) →
      pathVars a t = (deepestPath t).map Prod.fst := by
  intro t
  induction t with
  | leaf b => intro _; simp [deepestPath, pathVars]
  | node v t0 t1 ih0 ih1 =>
      intro hdir
      rw [deepestPath] at hdir ⊢
      split
      · rename_i h
        rw [if_pos h] at hdir
        have hv : a v = true := hdir (v, true) (List.mem_cons_self _ _)
        rw [pathVars_node, hv]
        simp only [if_true, List.map_cons]
        congr 1
        exact ih1 (fun vd hvd => hdir vd (List.mem_cons_of_mem _ hvd))
      · rename_i h
        rw [if_neg h] at hdir
        have hv : a v = false := hdir (v, false) (List.mem_cons_self _ _)
        rw [pathVars_node, hv]
        simp only [Bool.false_eq_true, if_false, List.map_cons]
        congr 1
        exact ih0 (fun vd hvd => hdir vd (List.mem_cons_of_mem _ hvd))

/-! ## 5. The encoding `encode₁ = σ` and its star count

Let `T := termCanonicalDT (D|ρ)`.  For a bad `ρ` we take the first `s` decisions
of the deepest path `dpath ρ := (deepestPath T).take s` (length `s`, since
`s ≤ dtDepth T = (deepestPath T).length`), read its variables `Y` and directions,
and define `σ := encode₁ ρ` to agree with `ρ` except that each `y ∈ Y` is fixed to
its path direction.  Because the `Y` are `s` *distinct stars* of `ρ`, `σ` has
exactly `ℓ - s` stars. -/

/-- The first `s` decisions of the deepest path of `termCanonicalDT (D|ρ)`. -/
noncomputable def dpath {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    List (Fin n × Bool) :=
  (deepestPath (termCanonicalDT (dnfRestrict ρ D))).take s

/-- The recorded direction at `v` (if `v` is a touched variable). -/
noncomputable def dlookup {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) : Option Bool :=
  ((dpath D s ρ).find? (fun vd => vd.1 = v)).map Prod.snd

/-- The set of touched variables (as a list, in path order). -/
noncomputable def touchedVars {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    List (Fin n) := (dpath D s ρ).map Prod.fst

/-- **`encode₁ ρ = σ`**: `ρ` with the `s` deep-path variables additionally fixed to
their recorded path directions. -/
noncomputable def encode₁ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    Restriction n :=
  fun v => match dlookup D s ρ v with
    | some d => some d
    | none => ρ v

/-! ### Basic facts about `dpath` / `dlookup` / `touchedVars` -/

/-- For a bad `ρ`, the deep-path prefix has length exactly `s`. -/
theorem dpath_length {n : Nat} {D : DNF n} {s ℓ : Nat} {ρ : Restriction n}
    (hρ : ρ ∈ badSetTerm D s ℓ) : (dpath D s ρ).length = s := by
  have hdepth : s ≤ dtDepth (termCanonicalDT (dnfRestrict ρ D)) :=
    ((mem_badSetTerm ρ).mp hρ).2
  have hlen : s ≤ (deepestPath (termCanonicalDT (dnfRestrict ρ D))).length := by
    rw [deepestPath_length]; exact hdepth
  unfold dpath
  rw [List.length_take]
  omega

/-- `dlookup` is `none` exactly off the touched set. -/
theorem dlookup_eq_none_iff {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) : dlookup D s ρ v = none ↔ v ∉ touchedVars D s ρ := by
  unfold dlookup touchedVars
  rw [Option.map_eq_none', List.find?_eq_none]
  constructor
  · intro h hmem
    rw [List.mem_map] at hmem
    obtain ⟨vd, hvd, hv⟩ := hmem
    exact (h vd hvd) (by simpa using hv)
  · intro h vd hvd hcon
    apply h
    rw [List.mem_map]
    exact ⟨vd, hvd, by simpa using hcon⟩

/-- Touched variables are stars of `ρ`. -/
theorem touchedVars_free {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) (hv : v ∈ touchedVars D s ρ) : ρ v = none := by
  unfold touchedVars dpath at hv
  rw [List.mem_map] at hv
  obtain ⟨vd, hvd, hv⟩ := hv
  have hmem : vd ∈ deepestPath (termCanonicalDT (dnfRestrict ρ D)) :=
    List.mem_of_mem_take hvd
  have := deepestPath_var_free ρ D vd hmem
  rw [hv] at this; exact this

/-- Touched variables are `Nodup` (deep-path distinctness, under `SimpleDNF`). -/
theorem touchedVars_nodup {n : Nat} {D : DNF n} (hD : SimpleDNF D) (s : Nat)
    (ρ : Restriction n) : (touchedVars D s ρ).Nodup := by
  unfold touchedVars dpath
  have hnd := deepestPath_var_nodup hD ρ
  have hsub : (List.map Prod.fst
      (List.take s (deepestPath (termCanonicalDT (dnfRestrict ρ D))))).Sublist
      (List.map Prod.fst (deepestPath (termCanonicalDT (dnfRestrict ρ D)))) :=
    (List.take_sublist s _).map Prod.fst
  exact hsub.nodup hnd

/-- Touched-variable list length: exactly `s` for a bad `ρ`. -/
theorem touchedVars_length {n : Nat} {D : DNF n} {s ℓ : Nat} {ρ : Restriction n}
    (hρ : ρ ∈ badSetTerm D s ℓ) : (touchedVars D s ρ).length = s := by
  unfold touchedVars
  rw [List.length_map]
  exact dpath_length hρ

/-- `σ = encode₁ ρ` is `none` exactly on stars of `ρ` that are *not* touched. -/
theorem encode₁_eq_none_iff {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) :
    encode₁ D s ρ v = none ↔ (ρ v = none ∧ v ∉ touchedVars D s ρ) := by
  unfold encode₁
  cases hl : dlookup D s ρ v with
  | some d => simp only [hl]; constructor
              · intro h; exact absurd h (by simp)
              · rintro ⟨_, hnt⟩
                exact absurd ((dlookup_eq_none_iff D s ρ v).mpr hnt) (by rw [hl]; simp)
  | none =>
      simp only [hl]
      have hnt := (dlookup_eq_none_iff D s ρ v).mp hl
      constructor
      · intro h; exact ⟨h, hnt⟩
      · rintro ⟨h, _⟩; exact h

/-- The touched variables form a finset that is a subset of `ρ`'s star set, of
cardinality `s`. -/
theorem touched_finset_card {n : Nat} {D : DNF n} (hD : SimpleDNF D) {s ℓ : Nat}
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) :
    (touchedVars D s ρ).toFinset.card = s := by
  rw [List.toFinset_card_of_nodup (touchedVars_nodup hD s ρ)]
  exact touchedVars_length hρ

/-- **Star count of `σ = encode₁ ρ`.**  For a bad `ρ` (with `s ≤ ℓ`, automatic
since `s ≤ stars(D|ρ-tree depth) ≤ ℓ`), `σ` has exactly `ℓ - s` stars. -/
theorem stars_encode₁ {n : Nat} {D : DNF n} (hD : SimpleDNF D) {s ℓ : Nat}
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) :
    stars (encode₁ D s ρ) = ℓ - s := by
  classical
  have hstarsρ : stars ρ = ℓ := ((mem_badSetTerm ρ).mp hρ).1
  -- the star set of σ = (star set of ρ) \ (touched finset)
  set Tf : Finset (Fin n) := (touchedVars D s ρ).toFinset with hTf
  have hsub : Tf ⊆ Finset.univ.filter (fun v => ρ v = none) := by
    intro v hv
    rw [hTf, List.mem_toFinset] at hv
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, touchedVars_free D s ρ v hv⟩
  have hσset : (Finset.univ.filter (fun v => encode₁ D s ρ v = none))
      = (Finset.univ.filter (fun v => ρ v = none)) \ Tf := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      hTf, List.mem_toFinset]
    rw [encode₁_eq_none_iff]
  unfold stars
  rw [hσset, Finset.card_sdiff hsub, touched_finset_card hD hρ]
  -- |star set ρ| = stars ρ = ℓ
  have : (Finset.univ.filter (fun v => ρ v = none)).card = ℓ := by
    rw [← hstarsρ]; rfl
  rw [this]

/-- A DNF of width `0` (all terms empty) has `dnfSize 0`. -/
theorem dnfSize_eq_zero_of_width_zero {n : Nat} :
    ∀ (E : DNF n), widthDNF E = 0 → dnfSize E = 0
  | [], _ => rfl
  | t :: Ds, hw => by
      rw [widthDNF_cons] at hw
      have htw : termWidth t = 0 := by omega
      have hDw : widthDNF Ds = 0 := by omega
      rw [dnfSize_cons, dnfSize_eq_zero_of_width_zero Ds hDw]
      unfold termWidth at htw; omega

/-! ## 6. The code, the full encode, and injectivity

The `σ = encode₁ ρ` star count is proved.  It remains to (a) attach the Razborov
*code* `Fin s → Fin w × Bool` and (b) prove the full map injective on the bad set.

The code attaches the genuine deep-path **direction** of each touched decision
(real, recoverable data) together with a `Fin w` index slot.  The substantive
content of injectivity is that the touched set of `ρ` is recoverable from `σ` (and
`D`); we isolate exactly this as `TouchedRecoverable` (a `def : Prop`, NOT an
axiom) and prove that it implies injectivity and hence `SwitchingLemmaTerm`. -/

/-! ### Genuine within-term-block positions of the touched variables

The Razborov code must record, for each touched variable, *which variable of its
term block it is* — its within-block position — so that the replay can re-identify
exactly those variables.  The term-canonical tree partitions every root-to-leaf
path into consecutive **term blocks**, one per term, the block for a term
`t₁ = l :: t` consisting of its `1 + t.length` variables in order
(`pathVars_termCanonicalDT_cons_cons`).

We compute the consecutive block lengths along the *deepest* branch of
`termCanonicalDT (D|ρ)` by re-walking the canonical-tree recursion and following
the deeper child at each node — `deepBlockLens` / `deepBlockLensQ` mirror
`termCanonicalDT` / `queryTerm` exactly, descending into the deeper subtree and
emitting one block length per term entered.  From the block-length list,
`blockPosOfIndex` converts a global path index `i` into its position *within its
own block* (subtracting all preceding complete blocks). -/

/-- Position of a global path index `i` within its own term block, given the list
of consecutive block lengths (in path order). -/
def blockPosOfIndex : List Nat → Nat → Nat
  | [], i => i
  | b :: bs, i => if i < b then i else blockPosOfIndex bs (i - b)

mutual
/-- Consecutive term-block lengths along the *deepest branch* of
`termCanonicalDT D`: mirrors `termCanonicalDT`, emitting `1 + t.length` (the block
of the first term `l :: t`) then descending into the deeper child's blocks. -/
def deepBlockLens {n : Nat} : DNF n → List Nat
  | [] => []
  | [] :: _ => []
  | (l :: t) :: D =>
      (1 + t.length) ::
        (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
            ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
          then deepBlockLensQ t (assignVar l.var true ((l :: t) :: D))
          else deepBlockLensQ t (assignVar l.var false ((l :: t) :: D)))
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)

/-- Block-length helper mirroring `queryTerm`: continues the current block down
the deeper child, returning control to `deepBlockLens` at the block boundary. -/
def deepBlockLensQ {n : Nat} : Term n → DNF n → List Nat
  | [], D => deepBlockLens D
  | l :: vs, D =>
      if dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
        then deepBlockLensQ vs (assignVar l.var true D)
        else deepBlockLensQ vs (assignVar l.var false D)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

/-- The genuine within-block position of the `i`-th touched variable along the deep
path of `termCanonicalDT (D|ρ)`. -/
noncomputable def codeBlockPos {n : Nat} (D : DNF n) (ρ : Restriction n) (i : Nat) :
    Nat :=
  blockPosOfIndex (deepBlockLens (dnfRestrict ρ D)) i

/-- The Razborov code of `ρ` at position `i ∈ Fin s` (requires `0 < w`, supplied at
use sites where a touched variable exists): the **genuine within-term-block
position** of the `i`-th touched variable (which variable of its term it is — the
real, recoverable content, taken `% w` only as a totality guard; it is already
`< w` since a block has at most `widthDNF D ≤ w` variables) together with its
genuine deep-path direction.  This replaces the previous placeholder (which
recorded the bare global index `i % w`) with the actual block position the replay
needs to re-identify the touched variables. -/
noncomputable def codeOf {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) : Fin s → Fin w × Bool :=
  fun i =>
    match (dpath D s ρ).get? i.1 with
    | some (_, d) => (⟨codeBlockPos D ρ i.1 % w, Nat.mod_lt _ hw⟩, d)
    | none => (⟨0, hw⟩, false)

/-- The full Razborov **encode** (requires `0 < w`). -/
noncomputable def encode {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) : Restriction n × (Fin s → Fin w × Bool) :=
  (encode₁ D s ρ, codeOf D w s hw ρ)

/-! ### Restriction composition: `D|σ = (D|ρ)|τ` (PROVED machinery)

A genuine, fully-proved structural lever for the decode side: the encoded
restriction `σ = encode₁ ρ` factors as `ρ` overlaid with the *touched-direction*
restriction `τ` (fixing exactly the touched variables to their deep-path
directions), and because `τ` only touches variables FREE in `ρ` (the touched
variables are stars of `ρ`), restriction commutes:

  `dnfRestrict σ D = dnfRestrict τ (dnfRestrict ρ D)`.

This is the decode-side analogue of `pathVars_eq_deepestPath_of_follows`: it lets
the recovery argument reason about `D|σ` as the deep residual of `D|ρ` rather than
as a fresh restriction.  It is proved with no `sorry`; it does NOT by itself close
`TouchedRecoverable` (see the precise remaining sub-step below). -/

/-- Overlay of two restrictions: `τ` wins where it is defined, else `ρ`. -/
def overlay {n : Nat} (ρ τ : Restriction n) : Restriction n :=
  fun v => match τ v with | some b => some b | none => ρ v

theorem overlay_eq_some_of_τ {n : Nat} (ρ τ : Restriction n) (v : Fin n) (b : Bool)
    (h : τ v = some b) : overlay ρ τ v = some b := by unfold overlay; rw [h]

theorem overlay_eq_ρ_of_τ_none {n : Nat} (ρ τ : Restriction n) (v : Fin n)
    (h : τ v = none) : overlay ρ τ v = ρ v := by unfold overlay; rw [h]

/-- **Term-level composition** (τ disjoint from ρ's domain). -/
theorem termRestrict_overlay {n : Nat} (ρ τ : Restriction n) (t : Term n)
    (hdisj : ∀ v, ρ v ≠ none → τ v = none) :
    termRestrict (overlay ρ τ) t =
      (termRestrict ρ t).bind (termRestrict τ) := by
  induction t with
  | nil => simp [termRestrict]
  | cons l t ih =>
      simp only [termRestrict]
      cases hρ : ρ l.var with
      | none =>
          cases hτ2 : τ l.var with
          | none =>
              rw [overlay_eq_ρ_of_τ_none ρ τ l.var hτ2]
              simp only [hρ, ih]
              cases hr : termRestrict ρ t with
              | none => simp [hr, hτ2]
              | some t' => simp [hr, termRestrict, hτ2]
          | some b =>
              rw [overlay_eq_some_of_τ ρ τ l.var b hτ2]
              simp only [hρ, ih]
              by_cases hb : b = l.sign
              · simp only [if_pos hb]
                cases hr : termRestrict ρ t with
                | none => simp [hr]
                | some t' => simp [hr, termRestrict, hτ2, hb]
              · simp only [if_neg hb]
                cases hr : termRestrict ρ t with
                | none => simp [hr]
                | some t' => simp [hr, termRestrict, hτ2, hb]
      | some b =>
          have hτ0 : τ l.var = none := hdisj l.var (by rw [hρ]; simp)
          rw [overlay_eq_ρ_of_τ_none ρ τ l.var hτ0]
          simp only [hρ, ih]
          by_cases hb : b = l.sign
          · simp only [if_pos hb]
          · simp only [if_neg hb]; simp

/-- **DNF-level composition** (τ disjoint from ρ's domain). -/
theorem dnfRestrict_overlay {n : Nat} (ρ τ : Restriction n) (D : DNF n)
    (hdisj : ∀ v, ρ v ≠ none → τ v = none) :
    dnfRestrict (overlay ρ τ) D = dnfRestrict τ (dnfRestrict ρ D) := by
  unfold dnfRestrict
  rw [List.filterMap_filterMap]
  apply List.filterMap_congr
  intro t _ht
  exact termRestrict_overlay ρ τ t hdisj

/-- The touched-direction restriction read off the deep-path prefix: fixes exactly
the touched variables to their recorded deep-path directions. -/
noncomputable def touchedRestr {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    Restriction n := fun v => dlookup D s ρ v

/-- `encode₁` is exactly `overlay ρ (touchedRestr …)`. -/
theorem encode₁_eq_overlay {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    encode₁ D s ρ = overlay ρ (touchedRestr D s ρ) := by
  funext v
  unfold encode₁ overlay touchedRestr
  cases dlookup D s ρ v <;> rfl

/-- The touched directions are disjoint from `ρ`'s domain (touched vars are free). -/
theorem touchedRestr_disj {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    ∀ v, ρ v ≠ none → touchedRestr D s ρ v = none := by
  intro v hv
  unfold touchedRestr
  rw [dlookup_eq_none_iff]
  intro hmem
  exact hv (touchedVars_free D s ρ v hmem)

/-- **`D|σ` decomposes as `(D|ρ)|τ`** for `σ = encode₁ ρ` and `τ` the
touched-direction restriction.  Fully proved. -/
theorem dnfRestrict_encode₁ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    dnfRestrict (encode₁ D s ρ) D
      = dnfRestrict (touchedRestr D s ρ) (dnfRestrict ρ D) := by
  rw [encode₁_eq_overlay]
  exact dnfRestrict_overlay ρ (touchedRestr D s ρ) D (touchedRestr_disj D s ρ)

/-! ### The variable-emitting deep walk (NEW, fully proved)

We close one half of the "remaining work" flagged below: a recursion mirroring
`deepBlockLens`/`deepBlockLensQ` that emits the chosen **variable** (and direction)
at each step — `deepPathV` / `deepPathVQ` — and a full proof that it agrees with
the depth-driven deepest path of the term-canonical tree:

  `deepPathV D = deepestPath (termCanonicalDT D)`.

This is the "residual-aware term-block bookkeeping (a recursion mirroring
`deepBlockLens` that also emits the chosen VARIABLE) and ... its agreement with the
deep path" referenced in the open-problem comment.  It is genuinely proved (no
`sorry`): both sides follow the same depth-comparison at each node, so they
coincide structurally.  It is the variable-level companion of `deepBlockLens` and
makes the deep path computable by the same canonical recursion that the decode
must walk. -/

mutual
/-- Deepest-path `(var, dir)` list along the canonical recursion of `D`, mirroring
`deepBlockLens` but emitting the queried variable and the deep direction. -/
def deepPathV {n : Nat} : DNF n → List (Fin n × Bool)
  | [] => []
  | [] :: _ => []
  | (l :: t) :: D =>
      if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
        then (l.var, true) ::
              deepPathVQ t (assignVar l.var true ((l :: t) :: D))
        else (l.var, false) ::
              deepPathVQ t (assignVar l.var false ((l :: t) :: D))
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)

/-- Block helper for `deepPathV`, mirroring `deepBlockLensQ`/`queryTerm`. -/
def deepPathVQ {n : Nat} : Term n → DNF n → List (Fin n × Bool)
  | [], D => deepPathV D
  | l :: vs, D =>
      if dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
        then (l.var, true) :: deepPathVQ vs (assignVar l.var true D)
        else (l.var, false) :: deepPathVQ vs (assignVar l.var false D)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

mutual
/-- **Agreement (helper).** `deepPathVQ vars D = deepestPath (queryTerm vars D)`. -/
theorem deepPathVQ_eq {n : Nat} :
    ∀ (vars : Term n) (D : DNF n),
      deepPathVQ vars D = deepestPath (queryTerm vars D)
  | [], D => by
      rw [show deepPathVQ ([] : Term n) D = deepPathV D from by rw [deepPathVQ]]
      rw [queryTerm_nil]
      exact deepPathV_eq D
  | l :: vs, D => by
      rw [show deepPathVQ (l :: vs) D
            = (if dtDepth (queryTerm vs (assignVar l.var false D))
                  ≤ dtDepth (queryTerm vs (assignVar l.var true D))
                then (l.var, true) :: deepPathVQ vs (assignVar l.var true D)
                else (l.var, false) :: deepPathVQ vs (assignVar l.var false D))
            from by rw [deepPathVQ]]
      rw [queryTerm_cons, deepestPath]
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · simp only [if_pos h]
        rw [deepPathVQ_eq vs (assignVar l.var true D)]
      · simp only [if_neg h]
        rw [deepPathVQ_eq vs (assignVar l.var false D)]
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

/-- **Agreement (NEW, fully proved).** The variable-emitting deep walk equals the
depth-driven deepest path of the term-canonical tree:
`deepPathV D = deepestPath (termCanonicalDT D)`.  This is the variable-level
analogue of `deepBlockLens`, with its correctness against `deepestPath` proved. -/
theorem deepPathV_eq {n : Nat} :
    ∀ (D : DNF n), deepPathV D = deepestPath (termCanonicalDT D)
  | [] => by simp [deepPathV, termCanonicalDT, deepestPath]
  | [] :: _ => by simp [deepPathV, termCanonicalDT, deepestPath]
  | (l :: t) :: D => by
      rw [show deepPathV ((l :: t) :: D)
            = (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                  ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
                then (l.var, true) ::
                      deepPathVQ t (assignVar l.var true ((l :: t) :: D))
                else (l.var, false) ::
                      deepPathVQ t (assignVar l.var false ((l :: t) :: D)))
            from by rw [deepPathV]]
      rw [termCanonicalDT_cons_cons, deepestPath]
      by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
      · simp only [if_pos h]
        rw [deepPathVQ_eq t (assignVar l.var true ((l :: t) :: D))]
      · simp only [if_neg h]
        rw [deepPathVQ_eq t (assignVar l.var false ((l :: t) :: D))]
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
end

/-- **Computable characterization of the touched variables (NEW, proved).**  The
touched variables are the first `s` variables of the variable-emitting deep walk on
`D|ρ`.  This re-expresses `touchedVars` (defined via the opaque `deepestPath` of the
built tree) through the *same canonical recursion* `deepPathV` that the decode must
re-walk — a prerequisite for any decode that re-runs the canonical tree. -/
theorem touchedVars_eq_deepPathV {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) :
    touchedVars D s ρ = ((deepPathV (dnfRestrict ρ D)).take s).map Prod.fst := by
  unfold touchedVars dpath
  rw [deepPathV_eq]

/-! ### Block-alignment of `deepBlockLens` against `deepPathV` (NEW, fully proved)

The decode (`BlockDecodeStep`) needs to know that the term-block lengths
`deepBlockLens D` genuinely partition the deep path `deepPathV D` into consecutive
term blocks, one block per term, each block being exactly the variables of that
term in order.  We prove this foundational structural fact in three parts:

1. `deepBlockLens_sum_eq` — the block lengths sum to the path length.
2. `deepPathV_cons_cons_take` / `deepBlockLens_head` — the first block has length
   `(l :: t).length` and the first `(l :: t).length` deep-path variables are
   exactly the variables of the first term `l :: t`, in order.
3. `blockPosOfIndex_lt` and the within-block position machinery tying a global
   index to its within-block position.

Everything is proved by the SAME mutual recursion that generates
`deepBlockLens`/`deepBlockLensQ` and `deepPathV`/`deepPathVQ` (well-founded on
`(dnfSize, vars.length)`), so the structural correspondence is exact. -/

mutual
/-- **Block lengths sum to path length (main).** -/
theorem deepBlockLens_sum_eq {n : Nat} :
    ∀ (D : DNF n), (deepBlockLens D).sum = (deepPathV D).length
  | [] => by rw [deepBlockLens, deepPathV]; rfl
  | [] :: D => by rw [deepBlockLens, deepPathV]; rfl
  | (l :: t) :: D => by
      rw [show deepBlockLens ((l :: t) :: D)
            = (1 + t.length) ::
                (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                    ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
                  then deepBlockLensQ t (assignVar l.var true ((l :: t) :: D))
                  else deepBlockLensQ t (assignVar l.var false ((l :: t) :: D)))
            from by rw [deepBlockLens]]
      rw [show deepPathV ((l :: t) :: D)
            = (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                  ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
                then (l.var, true) ::
                      deepPathVQ t (assignVar l.var true ((l :: t) :: D))
                else (l.var, false) ::
                      deepPathVQ t (assignVar l.var false ((l :: t) :: D)))
            from by rw [deepPathV]]
      by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
      · simp only [if_pos h, List.sum_cons, List.length_cons]
        have := deepBlockLensQ_sum_eq t (assignVar l.var true ((l :: t) :: D))
        omega
      · simp only [if_neg h, List.sum_cons, List.length_cons]
        have := deepBlockLensQ_sum_eq t (assignVar l.var false ((l :: t) :: D))
        omega
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)

/-- **Block lengths sum to path length (block helper).**  The current (un-emitted)
block of `vars.length` variables plus the emitted blocks sum to the path length. -/
theorem deepBlockLensQ_sum_eq {n : Nat} :
    ∀ (vars : Term n) (D : DNF n),
      (deepBlockLensQ vars D).sum + vars.length = (deepPathVQ vars D).length
  | [], D => by
      rw [show deepBlockLensQ ([] : Term n) D = deepBlockLens D from by
            rw [deepBlockLensQ]]
      rw [show deepPathVQ ([] : Term n) D = deepPathV D from by rw [deepPathVQ]]
      rw [List.length_nil, Nat.add_zero]
      exact deepBlockLens_sum_eq D
  | l :: vs, D => by
      rw [show deepBlockLensQ (l :: vs) D
            = (if dtDepth (queryTerm vs (assignVar l.var false D))
                  ≤ dtDepth (queryTerm vs (assignVar l.var true D))
                then deepBlockLensQ vs (assignVar l.var true D)
                else deepBlockLensQ vs (assignVar l.var false D))
            from by rw [deepBlockLensQ]]
      rw [show deepPathVQ (l :: vs) D
            = (if dtDepth (queryTerm vs (assignVar l.var false D))
                  ≤ dtDepth (queryTerm vs (assignVar l.var true D))
                then (l.var, true) :: deepPathVQ vs (assignVar l.var true D)
                else (l.var, false) :: deepPathVQ vs (assignVar l.var false D))
            from by rw [deepPathVQ]]
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · simp only [if_pos h, List.length_cons]
        have := deepBlockLensQ_sum_eq vs (assignVar l.var true D)
        omega
      · simp only [if_neg h, List.length_cons]
        have := deepBlockLensQ_sum_eq vs (assignVar l.var false D)
        omega
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

/-- **First block length.**  For a DNF whose first term is `l :: t`, the head of
`deepBlockLens` is exactly the width `1 + t.length = (l :: t).length` of the first
term. -/
theorem deepBlockLens_head {n : Nat} (l : Literal n) (t : Term n) (D : DNF n) :
    (deepBlockLens ((l :: t) :: D)).head? = some (1 + t.length) := by
  rw [show deepBlockLens ((l :: t) :: D)
        = (1 + t.length) ::
            (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
              then deepBlockLensQ t (assignVar l.var true ((l :: t) :: D))
              else deepBlockLensQ t (assignVar l.var false ((l :: t) :: D)))
        from by rw [deepBlockLens]]
  rfl

/-- The deep-path block helper emits, as a prefix, one entry per variable of
`vars`, in order — i.e. `(deepPathVQ vars D).map Prod.fst` begins with
`vars.map (·.var)`.  Mirrors `pathVars_queryTerm`. -/
theorem deepPathVQ_vars_prefix {n : Nat} :
    ∀ (vars : Term n) (D : DNF n),
      ∃ rest, (deepPathVQ vars D).map Prod.fst = vars.map (·.var) ++ rest
  | [], D => by
      rw [show deepPathVQ ([] : Term n) D = deepPathV D from by rw [deepPathVQ]]
      exact ⟨(deepPathV D).map Prod.fst, by simp⟩
  | l :: vs, D => by
      rw [show deepPathVQ (l :: vs) D
            = (if dtDepth (queryTerm vs (assignVar l.var false D))
                  ≤ dtDepth (queryTerm vs (assignVar l.var true D))
                then (l.var, true) :: deepPathVQ vs (assignVar l.var true D)
                else (l.var, false) :: deepPathVQ vs (assignVar l.var false D))
            from by rw [deepPathVQ]]
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · obtain ⟨rest, hrest⟩ := deepPathVQ_vars_prefix vs (assignVar l.var true D)
        refine ⟨rest, ?_⟩
        simp only [if_pos h, List.map_cons, List.cons_append]
        rw [hrest]
      · obtain ⟨rest, hrest⟩ := deepPathVQ_vars_prefix vs (assignVar l.var false D)
        refine ⟨rest, ?_⟩
        simp only [if_neg h, List.map_cons, List.cons_append]
        rw [hrest]
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-- **First-block alignment (variable level).**  The deep-path variables of
`termCanonicalDT ((l :: t) :: D)` begin with exactly the variables of the first
term `l :: t`, in order: `(deepPathV ((l :: t) :: D)).map Prod.fst` factors as
`(l :: t).map (·.var) ++ rest`.  This is the depth-driven analogue of
`pathVars_termCanonicalDT_cons_cons`, and it certifies that the head block of
`deepBlockLens` (length `(l :: t).length`) carves off exactly the first term. -/
theorem deepPathV_cons_cons_prefix {n : Nat} (l : Literal n) (t : Term n)
    (D : DNF n) :
    ∃ rest, (deepPathV ((l :: t) :: D)).map Prod.fst
              = (l :: t).map (·.var) ++ rest := by
  rw [show deepPathV ((l :: t) :: D)
        = (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
              ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
            then (l.var, true) ::
                  deepPathVQ t (assignVar l.var true ((l :: t) :: D))
            else (l.var, false) ::
                  deepPathVQ t (assignVar l.var false ((l :: t) :: D)))
        from by rw [deepPathV]]
  by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
      ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
  · obtain ⟨rest, hrest⟩ :=
      deepPathVQ_vars_prefix t (assignVar l.var true ((l :: t) :: D))
    refine ⟨rest, ?_⟩
    simp only [if_pos h, List.map_cons, List.cons_append]
    rw [hrest]
  · obtain ⟨rest, hrest⟩ :=
      deepPathVQ_vars_prefix t (assignVar l.var false ((l :: t) :: D))
    refine ⟨rest, ?_⟩
    simp only [if_neg h, List.map_cons, List.cons_append]
    rw [hrest]

/-- **First-block alignment (take form).**  The first `(l :: t).length` deep-path
variables of `termCanonicalDT ((l :: t) :: D)` are exactly the variables of the
first term `l :: t`.  This is the precise "the first block is the first term's
variables" statement the decode consumes, with the block length read off
`deepBlockLens_head`. -/
theorem deepPathV_cons_cons_take {n : Nat} (l : Literal n) (t : Term n)
    (D : DNF n) :
    ((deepPathV ((l :: t) :: D)).map Prod.fst).take (1 + t.length)
      = (l :: t).map (·.var) := by
  obtain ⟨rest, hrest⟩ := deepPathV_cons_cons_prefix l t D
  rw [hrest]
  have hlen : ((l :: t).map (·.var)).length = 1 + t.length := by
    simp [List.length_map, Nat.add_comm]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-! ### `blockPosOfIndex` correctness

`blockPosOfIndex bs i` subtracts off whole preceding blocks of `bs` to return the
position of global index `i` inside its own block.  We prove the two facts the
decode needs: (a) a `blockPosOfIndex_lt` bound — the within-block position is
strictly less than its block's length whenever `i` is in range of the total; and
(b) for the *first* block, `blockPosOfIndex (b :: bs) i = i` exactly when `i < b`,
so the within-block position of an index inside the first term block is the index
itself (the head-block decode case). -/

/-- For an index inside the first block, the within-block position is the index. -/
theorem blockPosOfIndex_first {bs : List Nat} {b i : Nat} (h : i < b) :
    blockPosOfIndex (b :: bs) i = i := by
  rw [blockPosOfIndex]; simp [h]

/-- **`blockPosOfIndex` lands inside a block.**  If `i` is a valid global index
(`i < bs.sum`), then its within-block position is strictly less than the length of
the block it falls in; concretely it is `< ` the matched block length, hence the
code slot `codeBlockPos … % w` is a faithful within-block coordinate.  We prove the
clean invariant: for any `i < bs.sum` there is a block `b ∈ bs` with
`blockPosOfIndex bs i < b`. -/
theorem blockPosOfIndex_lt :
    ∀ (bs : List Nat) (i : Nat), i < bs.sum →
      ∃ b ∈ bs, blockPosOfIndex bs i < b
  | [], i, h => by simp [List.sum_nil] at h
  | b :: bs, i, h => by
      by_cases hib : i < b
      · refine ⟨b, List.mem_cons_self _ _, ?_⟩
        rw [blockPosOfIndex, if_pos hib]; exact hib
      · rw [blockPosOfIndex, if_neg hib]
        have hsum : (b :: bs).sum = b + bs.sum := by rw [List.sum_cons]
        have hlt : i - b < bs.sum := by omega
        obtain ⟨b', hb'mem, hb'lt⟩ := blockPosOfIndex_lt bs (i - b) hlt
        exact ⟨b', List.mem_cons_of_mem _ hb'mem, hb'lt⟩

/-- **Within-block position bound on the deep path (specialized).**  For a global
deep-path index `i` in range (`i < (deepPathV D).length`), the within-block
position `blockPosOfIndex (deepBlockLens D) i` is strictly less than the length of
the term block it falls in — so it is a genuine within-block coordinate of one of
the term blocks.  Combines `deepBlockLens_sum_eq` with `blockPosOfIndex_lt`. -/
theorem blockPosOfIndex_deepBlockLens_lt {n : Nat} (D : DNF n) (i : Nat)
    (h : i < (deepPathV D).length) :
    ∃ b ∈ deepBlockLens D, blockPosOfIndex (deepBlockLens D) i < b := by
  apply blockPosOfIndex_lt
  rw [deepBlockLens_sum_eq]
  exact h

/-! ### The isolated injectivity crux

`TouchedRecoverable` says: from `σ = encode₁ ρ` and the code one can recover the
touched-variable set of `ρ`.  Given recoverability, `ρ` is determined by `σ` (set
the touched variables back to `none`, keep the rest from `σ`), so `encode` is
injective on the bad set.

This is an isolated `def : Prop` — NOT an `axiom`, NOT asserted true.  It names
exactly the remaining content: the Razborov *replay* that re-finds the touched
variables of `ρ` by re-running the term-canonical tree on `D|σ`.

PRECISE REMAINING SUB-STEP (the blocking induction).  All of the supporting
structure is now in place and proved:

* `codeOf` records the **genuine within-term-block position** of each touched
  variable (via `codeBlockPos`/`deepBlockLens`/`blockPosOfIndex`), plus its
  deep-path direction — no longer a placeholder.
* `pathVars_eq_deepestPath_of_follows` proves that `σ = encode₁ ρ`, which fixes the
  touched variables to their deep-path directions, re-traces the deep path through
  them (the depth-driven `deepestPath` agrees with the σ-selected `pathVars`).
* `stars_encode₁`, `ρ_eq_of_encode`, `touchedVars_nodup`, and the full
  injectivity-from-recovery reduction (`switchingLemmaTerm_of_recoverable`) are all
  proved generically in `codeOf`.
* `dnfRestrict_encode₁` (just above) proves the decode-side composition
  `D|σ = (D|ρ)|τ`, τ the touched-direction restriction — so the recovery argument
  may treat `D|σ` as the deep residual of `D|ρ`.

What remains is a single induction: define `rec` as the **code-guided block walk**
on `D|σ` and prove `rec (encode₁ ρ) (codeOf ρ) = (touchedVars ρ).toFinset`.  The
difficulty is intrinsic and is the genuine mathematical heart of the switching
lemma: the touched variables are *fixed* in `σ`, hence absent from
`termCanonicalDT (D|σ)`, so the replay must reconstruct them from `D`'s original
term structure interleaved with the recorded block positions — it cannot read them
off `D|σ` directly.  Carrying the term-block boundaries through the residualization
of the canonical-tree recursion is the open part.

PRECISE BLOCKING SUB-LEMMA (after composition).  All restriction-algebra plumbing
is now discharged.  The single open content is the **decode determinacy** step:

  given only `D`, `σ = encode₁ ρ`, and the code `codeOf ρ`, the i-th touched
  variable `v_i` is uniquely identified as the variable at within-block position
  `codeBlockPos D ρ i` of the i-th term-block ENTERED by the deep path of `D|ρ`,
  and this term-block is recoverable from `D|σ` (= `(D|ρ)|τ`) without ρ — namely it
  is the first surviving term-block of the residual after the first `i` touched
  variables are re-fixed.

Concretely the open `def : Prop` is the per-block recovery step:

  `∀ i < s, the (i+1)-th surviving term-block of D under (σ on the first i decoded
   vars) has its `codeBlockPos`-th variable equal to the i-th touched variable`,

from which `rec` is the obvious `s`-fold fold and the recovery equation follows by
induction on `i`.

UPDATE (this revision).  Two of the three "remaining work" items above are now
PROVED, and the isolation has been SHARPENED:

* The "recursion mirroring `deepBlockLens` that also emits the chosen VARIABLE" and
  "its agreement with the deep path of `D|ρ`" are now `deepPathV` / `deepPathVQ`
  with the proved equality `deepPathV_eq : deepPathV D = deepestPath
  (termCanonicalDT D)` and the corollary `touchedVars_eq_deepPathV`.
* The "obvious `s`-fold fold ... by induction on `i`" is now the proved
  `decodeAux` + `decodeAux_eq_take` + `touchedRecoverable_of_blockStep :
  BlockDecodeStep n → TouchedRecoverable n`.

Consequently the SOLE remaining mathematical content is the *single deep-path entry*
recovery `BlockDecodeStep` (below), strictly smaller than `TouchedRecoverable`.
`TouchedRecoverable` is kept as the interface for the proved injectivity reduction;
`BlockDecodeStep` is the tighter isolated `def : Prop`.  This file does NOT fake it:
both stay isolated `def : Prop`s (NOT axioms). -/
def TouchedRecoverable (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w),
    ∃ rec : Restriction n → (Fin s → Fin w × Bool) → Finset (Fin n),
      ∀ ρ ∈ badSetTerm D s ℓ,
        rec (encode₁ D s ρ) (codeOf D w s hw ρ) = (touchedVars D s ρ).toFinset

/-! ### Tighter isolation: reduce `TouchedRecoverable` to a SINGLE-BLOCK step

We now strictly reduce the monolithic recovery `TouchedRecoverable` to a single
**per-step** recovery obligation `BlockDecodeStep`, with a *fully proved* fold.
This is the "`rec` is the obvious `s`-fold fold and the recovery equation follows by
induction on `i`" promised in the comment, now formalized: given a step function
that recovers the `i`-th deep-path entry from `σ`, the `i`-th code entry, and the
already-recovered prefix, the `s`-fold deterministically rebuilds the whole touched
list.  All of the fold/prefix induction is discharged here; the SINGLE remaining
mathematical content is `BlockDecodeStep`. -/

/-- `take (i+1)` is `take i` with the `i`-th element appended (list helper). -/
theorem List.take_succ_append_getElem {α : Type*} :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      l.take (i + 1) = l.take i ++ [l[i]]
  | [], i, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, h => by
      simp only [List.take_succ_cons, List.getElem_cons_succ]
      rw [List.take_succ_append_getElem l i (by simpa using h)]
      simp

/-- Deterministic `i`-fold decoder driven by a per-step recovery function `step`:
rebuild the deep-path prefix entry by entry, each step consulting `σ`, the `i`-th
code entry, and the prefix recovered so far. -/
def decodeAux {n w : Nat} (step : Restriction n → (Fin w × Bool) →
      List (Fin n × Bool) → (Fin n × Bool))
    (σ : Restriction n) (s : Nat) (code : Fin s → Fin w × Bool) :
    Nat → List (Fin n × Bool)
  | 0 => []
  | (i + 1) =>
      let prev := decodeAux step σ s code i
      if h : i < s then prev ++ [step σ (code ⟨i, h⟩) prev] else prev

theorem decodeAux_succ {n w : Nat} (step : Restriction n → (Fin w × Bool) →
      List (Fin n × Bool) → (Fin n × Bool))
    (σ : Restriction n) (s : Nat) (code : Fin s → Fin w × Bool) (i : Nat)
    (h : i < s) :
    decodeAux step σ s code (i + 1)
      = decodeAux step σ s code i
          ++ [step σ (code ⟨i, h⟩) (decodeAux step σ s code i)] := by
  rw [decodeAux]; simp only [h, dif_pos]

theorem decodeAux_length {n w : Nat} (step : Restriction n → (Fin w × Bool) →
      List (Fin n × Bool) → (Fin n × Bool))
    (σ : Restriction n) (s : Nat) (code : Fin s → Fin w × Bool) :
    ∀ i, i ≤ s → (decodeAux step σ s code i).length = i
  | 0, _ => by simp [decodeAux]
  | (i + 1), hi => by
      rw [decodeAux_succ step σ s code i (by omega)]
      rw [List.length_append, decodeAux_length step σ s code i (by omega)]
      simp

/-- The bad-set membership gives `i < length (deepPathV (D|ρ))` for `i < s`. -/
theorem lt_deepPathV_length_of_bad {n : Nat} {D : DNF n} {s ℓ : Nat}
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) {i : Nat} (hi : i < s) :
    i < (deepPathV (dnfRestrict ρ D)).length := by
  rw [deepPathV_eq, deepestPath_length]
  exact lt_of_lt_of_le hi ((mem_badSetTerm ρ).mp hρ).2

/-- **`dpath` is the length-`s` prefix of the variable-emitting deep walk.**
Re-expresses `dpath` (defined via the opaque `deepestPath`) through `deepPathV`. -/
theorem dpath_eq_deepPathV_take {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    dpath D s ρ = (deepPathV (dnfRestrict ρ D)).take s := by
  unfold dpath; rw [deepPathV_eq]

/-- **Direction half of the decode is FREE (PROVED).**  The direction recorded by
`codeOf` at position `i` is exactly the deep-path direction of the `i`-th entry.
This proves that the *direction* component of the per-step recovery requires no
reconstruction at all: it is literally carried in the code.  Hence the only
remaining content of `BlockDecodeStep` is recovering the *variable*. -/
theorem codeOf_snd_eq_deepPathV {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) {i : Nat} (hi : i < s) :
    (codeOf D w s hw ρ ⟨i, hi⟩).2
      = ((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).2 := by
  unfold codeOf
  -- `(dpath D s ρ).get? i = some ((deepPathV (D|ρ)).get ⟨i,_⟩)`
  have hlen : i < (deepPathV (dnfRestrict ρ D)).length := lt_deepPathV_length_of_bad hρ hi
  have hget : (dpath D s ρ).get? i
      = some ((deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩) := by
    rw [dpath_eq_deepPathV_take]
    rw [List.get?_eq_getElem?, List.getElem?_take_of_lt hi]
    rw [List.getElem?_eq_getElem hlen, List.get_eq_getElem]
  rw [hget]

/-- **The single-block decode step (the SOLE remaining mathematical content).**
There is a per-step recovery function that, for every bad `ρ`, recovers the `i`-th
deep-path entry of `D|ρ` from `σ = encode₁ ρ`, the `i`-th code entry, and the
already-recovered length-`i` prefix `(deepPathV (D|ρ)).take i`.  This is the
Razborov replay's per-block determinacy step; it is an isolated `def : Prop` (NOT an
axiom, NOT asserted true).  Below we PROVE that it implies the monolithic
`TouchedRecoverable`. -/
def BlockDecodeStep (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w),
    ∃ step : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → (Fin n × Bool),
      ∀ (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s),
        step (encode₁ D s ρ) (codeOf D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = (deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩

/-! ### STRICTLY SMALLER isolation: variable-only recovery `BlockDecodeStepVar`

`codeOf_snd_eq_deepPathV` proves the *direction* half of the decode is free (it is
literally carried in the code).  We therefore reduce `BlockDecodeStep` to the
strictly smaller obligation of recovering only the *variable* of the `i`-th deep
entry — `BlockDecodeStepVar` — and PROVE the reduction
`BlockDecodeStepVar n → BlockDecodeStep n`.  This sharpens the isolation: the SOLE
remaining mathematical content is a single `Fin n`-valued recovery, with the `Bool`
direction discharged. -/

/-- **Variable-only single-block decode step.**  A per-step recovery of just the
*variable* of the `i`-th deep-path entry of `D|ρ`, from `σ = encode₁ ρ`, the `i`-th
code entry, and the already-recovered length-`i` prefix.  Strictly smaller than
`BlockDecodeStep` (the direction is supplied by `codeOf_snd_eq_deepPathV`). -/
def BlockDecodeStepVar (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w),
    ∃ stepVar : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → Fin n,
      ∀ (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s),
        stepVar (encode₁ D s ρ) (codeOf D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = ((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1

/-- **Reduction (PROVED): `BlockDecodeStepVar n → BlockDecodeStep n`.**  Pair the
recovered variable with the *direction read straight off the code* (proved correct
by `codeOf_snd_eq_deepPathV`).  This discharges the direction component of the
decode, leaving only the variable recovery as the remaining content. -/
theorem blockDecodeStep_of_var {n : Nat}
    (h : BlockDecodeStepVar n) : BlockDecodeStep n := by
  intro D w s ℓ hw
  obtain ⟨stepVar, hsv⟩ := h D w s ℓ hw
  -- the full step pairs the recovered variable with the code's recorded direction
  refine ⟨fun σ code prev => (stepVar σ code prev, code.2), ?_⟩
  intro ρ hρ i hi
  -- the entry is `(variable, direction)`; recover each component
  have hv := hsv ρ hρ i hi
  have hd := codeOf_snd_eq_deepPathV hw hρ hi
  -- assemble: (var, code.2) = ((deepPathV …).get ⟨i⟩).1, .2) = the entry
  rw [Prod.ext_iff]
  refine ⟨hv, ?_⟩
  -- the second component is exactly the code's direction = the entry's direction
  exact hd

/-- Prefix-recovery induction: for a bad `ρ`, the `i`-fold decoder driven by a
correct `step` reproduces exactly the length-`i` deep-path prefix.  Fully proved by
induction on `i` using the single-block step. -/
theorem decodeAux_eq_take {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    (step : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → (Fin n × Bool))
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ)
    (hcorrect : ∀ i (hi : i < s),
        step (encode₁ D s ρ) (codeOf D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = (deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩) :
    ∀ i, i ≤ s →
      decodeAux step (encode₁ D s ρ) s (codeOf D w s hw ρ) i
        = (deepPathV (dnfRestrict ρ D)).take i
  | 0, _ => by simp [decodeAux]
  | (i + 1), hi => by
      have hi' : i < s := by omega
      rw [decodeAux_succ step (encode₁ D s ρ) s (codeOf D w s hw ρ) i hi']
      rw [decodeAux_eq_take hw step hρ hcorrect i (by omega)]
      rw [hcorrect i hi']
      -- (deepPathV …).take i ++ [(deepPathV …).get ⟨i,_⟩] = (deepPathV …).take (i+1)
      rw [List.get_eq_getElem]
      exact (List.take_succ_append_getElem _ i (lt_deepPathV_length_of_bad hρ hi')).symm

/-- **The fold reduction (PROVED): `BlockDecodeStep n → TouchedRecoverable n`.**
Given the per-step recovery function, the `s`-fold `decodeAux` rebuilds the entire
deep-path prefix `(deepPathV (D|ρ)).take s`, whose variables are exactly the touched
set.  The prefix induction (`decodeAux … i = (deepPathV (D|ρ)).take i`) is fully
discharged in `decodeAux_eq_take`; this realizes the previously-open "obvious
`s`-fold fold ... by induction on `i`". -/
theorem touchedRecoverable_of_blockStep {n : Nat}
    (h : BlockDecodeStep n) : TouchedRecoverable n := by
  intro D w s ℓ hw
  unfold BlockDecodeStep at h
  obtain ⟨step, hstep⟩ := h D w s ℓ hw
  -- `hstep : ∀ ρ hρ i hi, step … = (deepPathV (D|ρ)).get …`
  refine ⟨fun σ code => ((decodeAux step σ s code s).map Prod.fst).toFinset, ?_⟩
  intro ρ hρ
  have hfold : decodeAux step (encode₁ D s ρ) s (codeOf D w s hw ρ) s
      = (deepPathV (dnfRestrict ρ D)).take s :=
    decodeAux_eq_take hw step hρ (fun i hi => hstep ρ hρ i hi) s (le_refl s)
  simp only []
  rw [hfold, ← touchedVars_eq_deepPathV D s ρ]

/-- **From recoverability, `ρ` is determined by `encode ρ`.**  If `σ = encode₁ ρ`
and the touched set is recoverable, then `ρ v = if v ∈ touched then none else σ v`.
-/
theorem ρ_eq_of_encode {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    ρ = fun v => if v ∈ touchedVars D s ρ then none else encode₁ D s ρ v := by
  funext v
  by_cases hv : v ∈ touchedVars D s ρ
  · simp only [if_pos hv]; exact touchedVars_free D s ρ v hv
  · simp only [if_neg hv]
    unfold encode₁
    have : dlookup D s ρ v = none := (dlookup_eq_none_iff D s ρ v).mpr hv
    rw [this]

/-- **The reduction from recoverability to the term switching lemma (PROVED).** -/
theorem switchingLemmaTerm_of_recoverable {n : Nat} {D : DNF n}
    (hD : SimpleDNF D) (hrec : TouchedRecoverable n) (w s ℓ : Nat)
    (hwD : widthDNF D ≤ w) :
    (badSetTerm D s ℓ).card
      ≤ (restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s := by
  classical
  -- Degenerate width: if the bad set is empty (which it is when w = 0), bound is 0.
  by_cases hw : 0 < w
  · -- Substantive case: build the injection and invoke the cardinality backbone.
    obtain ⟨rec, hreceq⟩ := hrec D w s ℓ hw
    -- σ-membership: σ ∈ restrictionsWithStars n (ℓ - s)
    have hmem : ∀ ρ ∈ badSetTerm D s ℓ,
        (encode D w s hw ρ).1 ∈ restrictionsWithStars n (ℓ - s) := by
      intro ρ hρ
      rw [mem_restrictionsWithStars]
      exact stars_encode₁ hD hρ
    -- Injectivity from recoverability: decode ∘ encode = id on the bad set.
    have hinj : Set.InjOn (encode D w s hw) ↑(badSetTerm D s ℓ) := by
      intro ρ hρ ρ' hρ' heq
      have hρmem : ρ ∈ badSetTerm D s ℓ := by simpa using hρ
      have hρ'mem : ρ' ∈ badSetTerm D s ℓ := by simpa using hρ'
      -- σ = σ' and code = code'
      have hσ : encode₁ D s ρ = encode₁ D s ρ' := congrArg Prod.fst heq
      have hcode : codeOf D w s hw ρ = codeOf D w s hw ρ' := congrArg Prod.snd heq
      -- recovered touched sets agree
      have ht : (touchedVars D s ρ).toFinset = (touchedVars D s ρ').toFinset := by
        rw [← hreceq ρ hρmem, ← hreceq ρ' hρ'mem, hσ, hcode]
      -- ρ = ρ' via the determination lemma
      rw [ρ_eq_of_encode D s ρ, ρ_eq_of_encode D s ρ']
      funext v
      have hmemv : (v ∈ touchedVars D s ρ) = (v ∈ touchedVars D s ρ') := by
        have := congrArg (fun (F : Finset (Fin n)) => v ∈ F) ht
        simpa [List.mem_toFinset] using this
      by_cases hvv : v ∈ touchedVars D s ρ
      · have hvv' : v ∈ touchedVars D s ρ' := by rw [← hmemv]; exact hvv
        simp only [if_pos hvv, if_pos hvv']
      · have hvv' : v ∉ touchedVars D s ρ' := by rw [← hmemv]; exact hvv
        simp only [if_neg hvv, if_neg hvv']
        exact congrFun hσ v
    have hc : (badSetTerm D s ℓ).card
        ≤ (restrictionsWithStars n (ℓ - s)).card * (2 * w) ^ s :=
      card_le_mul_pow_of_injOn (badSetTerm D s ℓ) (restrictionsWithStars n (ℓ - s))
        w s (encode D w s hw) hmem hinj
    refine le_trans hc ?_
    apply Nat.mul_le_mul (le_refl _)
    exact Nat.pow_le_pow_left (by omega) s
  · -- w = 0: then widthDNF D = 0, so D|ρ has only empty terms, tree depth ≤ s only at s = 0.
    push_neg at hw
    have hw0 : w = 0 := Nat.le_zero.mp hw
    subst hw0
    -- every restricted tree has depth 0
    have hdepth0 : ∀ ρ : Restriction n,
        dtDepth (termCanonicalDT (dnfRestrict ρ D)) = 0 := by
      intro ρ
      apply Nat.le_zero.mp
      refine le_trans (dtDepth_termCanonicalDT_le _) ?_
      have hwr : widthDNF (dnfRestrict ρ D) = 0 := by
        have := widthDNF_dnfRestrict_le ρ D; omega
      rw [dnfSize_eq_zero_of_width_zero _ hwr]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · -- s = 0: (8·0)^0 = 1; badSet ⊆ restrictionsWithStars n ℓ
      subst hs
      simp only [Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_zero]
      exact Finset.card_le_card (badSetTerm_subset D 0 ℓ)
    · -- s > 0: badSet empty
      have hempty : badSetTerm D s ℓ = ∅ := by
        rw [Finset.eq_empty_iff_forall_not_mem]
        intro ρ hρ
        have := ((mem_badSetTerm ρ).mp hρ).2
        rw [hdepth0 ρ] at this
        omega
      rw [hempty]; simp

/-! ## 7. Capstone

The clean term switching lemma for *simple* DNFs (proper conjunctions — the
standard setting), reduced to the single isolated recovery hypothesis. -/

/-- The term switching lemma restricted to simple DNFs (each term a proper
conjunction). -/
def SwitchingLemmaTermSimple (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat), SimpleDNF D → widthDNF D ≤ w →
    (badSetTerm D s ℓ).card ≤ (restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s

/-- **CAPSTONE (PROVED, modulo the isolated `TouchedRecoverable`).**  The Razborov
encoding's injectivity — reduced to the single recovery `def : Prop`
`TouchedRecoverable` — yields the term switching lemma for simple DNFs. -/
theorem switchingLemmaTermSimple_of_recoverable {n : Nat}
    (hrec : TouchedRecoverable n) : SwitchingLemmaTermSimple n := by
  intro D w s ℓ hD hwD
  exact switchingLemmaTerm_of_recoverable hD hrec w s ℓ hwD

/-- **CAPSTONE (PROVED, modulo the TIGHTER isolated `BlockDecodeStep`).**  The whole
term switching lemma for simple DNFs now follows from the strictly smaller, single
per-block decode step `BlockDecodeStep` — the entire `s`-fold decode and the
recovery-to-injectivity reduction are proved (`touchedRecoverable_of_blockStep`
then `switchingLemmaTermSimple_of_recoverable`).  This sharpens the previous
isolation: the remaining content is a *single deep-path entry recovery*, not the
whole touched-set recovery. -/
theorem switchingLemmaTermSimple_of_blockStep {n : Nat}
    (hstep : BlockDecodeStep n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_recoverable (touchedRecoverable_of_blockStep hstep)

/-- **CAPSTONE (PROVED, modulo the STRICTLY SMALLER `BlockDecodeStepVar`).**  The
term switching lemma for simple DNFs follows from recovering only the *variable* of
each deep-path entry: the direction half is discharged by `codeOf_snd_eq_deepPathV`
(`blockDecodeStep_of_var`), the `s`-fold decode and the recovery-to-injectivity
reduction are all proved.  This is the tightest current isolation — a single
`Fin n`-valued per-block recovery. -/
theorem switchingLemmaTermSimple_of_blockStepVar {n : Nat}
    (hstep : BlockDecodeStepVar n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_blockStep (blockDecodeStep_of_var hstep)

/-! ## 8. Within-block indexing infrastructure (NEW, fully proved)

This section discharges the *within-block indexing* layer of the decode: given the
i-th deep **term-block** (as a contiguous slice of `deepPathV (D|ρ)`), the i-th deep
*variable* is its `codeBlockPos`-th element, and the within-block position fits in
`Fin w` (so it survives the `% w` in `codeOf`).  Everything here is ρ-independent
plumbing; it reduces `BlockDecodeStepVar` to the single genuinely-hard obligation of
recovering the i-th deep block ρ-independently (`DeepBlockRecoverable`, below).

The pieces:
* `termWidth_assignTerm_le` / `widthDNF_assignVar_le` — residualizing never widens.
* `deepBlockLens_le` / `deepBlockLensQ_le` — every deep term-block length is `≤
  widthDNF`, so within-block positions are `< widthDNF ≤ w` and the `% w` in `codeOf`
  is the identity.
* `blockOfIndex` / `blockOf_get` — generic block-tiling: a list tiled by block
  lengths `bs` has its `i`-th element equal to the `blockPosOfIndex`-th element of the
  block containing `i`.
* `deepBlock` + `deepPathV_get_eq_deepBlock` — the i-th deep variable is the
  `codeBlockPos`-th variable of the i-th deep block. -/

/-- `assignTerm` produces a no-wider term (it returns a sublist of the input). -/
theorem termWidth_assignTerm_le {n : Nat} (v : Fin n) (b : Bool) (t t' : Term n)
    (h : assignTerm v b t = some t') : termWidth t' ≤ termWidth t := by
  unfold termWidth
  have hsub : t'.Sublist t := by
    induction t generalizing t' with
    | nil =>
        simp only [assignTerm, Option.some.injEq] at h; subst h; exact List.Sublist.refl _
    | cons l t ih =>
        simp only [assignTerm] at h
        by_cases hlv : l.var = v
        · by_cases hls : l.sign = b
          · simp only [if_pos hlv, if_pos hls] at h
            exact (ih t' h).trans (List.sublist_cons_self l t)
          · simp only [if_pos hlv, if_neg hls] at h; exact absurd h (by simp)
        · simp only [if_neg hlv] at h
          cases hrec : assignTerm v b t with
          | some t'' =>
              simp only [hrec, Option.some.injEq] at h; subst h
              exact (ih t'' hrec).cons₂ l
          | none => simp only [hrec] at h; exact absurd h (by simp)
  exact hsub.length_le

/-- Residualizing a DNF never increases its width: `widthDNF (assignVar v b D) ≤
widthDNF D`. -/
theorem widthDNF_assignVar_le {n : Nat} (v : Fin n) (b : Bool) :
    ∀ (D : DNF n), widthDNF (assignVar v b D) ≤ widthDNF D
  | [] => by simp [assignVar]
  | t :: D => by
      rw [show assignVar v b (t :: D)
            = (match assignTerm v b t with
                | some t' => t' :: assignVar v b D
                | none => assignVar v b D) from by
            simp only [assignVar, List.filterMap_cons]; cases assignTerm v b t <;> rfl]
      cases hres : assignTerm v b t with
      | none =>
          simp only [hres]; rw [widthDNF_cons]
          exact le_trans (widthDNF_assignVar_le v b D) (Nat.le_max_right _ _)
      | some t' =>
          simp only [hres, widthDNF_cons]
          have h1 : termWidth t' ≤ termWidth t := termWidth_assignTerm_le v b t t' hres
          have h2 := widthDNF_assignVar_le v b D
          omega

mutual
/-- **Every deep term-block length is bounded by the DNF width.**  Each entry of
`deepBlockLens D` is `≤ widthDNF D` (a term-block is the variables of one term, of
length `≤ widthDNF D`). -/
theorem deepBlockLens_le {n : Nat} :
    ∀ (D : DNF n), ∀ b ∈ deepBlockLens D, b ≤ widthDNF D
  | [], b, hb => by rw [deepBlockLens] at hb; simp at hb
  | [] :: D, b, hb => by rw [deepBlockLens] at hb; simp at hb
  | (l :: t) :: D, b, hb => by
      rw [show deepBlockLens ((l :: t) :: D)
            = (1 + t.length) ::
                (if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                    ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
                  then deepBlockLensQ t (assignVar l.var true ((l :: t) :: D))
                  else deepBlockLensQ t (assignVar l.var false ((l :: t) :: D)))
            from by rw [deepBlockLens]] at hb
      rw [widthDNF_cons]
      have hw1 : termWidth (l :: t) = 1 + t.length := by
        unfold termWidth; simp [Nat.add_comm]
      rcases List.mem_cons.mp hb with h | h
      · subst h; rw [hw1]; exact Nat.le_max_left _ _
      · have htlt : t.length ≤ termWidth (l :: t) := by rw [hw1]; omega
        by_cases hc : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
            ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
        · rw [if_pos hc] at h
          have hb' := deepBlockLensQ_le t (assignVar l.var true ((l :: t) :: D)) b h
          have hww := widthDNF_assignVar_le l.var true ((l :: t) :: D)
          rw [widthDNF_cons] at hww; omega
        · rw [if_neg hc] at h
          have hb' := deepBlockLensQ_le t (assignVar l.var false ((l :: t) :: D)) b h
          have hww := widthDNF_assignVar_le l.var false ((l :: t) :: D)
          rw [widthDNF_cons] at hww; omega
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)

/-- Block-helper bound: every entry of `deepBlockLensQ vars D` is bounded by
`max vars.length (widthDNF D)`. -/
theorem deepBlockLensQ_le {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), ∀ b ∈ deepBlockLensQ vars D,
      b ≤ max vars.length (widthDNF D)
  | [], D, b, hb => by
      rw [show deepBlockLensQ ([] : Term n) D = deepBlockLens D from by
            rw [deepBlockLensQ]] at hb
      have := deepBlockLens_le D b hb
      simp only [List.length_nil]; omega
  | l :: vs, D, b, hb => by
      rw [show deepBlockLensQ (l :: vs) D
            = (if dtDepth (queryTerm vs (assignVar l.var false D))
                  ≤ dtDepth (queryTerm vs (assignVar l.var true D))
                then deepBlockLensQ vs (assignVar l.var true D)
                else deepBlockLensQ vs (assignVar l.var false D))
            from by rw [deepBlockLensQ]] at hb
      by_cases hc : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · rw [if_pos hc] at hb
        have := deepBlockLensQ_le vs (assignVar l.var true D) b hb
        have hw := widthDNF_assignVar_le l.var true D
        simp only [List.length_cons]; omega
      · rw [if_neg hc] at hb
        have := deepBlockLensQ_le vs (assignVar l.var false D) b hb
        have hw := widthDNF_assignVar_le l.var false D
        simp only [List.length_cons]; omega
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

/-- The block of a tiled list containing global index `i`, mirroring
`blockPosOfIndex`: descend past whole preceding blocks, then take the current
block. -/
def blockOfIndex {α : Type*} : List Nat → Nat → List α → List α
  | [], _, L => L
  | b :: bs, i, L => if i < b then L.take b else blockOfIndex bs (i - b) (L.drop b)

/-- **Generic block-tiling element law.**  If a list `L` is tiled by block lengths
`bs` (with `i < bs.sum` and `i < L.length`), then its `i`-th element equals the
`blockPosOfIndex bs i`-th element of the block `blockOfIndex bs i L` containing `i`.
A pure list fact (no `ρ`), the indexing core of the decode. -/
theorem blockOf_get {α : Type*} :
    ∀ (bs : List Nat) (i : Nat) (L : List α), i < bs.sum → i < L.length →
      L[i]? = (blockOfIndex bs i L)[blockPosOfIndex bs i]?
  | [], i, L, h, _ => by simp [List.sum_nil] at h
  | b :: bs, i, L, h, hL => by
      rw [blockOfIndex, blockPosOfIndex]
      by_cases hib : i < b
      · simp only [if_pos hib]; rw [List.getElem?_take_of_lt hib]
      · simp only [if_neg hib]
        have hlt : i - b < bs.sum := by rw [List.sum_cons] at h; omega
        have hL' : i - b < (L.drop b).length := by rw [List.length_drop]; omega
        rw [← blockOf_get bs (i - b) (L.drop b) hlt hL', List.getElem?_drop]
        congr 1; omega

/-- The i-th **deep term-block** of `D|ρ`: the contiguous slice of the deep path
`deepPathV (D|ρ)` carved off by the term-block lengths `deepBlockLens (D|ρ)`. -/
noncomputable def deepBlock {n : Nat} (D : DNF n) (ρ : Restriction n) (i : Nat) :
    List (Fin n × Bool) :=
  blockOfIndex (deepBlockLens (dnfRestrict ρ D)) i (deepPathV (dnfRestrict ρ D))

/-- **The i-th deep variable is the `codeBlockPos`-th variable of the i-th deep
block (PROVED).**  Combines the generic tiling law `blockOf_get` with
`deepBlockLens_sum_eq` (blocks tile the deep path).  This is the precise within-block
indexing equation the decode uses, fully ρ-independent in its statement form once the
block is recovered. -/
theorem deepPathV_get_eq_deepBlock {n : Nat} (D : DNF n) (ρ : Restriction n)
    (i : Nat) (hi : i < (deepPathV (dnfRestrict ρ D)).length) :
    ((deepPathV (dnfRestrict ρ D)).map Prod.fst)[i]?
      = ((deepBlock D ρ i).map Prod.fst)[codeBlockPos D ρ i]? := by
  unfold deepBlock codeBlockPos
  -- map commutes with getElem? and with blockOfIndex on the original list
  set bs := deepBlockLens (dnfRestrict ρ D) with hbs
  set L := deepPathV (dnfRestrict ρ D) with hL
  have hsum : i < bs.sum := by rw [hbs, deepBlockLens_sum_eq]; rw [hL] at hi; exact hi
  have hmapget : (L.map Prod.fst)[i]? = (L[i]?).map Prod.fst := by
    rw [List.getElem?_map]
  have key := blockOf_get bs i L hsum (by rw [hL] at hi ⊢; exact hi)
  rw [hmapget, key]
  -- RHS: ((blockOfIndex bs i L).map fst)[blockPosOfIndex bs i]?
  --    = ((blockOfIndex bs i L)[blockPosOfIndex bs i]?).map fst
  rw [List.getElem?_map]

/-- `codeBlockPos` of an in-range deep index is `< widthDNF (D|ρ)` — so it survives
the `% w` in `codeOf` when `widthDNF D ≤ w`.  Uses `blockPosOfIndex_deepBlockLens_lt`
and `deepBlockLens_le`. -/
theorem codeBlockPos_lt_width {n : Nat} (D : DNF n) (ρ : Restriction n) (i : Nat)
    (hi : i < (deepPathV (dnfRestrict ρ D)).length) :
    codeBlockPos D ρ i < widthDNF (dnfRestrict ρ D) := by
  unfold codeBlockPos
  obtain ⟨b, hbmem, hblt⟩ := blockPosOfIndex_deepBlockLens_lt (dnfRestrict ρ D) i hi
  exact lt_of_lt_of_le hblt (deepBlockLens_le (dnfRestrict ρ D) b hbmem)

/-! ### IMPORTANT honesty note: `BlockDecodeStepVar` is too strong (and FALSE)

`codeOf` records the within-block position as `codeBlockPos D ρ i % w`.  When `w <
widthDNF (dnfRestrict ρ D)` this `% w` genuinely DESTROYS information (two distinct
within-block positions collide), so the i-th variable is NOT recoverable from the code.
`BlockDecodeStepVar n` quantifies over ALL `w` with `0 < w` and imposes NO width
constraint, hence it is **false** for any `n, D, s, ℓ` with a bad `ρ` and a chosen `w
< widthDNF (D|ρ)`.  (It is additionally false for `n = 0`, where it asserts a total
function into the empty type `Fin 0`.)

This is harmless for the switching lemma: the only place recovery is *used*
(`switchingLemmaTerm_of_recoverable`) supplies `w` with `widthDNF D ≤ w`.  So the
*correct* target is the **width-bounded** recovery `DeepBlockRecoverableW` below, which
carries `widthDNF D ≤ w`; we PROVE it yields `SwitchingLemmaTermSimple` directly.  We
keep the original `BlockDecodeStepVar` only for the (vacuous, for small `w`) interface
above. -/

/-- **The isolated deep-block recovery (the genuine Razborov heart), width-bounded.**
A ρ-independent recovery of the i-th deep term-block of `D|ρ` (its `(var,dir)` slice)
from `σ = encode₁ ρ`, the i-th code entry, and the length-`i` decoded prefix — under
the standard width hypothesis `widthDNF D ≤ w` (the regime the switching lemma uses).
This is strictly the term-identification content; all within-block indexing, the `% w`
totality, and the direction half are discharged.  Isolated `def : Prop`, NOT an
axiom, NOT asserted true. -/
def DeepBlockRecoverableW (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w), widthDNF D ≤ w →
    ∃ blk : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → List (Fin n × Bool),
      ∀ (ρ : Restriction n), ρ ∈ badSetTerm D s ℓ → ∀ (i : Nat) (hi : i < s),
        blk (encode₁ D s ρ) (codeOf D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = deepBlock D ρ i

/-- **Per-step variable recovery from a recovered deep block (PROVED).**  For a bad
`ρ` with `widthDNF D ≤ w`, the i-th deep variable is the `code.1`-th variable of
`deepBlock D ρ i`: the `% w` in `codeOf` is the identity (by `codeBlockPos_lt_width`
and `widthDNF (D|ρ) ≤ widthDNF D ≤ w`), and the indexing is
`deepPathV_get_eq_deepBlock`.  This is the full per-step content given the block. -/
theorem deepVar_eq_block_getElem {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    (hwD : widthDNF D ≤ w) {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ)
    {i : Nat} (hi : i < s) :
    ((deepBlock D ρ i).map Prod.fst)[(codeOf D w s hw ρ ⟨i, hi⟩).1.val]?
      = some (((deepPathV (dnfRestrict ρ D)).get
          ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1) := by
  have hlen : i < (deepPathV (dnfRestrict ρ D)).length :=
    lt_deepPathV_length_of_bad hρ hi
  -- the code's first component is `codeBlockPos D ρ i % w = codeBlockPos D ρ i`
  have hwr : widthDNF (dnfRestrict ρ D) ≤ w :=
    le_trans (widthDNF_dnfRestrict_le ρ D) hwD
  have hpos_lt : codeBlockPos D ρ i < w :=
    lt_of_lt_of_le (codeBlockPos_lt_width D ρ i hlen) hwr
  -- compute (codeOf …).1.val
  have hcode : (codeOf D w s hw ρ ⟨i, hi⟩).1.val = codeBlockPos D ρ i := by
    have hget : (dpath D s ρ).get? (⟨i, hi⟩ : Fin s).1
        = some ((deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩) := by
      show (dpath D s ρ).get? i = _
      rw [dpath_eq_deepPathV_take, List.get?_eq_getElem?, List.getElem?_take_of_lt hi,
        List.getElem?_eq_getElem hlen, List.get_eq_getElem]
    unfold codeOf
    rcases hd : (deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩ with ⟨vv, dd⟩
    rw [hd] at hget
    rw [hget]
    simp only [Nat.mod_eq_of_lt hpos_lt]
  rw [hcode]
  -- now use the indexing equation
  have hidx := deepPathV_get_eq_deepBlock D ρ i hlen
  -- LHS of hidx is ((deepPathV …).map fst)[i]? = some (get i).1
  rw [← hidx]
  rw [List.getElem?_map, List.getElem?_eq_getElem hlen, List.get_eq_getElem]
  rfl


/-! ### The width-bounded recovery chain to the switching lemma (PROVED)

We close the chain `DeepBlockRecoverableW n → SwitchingLemmaTermSimple n` with no
`Fin n` defaults (so it holds for all `n`, including `n = 0`).  The decoder
accumulates the recovered deep-path entries directly from the recovered blocks via
`getElem?`/`Option.toList`, so it never needs to invent a `Fin n`. -/

/-- A `Fin n`-default-free fold: rebuild the deep-path entry list from the recovered
blocks.  At step `i` it appends `((blk σ code_i prev)[code_i.1.val]?).toList` — exactly
one element in the in-range case, none otherwise (so it is total for every `n`). -/
def recVarFold {n w : Nat}
    (blk : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → List (Fin n × Bool))
    (σ : Restriction n) (s : Nat) (code : Fin s → Fin w × Bool) :
    Nat → List (Fin n × Bool)
  | 0 => []
  | (i + 1) =>
      let prev := recVarFold blk σ s code i
      if h : i < s then
        prev ++ (((blk σ (code ⟨i, h⟩) prev).map Prod.fst)[(code ⟨i, h⟩).1.val]?).toList.map
                  (fun v => (v, (code ⟨i, h⟩).2))
      else prev

theorem recVarFold_succ {n w : Nat}
    (blk : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → List (Fin n × Bool))
    (σ : Restriction n) (s : Nat) (code : Fin s → Fin w × Bool) (i : Nat) (h : i < s) :
    recVarFold blk σ s code (i + 1)
      = recVarFold blk σ s code i
          ++ (((blk σ (code ⟨i, h⟩) (recVarFold blk σ s code i)).map Prod.fst)[(code ⟨i, h⟩).1.val]?).toList.map
              (fun v => (v, (code ⟨i, h⟩).2)) := by
  rw [recVarFold]; simp only [h, dif_pos]

/-- **The fold reconstructs the deep-path prefix (PROVED).**  Under
`DeepBlockRecoverableW`'s recovery equation, for a bad `ρ` (with `widthDNF D ≤ w`), the
`i`-fold `recVarFold` on `σ = encode₁ ρ` and `codeOf ρ` equals `(deepPathV (D|ρ)).take
i`.  By induction on `i`, using `deepVar_eq_block_getElem` (variable) and
`codeOf_snd_eq_deepPathV` (direction). -/
theorem recVarFold_eq_take {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    (hwD : widthDNF D ≤ w)
    (blk : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → List (Fin n × Bool))
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ)
    (hblk : ∀ (i : Nat) (hi : i < s),
        blk (encode₁ D s ρ) (codeOf D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = deepBlock D ρ i) :
    ∀ i, i ≤ s →
      recVarFold blk (encode₁ D s ρ) s (codeOf D w s hw ρ) i
        = (deepPathV (dnfRestrict ρ D)).take i
  | 0, _ => by simp [recVarFold]
  | (i + 1), hi => by
      have hi' : i < s := by omega
      rw [recVarFold_succ blk (encode₁ D s ρ) s (codeOf D w s hw ρ) i hi']
      rw [recVarFold_eq_take hw hwD blk hρ hblk i (by omega)]
      have hlen : i < (deepPathV (dnfRestrict ρ D)).length :=
        lt_deepPathV_length_of_bad hρ hi'
      have hbeq := hblk i hi'
      have hvar := deepVar_eq_block_getElem hw hwD hρ hi'
      have hdir := codeOf_snd_eq_deepPathV hw hρ hi'
      rw [hbeq, hvar]
      simp only [Option.toList, List.map_cons, List.map_nil]
      rw [hdir]
      have hentry : (((deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩).1,
                      ((deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩).2)
                    = (deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩ := by
        rw [Prod.mk.eta]
      rw [hentry, List.get_eq_getElem]
      exact (List.take_succ_append_getElem _ i hlen).symm

/-- **Width-bounded touched recovery (PROVED from `DeepBlockRecoverableW`).**  For the
width-`≥ widthDNF D` regime, the touched set of every bad `ρ` is recovered from
`(σ, code)` by `(recVarFold blk … s).map fst |>.toFinset`. -/
theorem touchedRecoverableW_of_deepBlockRecoverableW {n : Nat}
    (h : DeepBlockRecoverableW n) (D : DNF n) (w s ℓ : Nat) (hw : 0 < w)
    (hwD : widthDNF D ≤ w) :
    ∃ rec : Restriction n → (Fin s → Fin w × Bool) → Finset (Fin n),
      ∀ ρ ∈ badSetTerm D s ℓ,
        rec (encode₁ D s ρ) (codeOf D w s hw ρ) = (touchedVars D s ρ).toFinset := by
  obtain ⟨blk, hblk⟩ := h D w s ℓ hw hwD
  refine ⟨fun σ code => ((recVarFold blk σ s code s).map Prod.fst).toFinset, ?_⟩
  intro ρ hρ
  have hfold : recVarFold blk (encode₁ D s ρ) s (codeOf D w s hw ρ) s
      = (deepPathV (dnfRestrict ρ D)).take s :=
    recVarFold_eq_take hw hwD blk hρ (fun i hi => hblk ρ hρ i hi) s (le_refl s)
  simp only []
  rw [hfold, ← touchedVars_eq_deepPathV D s ρ]

/-- **CAPSTONE (PROVED): `DeepBlockRecoverableW n → SwitchingLemmaTermSimple n`.**
This is the correct (width-bounded) reduction.  The `% w` totality, within-block
indexing, direction half, `s`-fold, and injectivity backbone are all discharged; the
SOLE remaining mathematical content is the isolated ρ-independent block recovery
`DeepBlockRecoverableW`. -/
theorem switchingLemmaTermSimple_of_deepBlockRecoverableW {n : Nat}
    (h : DeepBlockRecoverableW n) : SwitchingLemmaTermSimple n := by
  intro D w s ℓ hD hwD
  classical
  by_cases hw : 0 < w
  · obtain ⟨rec, hreceq⟩ := touchedRecoverableW_of_deepBlockRecoverableW h D w s ℓ hw hwD
    have hmem : ∀ ρ ∈ badSetTerm D s ℓ,
        (encode D w s hw ρ).1 ∈ restrictionsWithStars n (ℓ - s) := by
      intro ρ hρ
      rw [mem_restrictionsWithStars]; exact stars_encode₁ hD hρ
    have hinj : Set.InjOn (encode D w s hw) ↑(badSetTerm D s ℓ) := by
      intro ρ hρ ρ' hρ' heq
      have hρmem : ρ ∈ badSetTerm D s ℓ := by simpa using hρ
      have hρ'mem : ρ' ∈ badSetTerm D s ℓ := by simpa using hρ'
      have hσ : encode₁ D s ρ = encode₁ D s ρ' := congrArg Prod.fst heq
      have hcode : codeOf D w s hw ρ = codeOf D w s hw ρ' := congrArg Prod.snd heq
      have ht : (touchedVars D s ρ).toFinset = (touchedVars D s ρ').toFinset := by
        rw [← hreceq ρ hρmem, ← hreceq ρ' hρ'mem, hσ, hcode]
      rw [ρ_eq_of_encode D s ρ, ρ_eq_of_encode D s ρ']
      funext v
      have hmemv : (v ∈ touchedVars D s ρ) = (v ∈ touchedVars D s ρ') := by
        have := congrArg (fun (F : Finset (Fin n)) => v ∈ F) ht
        simpa [List.mem_toFinset] using this
      by_cases hvv : v ∈ touchedVars D s ρ
      · have hvv' : v ∈ touchedVars D s ρ' := by rw [← hmemv]; exact hvv
        simp only [if_pos hvv, if_pos hvv']
      · have hvv' : v ∉ touchedVars D s ρ' := by rw [← hmemv]; exact hvv
        simp only [if_neg hvv, if_neg hvv']
        exact congrFun hσ v
    have hc : (badSetTerm D s ℓ).card
        ≤ (restrictionsWithStars n (ℓ - s)).card * (2 * w) ^ s :=
      card_le_mul_pow_of_injOn (badSetTerm D s ℓ) (restrictionsWithStars n (ℓ - s))
        w s (encode D w s hw) hmem hinj
    refine le_trans hc ?_
    apply Nat.mul_le_mul (le_refl _)
    exact Nat.pow_le_pow_left (by omega) s
  · push_neg at hw
    have hw0 : w = 0 := Nat.le_zero.mp hw
    subst hw0
    have hdepth0 : ∀ ρ : Restriction n,
        dtDepth (termCanonicalDT (dnfRestrict ρ D)) = 0 := by
      intro ρ
      apply Nat.le_zero.mp
      refine le_trans (dtDepth_termCanonicalDT_le _) ?_
      have hwr : widthDNF (dnfRestrict ρ D) = 0 := by
        have := widthDNF_dnfRestrict_le ρ D; omega
      rw [dnfSize_eq_zero_of_width_zero _ hwr]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp only [Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_zero]
      exact Finset.card_le_card (badSetTerm_subset D 0 ℓ)
    · have hempty : badSetTerm D s ℓ = ∅ := by
        rw [Finset.eq_empty_iff_forall_not_mem]
        intro ρ hρ
        have := ((mem_badSetTerm ρ).mp hρ).2
        rw [hdepth0 ρ] at this; omega
      rw [hempty]; simp

end SwitchingEncodeConstruct
end PvNP
