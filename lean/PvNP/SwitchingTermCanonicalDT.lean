import PvNP.BoundedDepthCanonicalDT
import PvNP.SwitchingLemmaStatement

/-!
# The TERM-CANONICAL decision tree of a DNF

This file builds the **term-canonical decision tree** `termCanonicalDT : DNF n →
DTree n` — the standard Håstad/Razborov *canonical decision tree* of a DNF in
which one queries whole **terms** (blocks of variables), one term-block at a
time, rather than a single literal at a time.  This is the deterministic object
on which the switching-lemma *encoding* argument is built: the path through the
tree is partitioned into consecutive "term blocks", each block querying exactly
the variables of one term (≤ `widthDNF D` of them), which is what later yields the
`(const · w)^s` counting bound.

## HONEST SCOPE STATEMENT (read this)
This is **switching-lemma INFRASTRUCTURE ONLY** — the deterministic core object.
It is **NOT** the switching lemma (which is a *probabilistic* statement about a
*random restriction* collapsing a small DNF to a *shallow* tree with high
probability), it is **NOT** a lower bound, and it does **NOT** claim P ≠ NP.

This file provides only:
* `termCanonicalDT : DNF n → DTree n`, the deterministic term-canonical tree,
  terminating by a lexicographic measure `(dnfSize D, term-block progress)`;
* `dtEval_termCanonicalDT`: the genuine, unweakened eval-correctness
  `dtEval a (termCanonicalDT D) = dnfEval a D` — REAL Boolean semantics, no proxy;
* `dtDepth_termCanonicalDT_le`: the worst-case depth bound
  `dtDepth (termCanonicalDT D) ≤ dnfSize D`.

## Construction (the SIMPLER, block-property variant)
We use the prompt's "query variables one at a time but with the term-block
property" variant.  A helper `queryTerm (vars) (D)` walks the literals of the
*first term* of the residual DNF, branching on each literal's variable and
residualizing the WHOLE DNF by that fixing; when `vars` is exhausted the term
block is complete and control returns to `termCanonicalDT` on the residual DNF.

Concretely, at the root with first term `t₁ = l :: t`:
* we query `l.var` (which lives in `t₁`, so residualizing it strictly drops
  `dnfSize`, giving the outer-recursion decrease), then
* hand the remaining literals `t` to `queryTerm`, which queries each of their
  variables (residualizing the WHOLE DNF each time) and, at the end of the
  block, recurses into `termCanonicalDT` on the fully-residualized DNF.

So along **every** root-to-leaf path the first `|t₁|` queries are exactly the
variables of the first term `t₁` (in order) — this is the *term-block structure*.
The eval-correctness is genuine because every per-variable branch residualizes
the whole DNF under the queried value via `assignVar`, and `dnfEval_assignVar`
preserves the Boolean value under any agreeing assignment.

Reused unchanged from earlier bricks:
* `DNF n`, `Term n`, `dnfEval`, `termEval`, `assignVar`, `dnfEval_assignVar`,
  `dnfSize`, `dnfSize_assignVar_le`, `dnfSize_assignVar_lt` from
  `PvNP.BoundedDepthCanonicalDT`;
* `widthDNF`, `termWidth` from `PvNP.SwitchingLemmaStatement`;
* `DTree`, `dtEval`, `dtDepth`, `dtEval_node`, `dtDepth_node` from
  `PvNP.BoundedDepthDecisionTree`;
* `Assignment n`, `Literal n`, `litEval` from `PvNP.CNFModel`.
-/

namespace PvNP
namespace SwitchingTermCanonicalDT

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open SwitchingLemmaStatement

/-! ## 1. The term-canonical decision tree

`termCanonicalDT` and its block-helper `queryTerm` are defined by a single
well-founded recursion on the lexicographic measure `(dnfSize D, vars.length)`:

* `queryTerm vars D` recurses on the *structure* of `vars` (its length strictly
  drops) while `dnfSize D` only weakly decreases — so the pair drops
  lexicographically;
* when `vars = []`, `queryTerm` calls `termCanonicalDT D`, and at that call
  `dnfSize D` is **strictly** smaller than the `dnfSize` we started the block
  with (the block began only after `termCanonicalDT` had queried the first-term
  head literal, which strictly dropped `dnfSize`).

We package this with explicit measures so termination is transparent. -/

/-! ### The term-canonical decision tree and its block helper

The **term-canonical decision tree** of a DNF, together with its block helper
`queryTerm`, defined by mutual well-founded recursion on the lexicographic
measure `(dnfSize D, vars.length + 1)` (with the second component `0` for
`termCanonicalDT`, strictly below any `queryTerm` so the block-boundary call
`queryTerm [] D → termCanonicalDT D` decreases).

`termCanonicalDT`:
* `[]` (constant false) → `leaf false`;
* `[] :: _` (first term is constant true) → `leaf true`;
* `(l :: t) :: D`: query the first term's head variable `l.var`, and in each
  child hand the remaining literals `t` of the first term to `queryTerm`, which
  finishes the term block (querying `t`'s variables) and then recurses on the
  residual DNF.  Querying `l.var` residualizes the whole DNF, so `dnfSize`
  strictly drops, which is the outer-recursion decrease.

`queryTerm vars D`: queries the variables of the literal list `vars` (the
remaining literals of the current term block), branching on each and
residualizing the WHOLE DNF `D` under the queried value; when `vars` is exhausted
it returns control to `termCanonicalDT D` (next term block). -/
mutual
/-- The **term-canonical decision tree** of a DNF (see the section comment above
for the construction and termination measure). -/
def termCanonicalDT {n : Nat} : DNF n → DTree n
  | [] => DTree.leaf false
  | [] :: _ => DTree.leaf true
  | (l :: t) :: D =>
      DTree.node l.var
        (queryTerm t (assignVar l.var false ((l :: t) :: D)))
        (queryTerm t (assignVar l.var true ((l :: t) :: D)))
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)

/-- The block helper for `termCanonicalDT` (see the section comment above). -/
def queryTerm {n : Nat} : Term n → DNF n → DTree n
  | [], D => termCanonicalDT D
  | l :: vs, D =>
      DTree.node l.var
        (queryTerm vs (assignVar l.var false D))
        (queryTerm vs (assignVar l.var true D))
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

/-! ## 2. Eval-correctness — THE DELIVERABLE

We first prove the helper's eval-correctness (`queryTerm` evaluates the residual
DNF), then derive the main statement.  Both go by the same well-founded
recursion as the definitions. -/

mutual
/-- Eval-correctness of the block helper: `queryTerm vars D` evaluates, under any
assignment `a`, to exactly the DNF value `dnfEval a D`.  The variables in `vars`
are queried and the DNF residualized along the matching branch, but residualizing
under the queried value preserves `dnfEval` (by `dnfEval_assignVar`), so the
value is unchanged. -/
theorem dtEval_queryTerm {n : Nat} (a : Assignment n) :
    ∀ (vars : Term n) (D : DNF n),
      dtEval a (queryTerm vars D) = dnfEval a D
  | [], D => by
      rw [show queryTerm [] D = termCanonicalDT D from by rw [queryTerm]]
      exact dtEval_termCanonicalDT a D
  | l :: vs, D => by
      rw [show queryTerm (l :: vs) D
            = DTree.node l.var
                (queryTerm vs (assignVar l.var false D))
                (queryTerm vs (assignVar l.var true D)) from by rw [queryTerm]]
      rw [dtEval_node]
      cases hv : a l.var with
      | true =>
          simp only [hv, if_true]
          rw [dtEval_queryTerm a vs (assignVar l.var true D)]
          exact dnfEval_assignVar a l.var true hv D
      | false =>
          simp only [hv, Bool.false_eq_true, if_false]
          rw [dtEval_queryTerm a vs (assignVar l.var false D)]
          exact dnfEval_assignVar a l.var false hv D
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

/-- **`dtEval_termCanonicalDT` — THE DELIVERABLE.**  For every assignment `a` and
DNF `D`, the term-canonical decision tree computes exactly the DNF's Boolean
function: `dtEval a (termCanonicalDT D) = dnfEval a D`.  This is the genuine,
unweakened eval-correctness — REAL Boolean semantics, no proxy, no weakening. -/
theorem dtEval_termCanonicalDT {n : Nat} (a : Assignment n) :
    ∀ (D : DNF n), dtEval a (termCanonicalDT D) = dnfEval a D
  | [] => by simp [termCanonicalDT]
  | [] :: D => by
      simp [termCanonicalDT, dnfEval_cons, termEval_nil]
  | (l :: t) :: D => by
      rw [show termCanonicalDT ((l :: t) :: D)
            = DTree.node l.var
                (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                (queryTerm t (assignVar l.var true ((l :: t) :: D))) from by
            rw [termCanonicalDT]]
      rw [dtEval_node]
      cases hv : a l.var with
      | true =>
          simp only [hv, if_true]
          rw [dtEval_queryTerm a t (assignVar l.var true ((l :: t) :: D))]
          exact dnfEval_assignVar a l.var true hv ((l :: t) :: D)
      | false =>
          simp only [hv, Bool.false_eq_true, if_false]
          rw [dtEval_queryTerm a t (assignVar l.var false ((l :: t) :: D))]
          exact dnfEval_assignVar a l.var false hv ((l :: t) :: D)
  termination_by D => (dnfSize D, 0)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
end

/-! ### Structural facts about `assignTerm` / `assignVar` (for the depth bound)

These are elementary facts needed by the residual-aware depth argument:
`assignTerm` only ever returns a sublist of the input term whose literals keep
their identity and avoid the assigned variable, and `assignVar` commutes with
itself across different (or equal) fixings. -/

/-- Every literal surviving `assignTerm v b t` was a literal of `t`. -/
theorem assignTerm_mem_of_mem {n : Nat} (v : Fin n) (b : Bool) :
    ∀ (t t' : Term n), assignTerm v b t = some t' → ∀ l ∈ t', l ∈ t
  | [], t', h, l, hl => by
      simp only [assignTerm, Option.some.injEq] at h; subst h
      exact absurd hl (List.not_mem_nil l)
  | (m :: t), t', h, l, hl => by
      simp only [assignTerm] at h
      by_cases hmv : m.var = v
      · by_cases hms : m.sign = b
        · simp only [if_pos hmv, if_pos hms] at h
          exact List.mem_cons_of_mem m (assignTerm_mem_of_mem v b t t' h l hl)
        · simp only [if_pos hmv, if_neg hms] at h; exact absurd h (by simp)
      · simp only [if_neg hmv] at h
        cases hrec : assignTerm v b t with
        | some t'' =>
            simp only [hrec, Option.some.injEq] at h
            subst h
            rcases List.mem_cons.mp hl with h | h
            · subst h; exact List.mem_cons_self l t
            · exact List.mem_cons_of_mem m (assignTerm_mem_of_mem v b t t'' hrec l h)
        | none => simp only [hrec] at h; exact absurd h (by simp)

/-- No literal surviving `assignTerm v b t` is on the assigned variable `v`. -/
theorem assignTerm_var_ne {n : Nat} (v : Fin n) (b : Bool) :
    ∀ (t t' : Term n), assignTerm v b t = some t' → ∀ l ∈ t', l.var ≠ v
  | [], t', h, l, hl => by
      simp only [assignTerm, Option.some.injEq] at h; subst h
      exact absurd hl (List.not_mem_nil l)
  | (m :: t), t', h, l, hl => by
      simp only [assignTerm] at h
      by_cases hmv : m.var = v
      · by_cases hms : m.sign = b
        · simp only [if_pos hmv, if_pos hms] at h
          exact assignTerm_var_ne v b t t' h l hl
        · simp only [if_pos hmv, if_neg hms] at h; exact absurd h (by simp)
      · simp only [if_neg hmv] at h
        cases hrec : assignTerm v b t with
        | some t'' =>
            simp only [hrec, Option.some.injEq] at h
            subst h
            rcases List.mem_cons.mp hl with h | h
            · subst h; exact hmv
            · exact assignTerm_var_ne v b t t'' hrec l h
        | none => simp only [hrec] at h; exact absurd h (by simp)

/-! ## 3. Depth bound

The term-canonical tree queries one variable per query node and residualizes.
The clean, fully-proved bound here is `dtDepth (termCanonicalDT D) ≤ dnfSize D`:
the depth is at most the DNF's total literal-occurrence count.  This is the
deterministic worst-case baseline the switching lemma later improves under a
random restriction.

To make the constant-`1` bound provable we use a **residual-aware** helper
measure `stripSize vars D`: the worst-case `dnfSize` of the DNF after `D` is
residualized by *all* the variables of `vars` (over both branch choices per
variable).  The block helper `queryTerm vars D` adds exactly `vars.length` query
levels and then recurses into `termCanonicalDT` on a DNF whose `dnfSize` is `≤
stripSize vars D`, giving `dtDepth (queryTerm vars D) ≤ vars.length + stripSize
vars D`.  The key combinatorial fact `stripSize_firstTermBlock_le` then shows
that residualizing by the first term's tail kills that term, so the size handed
to the next block is `≤ dnfSize D`, yielding the tight overall bound. -/

/-- Residual-aware size measure: the worst-case `dnfSize` of `D` after it is
residualized by all variables of `vars` (taking the max over branch choices). -/
def stripSize {n : Nat} : Term n → DNF n → Nat
  | [], D => dnfSize D
  | l :: vs, D =>
      max (stripSize vs (assignVar l.var false D))
          (stripSize vs (assignVar l.var true D))

@[simp] theorem stripSize_nil {n : Nat} (D : DNF n) :
    stripSize [] D = dnfSize D := rfl

@[simp] theorem stripSize_cons {n : Nat} (l : Literal n) (vs : Term n)
    (D : DNF n) :
    stripSize (l :: vs) D
      = max (stripSize vs (assignVar l.var false D))
            (stripSize vs (assignVar l.var true D)) := rfl

/-- `stripSize` never exceeds `dnfSize` (each residualization is non-increasing,
by `dnfSize_assignVar_le`). -/
theorem stripSize_le_dnfSize {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), stripSize vars D ≤ dnfSize D
  | [], D => by simp
  | l :: vs, D => by
      rw [stripSize_cons]
      have h0 := stripSize_le_dnfSize vs (assignVar l.var false D)
      have h1 := stripSize_le_dnfSize vs (assignVar l.var true D)
      have hle0 := dnfSize_assignVar_le l.var false D
      have hle1 := dnfSize_assignVar_le l.var true D
      omega

/-- **Key block-stripping bound.**  If every literal of the first term `t₀` has
its variable among `vars`, then residualizing the whole DNF `t₀ :: D'` by all of
`vars` kills the first term, so the stripped size is bounded by that of the rest:
`stripSize vars (t₀ :: D') ≤ stripSize vars D'` (and hence `≤ dnfSize D'`). -/
theorem stripSize_firstTermBlock_le {n : Nat} :
    ∀ (vars : Term n) (t₀ : Term n) (D' : DNF n),
      (∀ l ∈ t₀, l.var ∈ vars.map (·.var)) →
      stripSize vars (t₀ :: D') ≤ stripSize vars D'
  | [], t₀, D', hsub => by
      -- no vars left; then t₀ must be empty (every literal's var is in []),
      -- so t₀ = [] and dnfSize (t₀ :: D') = dnfSize D'.
      cases t₀ with
      | nil => simp [stripSize_nil]
      | cons l t =>
          exact absurd (hsub l (List.mem_cons_self l t)) (by simp)
  | v :: vs, t₀, D', hsub => by
      rw [stripSize_cons, stripSize_cons]
      -- residualize by v.var on both DNFs; recurse with the smaller t₀.
      have key : ∀ (b : Bool),
          stripSize vs (assignVar v.var b (t₀ :: D'))
            ≤ stripSize vs (assignVar v.var b D') := by
        intro b
        -- assignVar v.var b (t₀ :: D') is either D'' (term died) or t₀' :: D''
        -- where t₀' = assignTerm v.var b t₀ has all its vars still in vs ∪ {v.var};
        -- but v.var is fixed, so the surviving literals of t₀' have vars in vs.
        rw [show assignVar v.var b (t₀ :: D')
              = (match assignTerm v.var b t₀ with
                  | some t' => t' :: assignVar v.var b D'
                  | none => assignVar v.var b D') from by
              simp only [assignVar, List.filterMap_cons]
              cases assignTerm v.var b t₀ <;> rfl]
        cases hres : assignTerm v.var b t₀ with
        | none => simp only [hres]; exact Nat.le_refl _
        | some t' =>
            simp only [hres]
            -- every literal of t' has var in vs (its var is in t₀'s vars,
            -- which lie in v.var :: vs.map var, and v.var was stripped from t').
            apply stripSize_firstTermBlock_le vs t' (assignVar v.var b D')
            intro l hl
            have hlt₀ : l ∈ t₀ := assignTerm_mem_of_mem v.var b t₀ t' hres l hl
            have hlne : l.var ≠ v.var :=
              assignTerm_var_ne v.var b t₀ t' hres l hl
            have hmem := hsub l hlt₀
            simp only [List.map_cons, List.mem_cons] at hmem
            rcases hmem with h | h
            · exact absurd h hlne
            · exact h
      have h0 := key false
      have h1 := key true
      omega

mutual
/-- Residual-aware depth bound for the block helper: `queryTerm vars D` has depth
at most `vars.length` (one per queried literal) plus the worst-case stripped size
`stripSize vars D` (the size of the residual DNF handed to the next block). -/
theorem dtDepth_queryTerm_le {n : Nat} :
    ∀ (vars : Term n) (D : DNF n),
      dtDepth (queryTerm vars D) ≤ vars.length + stripSize vars D
  | [], D => by
      rw [show queryTerm [] D = termCanonicalDT D from by rw [queryTerm]]
      simp only [List.length_nil, Nat.zero_add, stripSize_nil]
      exact dtDepth_termCanonicalDT_le D
  | l :: vs, D => by
      rw [show queryTerm (l :: vs) D
            = DTree.node l.var
                (queryTerm vs (assignVar l.var false D))
                (queryTerm vs (assignVar l.var true D)) from by rw [queryTerm]]
      rw [dtDepth_node, stripSize_cons]
      have h0 := dtDepth_queryTerm_le vs (assignVar l.var false D)
      have h1 := dtDepth_queryTerm_le vs (assignVar l.var true D)
      simp only [List.length_cons]
      omega
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

/-- **Worst-case depth bound — the tight, fully-proved companion deliverable.**
The term-canonical decision tree of a DNF has depth at most the DNF's total
literal-occurrence count `dnfSize D`.  Each path queries each relevant variable at
most once (term-block by term-block, each block residualizing away the variables
it queries), so the number of queries on any path is at most `dnfSize D`.  This is
the deterministic worst-case baseline the switching lemma later improves under a
random restriction. -/
theorem dtDepth_termCanonicalDT_le {n : Nat} :
    ∀ (D : DNF n), dtDepth (termCanonicalDT D) ≤ dnfSize D
  | [] => by simp [termCanonicalDT]
  | [] :: _ => by simp [termCanonicalDT]
  | (l :: t) :: D => by
      rw [show termCanonicalDT ((l :: t) :: D)
            = DTree.node l.var
                (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                (queryTerm t (assignVar l.var true ((l :: t) :: D))) from by
            rw [termCanonicalDT]]
      rw [dtDepth_node]
      have h0 := dtDepth_queryTerm_le t (assignVar l.var false ((l :: t) :: D))
      have h1 := dtDepth_queryTerm_le t (assignVar l.var true ((l :: t) :: D))
      -- The block residual stripped by t's variables drops to ≤ dnfSize D:
      -- after residualizing ((l::t)::D) by l.var and then by all of t's vars,
      -- the first term is fully decided, leaving ≤ dnfSize D.
      have hb : ∀ (b : Bool),
          stripSize t (assignVar l.var b ((l :: t) :: D)) ≤ dnfSize D := by
        intro b
        -- assignVar l.var b ((l::t)::D) = (assignTerm result of (l::t)) ::? rest
        rw [show assignVar l.var b ((l :: t) :: D)
              = (match assignTerm l.var b (l :: t) with
                  | some t' => t' :: assignVar l.var b D
                  | none => assignVar l.var b D) from by
              simp only [assignVar, List.filterMap_cons]
              cases assignTerm l.var b (l :: t) <;> rfl]
        cases hres : assignTerm l.var b (l :: t) with
        | none =>
            simp only [hres]
            exact Nat.le_trans (stripSize_le_dnfSize t (assignVar l.var b D))
              (dnfSize_assignVar_le l.var b D)
        | some t' =>
            simp only [hres]
            -- every literal of t' lies in (l::t) with var ≠ l.var, so its var
            -- is in t.map var ⊆ t.map var; the block strips it.
            have hblock :
                stripSize t (t' :: assignVar l.var b D)
                  ≤ stripSize t (assignVar l.var b D) := by
              apply stripSize_firstTermBlock_le t t' (assignVar l.var b D)
              intro m hm
              have hmlt : m ∈ (l :: t) :=
                assignTerm_mem_of_mem l.var b (l :: t) t' hres m hm
              have hmne : m.var ≠ l.var :=
                assignTerm_var_ne l.var b (l :: t) t' hres m hm
              rcases List.mem_cons.mp hmlt with h | h
              · exact absurd (by rw [h]) hmne
              · exact List.mem_map_of_mem (·.var) h
            exact Nat.le_trans hblock
              (Nat.le_trans (stripSize_le_dnfSize t (assignVar l.var b D))
                (dnfSize_assignVar_le l.var b D))
      have hb0 := hb false
      have hb1 := hb true
      simp only [dnfSize_cons, List.length_cons]
      omega
  termination_by D => (dnfSize D, 0)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
        | exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
end

/-! ## 4. Term-block structure

The defining feature of the term-canonical tree: along the first term block, the
queried variables are exactly the variables of the first term, in order.  We
expose this structurally.  `termCanonicalDT ((l :: t) :: D)` is a `node` on
`l.var` whose two children are `queryTerm t …`; and `queryTerm (m :: vs) …` is a
`node` on `m.var` whose children are `queryTerm vs …`.  Hence reading the queried
variables down any path from the root, the first `|l :: t| = 1 + t.length`
queries are `l.var` followed by the variables of `t` — i.e. the variables of the
first term `t₁ = l :: t`.

We record the two unfolding equations that make this structure explicit and
machine-checkable; they are the hooks the encoding brick consumes. -/

/-- **Term-block root unfolding.**  The term-canonical tree of a DNF whose first
term is `l :: t` is a decision node on the first term's head variable `l.var`,
each child being the block-helper on the remaining first-term literals `t` over
the residualized DNF.  The head of the term block is therefore exactly `l.var`. -/
theorem termCanonicalDT_cons_cons {n : Nat}
    (l : Literal n) (t : Term n) (D : DNF n) :
    termCanonicalDT ((l :: t) :: D)
      = DTree.node l.var
          (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          (queryTerm t (assignVar l.var true ((l :: t) :: D))) := by
  rw [termCanonicalDT]

/-- **Term-block step unfolding.**  Within a term block, querying continues on the
remaining literals: `queryTerm (m :: vs) D` is a decision node on `m.var` whose
children continue the block on `vs`.  Composing this with `termCanonicalDT_cons_cons`
shows the first `1 + t.length` variables queried along any root path are exactly
the variables of the first term `l :: t`, in order — the term-block property. -/
theorem queryTerm_cons {n : Nat}
    (m : Literal n) (vs : Term n) (D : DNF n) :
    queryTerm (m :: vs) D
      = DTree.node m.var
          (queryTerm vs (assignVar m.var false D))
          (queryTerm vs (assignVar m.var true D)) := by
  rw [queryTerm]

/-- **Block boundary unfolding.**  At the end of a term block (`vars = []`),
`queryTerm` returns control to `termCanonicalDT` on the residual DNF, i.e. the
next term block begins.  Together with the two unfoldings above this fully
characterizes the block structure: queries come in consecutive groups, one group
of exactly the variables of one term. -/
theorem queryTerm_nil {n : Nat} (D : DNF n) :
    queryTerm ([] : Term n) D = termCanonicalDT D := by
  rw [queryTerm]

/-! ### The term-block property, made explicit

We now prove a clean, fully-explicit statement of the term-block property: along
*every* root-to-leaf path of `termCanonicalDT ((l :: t) :: D)`, the first
`1 + t.length` variables queried are exactly `(l :: t).map (·.var)`, the variables
of the first term, in order.

We formalize "the sequence of variables queried along the path selected by
assignment `a`" as a function `pathVars`, and prove that its prefix of length
`1 + t.length` equals `(l :: t).map (·.var)`.  This is the precise object the
switching-lemma encoding consumes. -/

/-- The list of variables queried along the path that assignment `a` selects in a
decision tree (leaf → empty path). -/
def pathVars {n : Nat} (a : Assignment n) : DTree n → List (Fin n)
  | .leaf _ => []
  | .node v t0 t1 => v :: (if a v then pathVars a t1 else pathVars a t0)

@[simp] theorem pathVars_leaf {n : Nat} (a : Assignment n) (b : Bool) :
    pathVars a (DTree.leaf b) = [] := rfl

@[simp] theorem pathVars_node {n : Nat} (a : Assignment n)
    (v : Fin n) (t0 t1 : DTree n) :
    pathVars a (DTree.node v t0 t1)
      = v :: (if a v then pathVars a t1 else pathVars a t0) := rfl

/-- Along the path chosen by `a`, the block helper `queryTerm vars D` queries
exactly the variables of `vars` (in order), then continues with the path of the
residual `termCanonicalDT`.  This is the heart of the term-block property. -/
theorem pathVars_queryTerm {n : Nat} (a : Assignment n) :
    ∀ (vars : Term n) (D : DNF n),
      ∃ rest, pathVars a (queryTerm vars D)
                = vars.map (·.var) ++ rest
  | [], D => by
      rw [queryTerm_nil]
      exact ⟨pathVars a (termCanonicalDT D), by simp⟩
  | l :: vs, D => by
      rw [queryTerm_cons]
      cases hv : a l.var with
      | true =>
          obtain ⟨rest, hrest⟩ := pathVars_queryTerm a vs (assignVar l.var true D)
          refine ⟨rest, ?_⟩
          simp only [pathVars_node, hv, if_true, List.map_cons, List.cons_append]
          rw [hrest]
      | false =>
          obtain ⟨rest, hrest⟩ := pathVars_queryTerm a vs (assignVar l.var false D)
          refine ⟨rest, ?_⟩
          simp only [pathVars_node, hv, Bool.false_eq_true, if_false,
            List.map_cons, List.cons_append]
          rw [hrest]
  termination_by vars D => (dnfSize D, vars.length)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-- **The term-block property (explicit).**  Along the path chosen by ANY
assignment `a`, the variables queried by `termCanonicalDT ((l :: t) :: D)` begin
with exactly the variables of the first term `l :: t`, in order: the queried-path
list factors as `(l :: t).map (·.var) ++ rest`.  In particular the first
`1 + t.length` queries form one term block equal to the first term's variables —
the structural fact the switching-lemma encoding brick consumes. -/
theorem pathVars_termCanonicalDT_cons_cons {n : Nat} (a : Assignment n)
    (l : Literal n) (t : Term n) (D : DNF n) :
    ∃ rest, pathVars a (termCanonicalDT ((l :: t) :: D))
              = (l :: t).map (·.var) ++ rest := by
  rw [termCanonicalDT_cons_cons]
  cases hv : a l.var with
  | true =>
      obtain ⟨rest, hrest⟩ :=
        pathVars_queryTerm a t (assignVar l.var true ((l :: t) :: D))
      refine ⟨rest, ?_⟩
      simp only [pathVars_node, hv, if_true, List.map_cons, List.cons_append]
      rw [hrest]
  | false =>
      obtain ⟨rest, hrest⟩ :=
        pathVars_queryTerm a t (assignVar l.var false ((l :: t) :: D))
      refine ⟨rest, ?_⟩
      simp only [pathVars_node, hv, Bool.false_eq_true, if_false,
        List.map_cons, List.cons_append]
      rw [hrest]

end SwitchingTermCanonicalDT
end PvNP
