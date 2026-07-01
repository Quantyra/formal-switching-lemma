import PvNP.BDTraceToSearchExtraction

/-!
# Variable-coverage floor for bounded-depth refutation traces

This module proves a structural lower bound on the local bounded-depth Tait
refutation traces: `litEM` is the ONLY inference rule whose soundness uses both
polarities of a variable, so a refutation whose `litEM` variables all lie in a
set `S` remains sound under a NON-STANDARD semantics where every literal on a
variable outside `S` evaluates to `false`.  Consequently the sub-CNF of clauses
supported inside `S` must already be unsatisfiable; contrapositively, if every
clause of a falsifying certificate needs a variable `v` (the sub-CNF avoiding
`v` is satisfiable), then EVERY refutation trace must perform `litEM` on `v`.

## HONEST SCOPE STATEMENT (read this)

* This is a variable-coverage floor for refutation traces of THE LOCAL
  bounded-depth Tait system (`BDProof`/`BDProofTrace`: truAx, litEM, weaken,
  orIntro, andIntro), which is cut-free and weak.  The resulting bounds are
  LINEAR in the number of variables.  This is NOT the classical exponential
  AC0-Frege/PHP lower bound, NOT a statement about Frege systems with cut,
  NOT an NP or circuit lower bound, and NOT a statement about P vs NP.
* The non-standard semantics is a proof device only; no claim is made about
  any other proof system.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace BDVariableCoverage

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open BDTraceToSearchExtraction

/-! ## Non-standard semantics -/

/-- Non-standard evaluation relative to a variable set `S`: literals on
variables outside `S` evaluate to `false` regardless of polarity; constants and
gates evaluate as usual. -/
def evalNS {n : Nat} (S : Fin n → Bool) (a : Assignment n) : BDFormula n → Bool
  | .tru => true
  | .fls => false
  | .lit l => S l.var && litEval a l
  | .and l => l.attach.all (fun f => evalNS S a f.1)
  | .or  l => l.attach.any (fun f => evalNS S a f.1)
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

theorem evalNS_tru {n : Nat} (S : Fin n → Bool) (a : Assignment n) :
    evalNS S a BDFormula.tru = true := by simp only [evalNS]

theorem evalNS_lit {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (l : Literal n) :
    evalNS S a (BDFormula.lit l) = (S l.var && litEval a l) := by
  simp only [evalNS]

/-- `and` gates evaluate as `List.all` under the non-standard semantics. -/
theorem evalNS_and {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (l : List (BDFormula n)) :
    evalNS S a (BDFormula.and l) = l.all (fun f => evalNS S a f) := by
  rw [show evalNS S a (BDFormula.and l)
        = l.attach.all (fun f => evalNS S a f.1) by simp only [evalNS]]
  exact attach_all_eq l (fun f => evalNS S a f)

/-- `or` gates evaluate as `List.any` under the non-standard semantics. -/
theorem evalNS_or {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (l : List (BDFormula n)) :
    evalNS S a (BDFormula.or l) = l.any (fun f => evalNS S a f) := by
  rw [show evalNS S a (BDFormula.or l)
        = l.attach.any (fun f => evalNS S a f.1) by simp only [evalNS]]
  exact attach_any_eq l (fun f => evalNS S a f)

/-- Non-standard truth of a disjunctive sequent. -/
def sequentTrueNS {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (Γ : List (BDFormula n)) : Bool :=
  Γ.any (fun f => evalNS S a f)

theorem sequentTrueNS_of_mem {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    {f : BDFormula n} {Γ : List (BDFormula n)}
    (hmem : f ∈ Γ) (hf : evalNS S a f = true) :
    sequentTrueNS S a Γ = true := by
  simp only [sequentTrueNS, List.any_eq_true]
  exact ⟨f, hmem, hf⟩

theorem sequentTrueNS_cons {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (f : BDFormula n) (Γ : List (BDFormula n)) :
    sequentTrueNS S a (f :: Γ) = (evalNS S a f || sequentTrueNS S a Γ) := by
  simp [sequentTrueNS]

theorem sequentTrueNS_append {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (Γ Δ : List (BDFormula n)) :
    sequentTrueNS S a (Γ ++ Δ) =
      (sequentTrueNS S a Γ || sequentTrueNS S a Δ) := by
  simp [sequentTrueNS, List.any_append]

/-! ## Trace query-order membership plumbing -/

/-- Membership transfers into a fold of list appends. -/
theorem mem_foldr_append {α : Type _} {x : α} :
    ∀ {ls : List (List α)} {l : List α}, l ∈ ls → x ∈ l →
      x ∈ ls.foldr (fun a acc => a ++ acc) []
  | _ :: ls, l, hmem, hx => by
      rcases List.mem_cons.mp hmem with h | h
      · subst h
        exact List.mem_append.mpr (Or.inl hx)
      · exact List.mem_append.mpr (Or.inr (mem_foldr_append h hx))

/-- Every `litEM` variable of an `andIntro` premise occurs in the query order
of the composed trace. -/
theorem mem_traceQueryOrder_andIntro {n : Nat} {Γ : List (BDFormula n)}
    {l : List (BDFormula n)}
    (h : ∀ f, f ∈ l → BDProofTrace (f :: Γ))
    {f : BDFormula n} (hf : f ∈ l) {v : Fin n}
    (hv : v ∈ traceQueryOrder (h f hf)) :
    v ∈ traceQueryOrder (BDProofTrace.andIntro h) := by
  show v ∈ (l.attach.map (fun g => traceQueryOrder (h g.1 g.2))).foldr
    (fun x acc => x ++ acc) []
  exact mem_foldr_append
    (List.mem_map_of_mem (fun g => traceQueryOrder (h g.1 g.2))
      (List.mem_attach l ⟨f, hf⟩)) hv

/-! ## Non-standard soundness -/

/-- **Non-standard soundness.**  A bounded-depth proof trace whose `litEM`
variables all lie in `S` derives a sequent that is true under the non-standard
semantics relative to `S`, for every assignment.  Every rule except `litEM` is
sound for ANY compositional semantics of this shape; `litEM` needs exactly the
membership of its variable in `S`. -/
theorem bdProofTrace_sound_nonstandard {n : Nat} (S : Fin n → Bool)
    {Γ : List (BDFormula n)} (π : BDProofTrace Γ)
    (hcov : ∀ v ∈ traceQueryOrder π, S v = true) (a : Assignment n) :
    sequentTrueNS S a Γ = true := by
  induction π with
  | truAx Γ hmem =>
      exact sequentTrueNS_of_mem S a hmem (evalNS_tru S a)
  | litEM Γ v hpos hneg =>
      have hSv : S v = true := hcov v (by simp [traceQueryOrder])
      cases hv : a v with
      | true =>
          refine sequentTrueNS_of_mem S a hpos ?_
          rw [evalNS_lit, hSv]
          simp [litEval, hv]
      | false =>
          refine sequentTrueNS_of_mem S a hneg ?_
          rw [evalNS_lit, hSv]
          simp [litEval, hv]
  | weaken h hsub ih =>
      have hcov' : ∀ v ∈ traceQueryOrder h, S v = true := by
        intro v hv
        exact hcov v (by simpa [traceQueryOrder] using hv)
      have hΓ := ih hcov'
      simp only [sequentTrueNS, List.any_eq_true] at hΓ ⊢
      rcases hΓ with ⟨f, hfmem, hfeval⟩
      exact ⟨f, hsub f hfmem, hfeval⟩
  | @orIntro Γ l h ih =>
      have hcov' : ∀ v ∈ traceQueryOrder h, S v = true := by
        intro v hv
        exact hcov v (by simpa [traceQueryOrder] using hv)
      have hlΓ := ih hcov'
      rw [sequentTrueNS_append] at hlΓ
      rw [sequentTrueNS_cons, evalNS_or]
      have hrw : sequentTrueNS S a l = l.any (fun f => evalNS S a f) := rfl
      rw [← hrw]
      exact hlΓ
  | @andIntro Γ l h ih =>
      rw [sequentTrueNS_cons, evalNS_and]
      by_cases hΓ : sequentTrueNS S a Γ = true
      · rw [hΓ, Bool.or_true]
      · have hall : l.all (fun f => evalNS S a f) = true := by
          rw [List.all_eq_true]
          intro f hfmem
          have hcov' : ∀ v ∈ traceQueryOrder (h f hfmem), S v = true := by
            intro v hv
            exact hcov v (mem_traceQueryOrder_andIntro h hfmem hv)
          have hfval := ih f hfmem hcov'
          rw [sequentTrueNS_cons] at hfval
          rcases Bool.or_eq_true _ _ |>.mp hfval with hf | hg
          · exact hf
          · exact absurd hg hΓ
        rw [hall, Bool.true_or]

/-! ## The coverage theorem -/

/-- Non-standard evaluation of a negated CNF literal. -/
theorem evalNS_neg_lit {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (l : Literal n) :
    evalNS S a (neg (cnfLiteralToBD l)) = (S l.var && !(litEval a l)) := by
  rw [show neg (cnfLiteralToBD l) = BDFormula.lit ⟨l.var, !l.sign⟩ from by
    simp [cnfLiteralToBD, neg]]
  rw [evalNS_lit]
  cases hs : l.sign <;> simp [litEval, hs]

/-- Non-standard evaluation of a negated CNF clause: every literal has its
variable in `S` and evaluates false. -/
theorem evalNS_neg_clause {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (c : Clause n) :
    evalNS S a (neg (cnfClauseToBD c)) =
      c.all (fun l => S l.var && !(litEval a l)) := by
  rw [show neg (cnfClauseToBD c)
        = BDFormula.and ((c.map cnfLiteralToBD).attach.map (fun f => neg f.1))
      from by rw [cnfClauseToBD, neg]]
  rw [evalNS_and]
  rw [List.attach_map_val (c.map cnfLiteralToBD) (fun f => neg f)]
  rw [List.map_map]
  induction c with
  | nil => rfl
  | cons l c ih =>
      simp only [List.map_cons, List.all_cons, ih]
      congr 1
      simpa using evalNS_neg_lit S a l

/-- Non-standard evaluation of a negated CNF: some clause is entirely
supported inside `S` and falsified by the assignment. -/
theorem evalNS_neg_cnf {n : Nat} (S : Fin n → Bool) (a : Assignment n)
    (C : CNF n) :
    evalNS S a (neg (cnfToBD C)) =
      C.any (fun c => c.all (fun l => S l.var && !(litEval a l))) := by
  rw [show neg (cnfToBD C)
        = BDFormula.or ((C.map cnfClauseToBD).attach.map (fun f => neg f.1))
      from by rw [cnfToBD, neg]]
  rw [evalNS_or]
  rw [List.attach_map_val (C.map cnfClauseToBD) (fun f => neg f)]
  rw [List.map_map]
  induction C with
  | nil => rfl
  | cons c C ih =>
      simp only [List.map_cons, List.any_cons, ih]
      congr 1
      simpa using evalNS_neg_clause S a c

/-- **Coverage theorem.**  If a bounded-depth refutation trace of the CNF `C`
performs `litEM` only on variables in `S`, then for EVERY assignment some
clause of `C` supported entirely inside `S` is falsified — i.e. the sub-CNF of
`S`-supported clauses is already unsatisfiable. -/
theorem refutationTrace_falsifiedClause_in_cover {n : Nat} (C : CNF n)
    (π : BDRefutationTrace [cnfToBD C]) (S : Fin n → Bool)
    (hcov : ∀ v ∈ traceQueryOrder π.proof, S v = true)
    (a : Assignment n) :
    ∃ c ∈ C, (∀ l ∈ c, S l.var = true) ∧ (∀ l ∈ c, litEval a l = false) := by
  have hNS := bdProofTrace_sound_nonstandard S π.proof hcov a
  have hone : evalNS S a (neg (cnfToBD C)) = true := by
    simpa [sequentTrueNS] using hNS
  rw [evalNS_neg_cnf] at hone
  rcases List.any_eq_true.mp hone with ⟨c, hcmem, hcall⟩
  rw [List.all_eq_true] at hcall
  refine ⟨c, hcmem, ?_, ?_⟩
  · intro l hl
    exact (Bool.and_eq_true _ _ |>.mp (hcall l hl)).1
  · intro l hl
    have := (Bool.and_eq_true _ _ |>.mp (hcall l hl)).2
    simpa using this

/-- **Per-variable coverage corollary.**  If the clauses of `C` avoiding a
variable `v` are simultaneously satisfiable, then every bounded-depth
refutation trace of `C` must perform `litEM` on `v`. -/
theorem refutationTrace_queries_var {n : Nat} (C : CNF n)
    (π : BDRefutationTrace [cnfToBD C]) (v : Fin n)
    (hsat : ∃ a : Assignment n, ∀ c ∈ C,
      (∀ l ∈ c, l.var ≠ v) → ∃ l ∈ c, litEval a l = true) :
    v ∈ traceQueryOrder π.proof := by
  by_contra hnot
  obtain ⟨a, ha⟩ := hsat
  have hcov : ∀ w ∈ traceQueryOrder π.proof,
      (fun w => decide (w ≠ v)) w = true := by
    intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hnot (h ▸ hw)
    simpa using hwv
  obtain ⟨c, hcmem, hvars, hfals⟩ :=
    refutationTrace_falsifiedClause_in_cover C π
      (fun w => decide (w ≠ v)) hcov a
  have hcv : ∀ l ∈ c, l.var ≠ v := by
    intro l hl
    have := hvars l hl
    simpa using this
  rcases ha c hcmem hcv with ⟨l, hl, htrue⟩
  rw [hfals l hl] at htrue
  exact Bool.noConfusion htrue

/-! ## Trace-size consequence plumbing -/

/-- Fold-of-appends length is the sum of the lengths. -/
theorem length_foldr_append {α : Type _} :
    ∀ ls : List (List α),
      (ls.foldr (fun x acc => x ++ acc) []).length =
        (ls.map List.length).foldr Nat.add 0
  | [] => rfl
  | l :: ls => by
      simp [List.length_append, length_foldr_append ls, Nat.add_comm]

/-- Pointwise-dominated map folds are dominated. -/
theorem foldr_add_le_of_pointwise {β : Type _} :
    ∀ (l : List β) (f g : β → Nat), (∀ x ∈ l, f x ≤ g x) →
      (l.map f).foldr Nat.add 0 ≤ (l.map g).foldr Nat.add 0
  | [], _, _, _ => Nat.le_refl _
  | x :: l, f, g, h => by
      simp only [List.map_cons, List.foldr_cons]
      exact Nat.add_le_add (h x (List.mem_cons_self x l))
        (foldr_add_le_of_pointwise l f g
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- The `litEM` query order is no longer than the trace size: every recorded
query comes from a distinct `litEM` node. -/
theorem traceQueryOrder_length_le_size {n : Nat} {Γ : List (BDFormula n)}
    (π : BDProofTrace Γ) :
    (traceQueryOrder π).length ≤ π.size := by
  induction π with
  | truAx Γ h => simp [traceQueryOrder, BDProofTrace.size]
  | litEM Γ v hpos hneg => simp [traceQueryOrder, BDProofTrace.size]
  | weaken h hsub ih =>
      calc (traceQueryOrder (BDProofTrace.weaken h hsub)).length
          = (traceQueryOrder h).length := by simp [traceQueryOrder]
        _ ≤ h.size := ih
        _ ≤ 1 + h.size := Nat.le_add_left _ _
  | @orIntro Γ l h ih =>
      calc (traceQueryOrder (BDProofTrace.orIntro h)).length
          = (traceQueryOrder h).length := by simp [traceQueryOrder]
        _ ≤ h.size := ih
        _ ≤ 1 + h.size := Nat.le_add_left _ _
  | @andIntro Γ l h ih =>
      have hlen : (traceQueryOrder (BDProofTrace.andIntro h)).length =
          (l.attach.map
            (fun f => (traceQueryOrder (h f.1 f.2)).length)).foldr Nat.add 0 := by
        show ((l.attach.map (fun g => traceQueryOrder (h g.1 g.2))).foldr
          (fun x acc => x ++ acc) []).length = _
        rw [length_foldr_append, List.map_map]
        rfl
      have hle : (l.attach.map
            (fun f => (traceQueryOrder (h f.1 f.2)).length)).foldr Nat.add 0 ≤
          (l.attach.map (fun f => (h f.1 f.2).size)).foldr Nat.add 0 :=
        foldr_add_le_of_pointwise l.attach _ _ (fun x _ => ih x.1 x.2)
      calc (traceQueryOrder (BDProofTrace.andIntro h)).length
          = _ := hlen
        _ ≤ (l.attach.map (fun f => (h f.1 f.2).size)).foldr Nat.add 0 := hle
        _ ≤ 1 + (l.attach.map (fun f => (h f.1 f.2).size)).foldr Nat.add 0 :=
            Nat.le_add_left _ _

end BDVariableCoverage
end PvNP
