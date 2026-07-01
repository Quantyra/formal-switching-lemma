import PvNP.BDVariableCoverage

/-!
# PHP CNF and its variable-coverage floor

The pigeonhole CNF `phpCNF p h` (pigeon clauses + collision clauses, matching
the clause set of `restrictedPHPFormula`) and the instantiated coverage floor:
for the fixed `3 x 2` view, removing ANY single PHP variable leaves a
satisfiable sub-CNF, so by `BDVariableCoverage.refutationTrace_queries_var`
every bounded-depth refutation trace of `phpCNF 3 2` must perform `litEM` on
every one of the six PHP variables — hence has query-order length and trace
size at least six.

## HONEST SCOPE STATEMENT (read this)

* These are variable-coverage floors for refutation traces of the LOCAL
  cut-free bounded-depth Tait system, LINEAR in the number of variables.
  They are NOT Frege/PHP lower bounds, NOT proof-size lower bounds for any
  standard proof system with cut, NOT NP/circuit lower bounds, and NOT
  statements about P vs NP.
* NON-VACUITY: the refutation-trace type these floors quantify over is
  nonempty — see `BDTaitCompleteness.phpCNF32_refutationTrace_nonempty`
  (completeness of the local system, S2068; that module imports this one, so
  the witness lives downstream).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPCNFCoverage

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor
open BDTraceToSearchExtraction
open BDVariableCoverage

/-! ## The PHP CNF -/

/-- Pigeon clause: pigeon `i` sits in some hole. -/
def phpPigeonClause (p h : Nat) (i : Fin p) : Clause (Nat.succ (p * h)) :=
  (finList h).map (fun j => mapsLit p h i j)

/-- Collision clause: pigeons `i` and `k` do not share hole `j`. -/
def phpCollisionClause (p h : Nat) (i k : Fin p) (j : Fin h) :
    Clause (Nat.succ (p * h)) :=
  [notMapsLit p h i j, notMapsLit p h k j]

/-- The pigeonhole CNF: every pigeon somewhere, no two pigeons in one hole.
Collision clauses are emitted only for `i.val < k.val`, matching
`restrictedPHPFormula`. -/
def phpCNF (p h : Nat) : CNF (Nat.succ (p * h)) :=
  (finList p).map (phpPigeonClause p h) ++
    (finList p).bind (fun i =>
      (finList p).bind (fun k =>
        if i.val < k.val then (finList h).map (phpCollisionClause p h i k)
        else []))

/-! ## Concrete `3 x 2` coverage -/

/-- Witness assignment: pigeons 1 and 2 in holes 0 and 1 (used when a variable
of pigeon 0 is removed). -/
private def assign_x10_x21 : Assignment (Nat.succ (3 * 2)) :=
  fun w => decide (w.val = 2) || decide (w.val = 5)

/-- Witness assignment: pigeons 0 and 2 in holes 0 and 1 (used when a variable
of pigeon 1 is removed). -/
private def assign_x00_x21 : Assignment (Nat.succ (3 * 2)) :=
  fun w => decide (w.val = 0) || decide (w.val = 5)

/-- Witness assignment: pigeons 0 and 1 in holes 0 and 1 (used when a variable
of pigeon 2 is removed). -/
private def assign_x00_x11 : Assignment (Nat.succ (3 * 2)) :=
  fun w => decide (w.val = 0) || decide (w.val = 3)

/-- Boolean reformulation adapter: every clause either mentions the removed
variable or is satisfied by the witness assignment (single `Bool` equation, so
`decide` always applies). -/
private theorem hsat_of_boolForm {n : Nat} {C : CNF n} {v : Fin n}
    {a : Assignment n}
    (hd : C.all (fun c =>
      c.any (fun l => decide (l.var = v)) ||
        c.any (fun l => litEval a l)) = true) :
    ∀ c ∈ C, (∀ l ∈ c, l.var ≠ v) → ∃ l ∈ c, litEval a l = true := by
  intro c hc hno
  have h := List.all_eq_true.mp hd c hc
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · rcases List.any_eq_true.mp h1 with ⟨l, hl, he⟩
    exact absurd (of_decide_eq_true he) (hno l hl)
  · rcases List.any_eq_true.mp h2 with ⟨l, hl, he⟩
    exact ⟨l, hl, he⟩

/-- **Concrete `3 x 2` full coverage.**  Every bounded-depth refutation trace
of `phpCNF 3 2` performs `litEM` on every one of the six PHP variables. -/
theorem phpCNF32_refutationTrace_queries_all
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    threeTwoPHPVar00 ∈ traceQueryOrder π.proof ∧
      threeTwoPHPVar01 ∈ traceQueryOrder π.proof ∧
      threeTwoPHPVar10 ∈ traceQueryOrder π.proof ∧
      threeTwoPHPVar11 ∈ traceQueryOrder π.proof ∧
      threeTwoPHPVar20 ∈ traceQueryOrder π.proof ∧
      threeTwoPHPVar21 ∈ traceQueryOrder π.proof := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact refutationTrace_queries_var _ π _
      ⟨assign_x10_x21, hsat_of_boolForm (by decide)⟩
  · exact refutationTrace_queries_var _ π _
      ⟨assign_x10_x21, hsat_of_boolForm (by decide)⟩
  · exact refutationTrace_queries_var _ π _
      ⟨assign_x00_x21, hsat_of_boolForm (by decide)⟩
  · exact refutationTrace_queries_var _ π _
      ⟨assign_x00_x21, hsat_of_boolForm (by decide)⟩
  · exact refutationTrace_queries_var _ π _
      ⟨assign_x00_x11, hsat_of_boolForm (by decide)⟩
  · exact refutationTrace_queries_var _ π _
      ⟨assign_x00_x11, hsat_of_boolForm (by decide)⟩

/-- The six PHP variables of the `3 x 2` view, as a duplicate-free list. -/
def phpVarsList32 : List (Fin (Nat.succ (3 * 2))) :=
  [threeTwoPHPVar00, threeTwoPHPVar01, threeTwoPHPVar10,
    threeTwoPHPVar11, threeTwoPHPVar20, threeTwoPHPVar21]

theorem phpVarsList32_nodup : phpVarsList32.Nodup := by decide

/-- **Query-order length floor.**  Every bounded-depth refutation trace of
`phpCNF 3 2` has `litEM` query-order length at least six. -/
theorem phpCNF32_traceQueryOrder_length_ge_six
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    6 ≤ (traceQueryOrder π.proof).length := by
  obtain ⟨h00, h01, h10, h11, h20, h21⟩ :=
    phpCNF32_refutationTrace_queries_all π
  have hsub : phpVarsList32 ⊆ traceQueryOrder π.proof := by
    intro v hv
    simp only [phpVarsList32, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h | h <;> subst h <;> assumption
  have hsubperm := List.Nodup.subperm phpVarsList32_nodup hsub
  simpa [phpVarsList32] using hsubperm.length_le

/-- **Trace-size floor.**  Every bounded-depth refutation trace of `phpCNF 3 2`
has size at least six: the refutation must genuinely touch every variable. -/
theorem phpCNF32_traceSize_ge_six
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    6 ≤ π.size := by
  calc 6 ≤ (traceQueryOrder π.proof).length :=
        phpCNF32_traceQueryOrder_length_ge_six π
    _ ≤ π.proof.size := traceQueryOrder_length_le_size π.proof
    _ = π.size := rfl

end PHPCNFCoverage
end PvNP
