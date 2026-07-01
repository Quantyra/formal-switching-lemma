import PvNP.PHPSearchFloor

/-!
# Genuinely trace-dependent extraction: refutation → search tree → floor

This module closes the loop disclosed by S2065: an UNPADDED extraction whose
correctness actually requires the trace to be a refutation.

`extractQueryTreeUnpadded` builds a `3 x 2` falsified-clause query tree from a
bounded-depth refutation trace of `phpCNF 3 2` using ONLY the trace's `litEM`
query order — no variable-completion padding.  Its correctness
(`extractQueryTreeUnpadded_evalSelector`) is proved FROM the variable-coverage
floor (`PHPCNFCoverage.phpCNF32_refutationTrace_queries_all`): a refutation
must query every variable, and only therefore does the unpadded schedule cover
the selector's support.  `buildTree_nil_incorrect` witnesses that this is not
free: the same construction on an empty query order is wrong.

Composing with the parameterized search floor yields the miniature of the
classical paradigm, formal and unconditional:
refutation trace → correct search tree of depth = query-order length →
adversary floor → lower bound on the trace's query-order length.

## HONEST SCOPE STATEMENT (read this)

* All statements are about ONE fixed finite instance (`phpCNF 3 2`) and the
  LOCAL cut-free bounded-depth Tait system.  The floor-composition bound
  (≥ 4) is numerically weaker than the direct coverage bound (≥ 6); the
  composition is the deliverable (the route), not the number.  Nothing here
  is a Frege/PHP lower bound, an NP/circuit lower bound, or a statement
  about P vs NP; see the module headers of `BDVariableCoverage` and
  `PHPSearchFloor`.
* "Trace-dependent" means: the query schedule is trace-supplied and
  correctness is not free (`buildTree_nil_incorrect`), consuming
  refutation-hood via the coverage theorem.  The extracted tree and its depth
  vary with the specific trace; the correctness ARGUMENT consumes only
  refutation-hood (coverage holds uniformly for every refutation trace), not
  the identity of the trace.
* NON-VACUITY: the refutation-trace type quantified over here is nonempty —
  see `BDTaitCompleteness.phpCNF32_refutationTrace_nonempty` (completeness
  of the local system, S2068; that module imports this one, so the witness
  lives downstream).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace TraceSearchConnection

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor
open BDTraceToSearchExtraction
open BDVariableCoverage
open PHPCNFCoverage
open PHPSearchFloor

/-! ## Restricting a trace query order to the six CNF variables -/

/-- Restrict an ambient `Fin 7` query order to the six PHP/CNF variables. -/
def orderToFin6 (order : List (Fin (Nat.succ (3 * 2)))) : List (Fin 6) :=
  order.filterMap (fun v => if h : v.val < 6 then some ⟨v.val, h⟩ else none)

theorem mem_orderToFin6 {order : List (Fin (Nat.succ (3 * 2)))}
    {v : Fin (Nat.succ (3 * 2))} (hv : v ∈ order) (hlt : v.val < 6) :
    (⟨v.val, hlt⟩ : Fin 6) ∈ orderToFin6 order := by
  rw [orderToFin6, List.mem_filterMap]
  exact ⟨v, hv, by rw [dif_pos hlt]⟩

/-- If the embedded image of every CNF variable occurs in an ambient order,
the restricted order covers all six CNF variables. -/
theorem orderToFin6_covers (order : List (Fin (Nat.succ (3 * 2))))
    (hcov : ∀ i : Fin 6, phpVarEmbedding i ∈ order) :
    ∀ i : Fin 6, i ∈ orderToFin6 order := by
  intro i
  have hmem := mem_orderToFin6 (hcov i)
    (show (phpVarEmbedding i).val < 6 from i.isLt)
  have he : (⟨(phpVarEmbedding i).val, i.isLt⟩ : Fin 6) = i := by
    rcases i with ⟨v, hv⟩
    rfl
  rwa [he] at hmem

/-- Refutation traces of `phpCNF 3 2` cover the embedded image of every CNF
variable (repackaging of the S3-stage coverage theorem). -/
theorem phpCNF32_embedding_covered
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    ∀ i : Fin 6, phpVarEmbedding i ∈ traceQueryOrder π.proof := by
  obtain ⟨h00, h01, h10, h11, h20, h21⟩ :=
    phpCNF32_refutationTrace_queries_all π
  have hlist : ∀ i : Fin 6, phpVarEmbedding i ∈ phpVarsList32 := by decide
  intro i
  have hi := hlist i
  simp only [phpVarsList32, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h <;> rw [h] <;> assumption

/-! ## The unpadded extraction -/

/-- **Unpadded trace-dependent extraction.**  The query schedule is EXACTLY
the trace's `litEM` order (restricted to the six CNF variables); no
completion padding is added.  Correctness therefore depends on the trace
being a refutation. -/
def extractQueryTreeUnpadded
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause :=
  buildTree (orderToFin6 (traceQueryOrder π.proof)) (fun _ => false)

/-- **Trace-dependent correctness.**  The unpadded extracted tree computes the
fixed finite semantic selector — proved FROM the coverage floor: only because
the trace is a refutation does its query order cover every variable. -/
theorem extractQueryTreeUnpadded_evalSelector
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)])
    (a : Assignment (Nat.succ (3 * 2))) :
    queryEval a (extractQueryTreeUnpadded π) =
      threeTwoPHPFalsifiedClauseSelector a := by
  apply buildTree_evalSelector
  intro i
  exact Or.inl (orderToFin6_covers _ (phpCNF32_embedding_covered π) i)

/-- The unpadded extracted tree always outputs a falsified clause. -/
theorem extractQueryTreeUnpadded_searchCorrect
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a
        (queryEval a (extractQueryTreeUnpadded π)) :=
  threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector
    (extractQueryTreeUnpadded π) (extractQueryTreeUnpadded_evalSelector π)

/-- **Non-freeness witness.**  The same construction on an EMPTY query order
is incorrect: unpadded correctness genuinely consumes the trace's coverage. -/
theorem buildTree_nil_incorrect :
    ∃ a : Assignment (Nat.succ (3 * 2)),
      queryEval a (buildTree [] (fun _ => false)) ≠
        threeTwoPHPFalsifiedClauseSelector a :=
  ⟨fun _ => true, by decide⟩

/-! ## Depth accounting and the floor composition -/

/-- The constructed tree's depth is exactly its query-order length. -/
theorem buildTree_queryDepth :
    ∀ (order : List (Fin 6)) (acc : Fin 6 → Bool),
      queryDepth (buildTree order acc) = order.length
  | [], _ => rfl
  | v :: rest, acc => by
      simp [buildTree, queryDepth, buildTree_queryDepth rest,
        Nat.max_self]

/-- The unpadded extracted tree's depth is the restricted query-order
length. -/
theorem extractQueryTreeUnpadded_depth
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    queryDepth (extractQueryTreeUnpadded π) =
      (orderToFin6 (traceQueryOrder π.proof)).length :=
  buildTree_queryDepth _ _

/-- **The miniature paradigm, composed.**  Refutation trace → unpadded correct
search tree of depth = restricted query-order length → `3 x 2` search floor of
four → the trace's query order has length at least four.  (The direct coverage
bound already gives ≥ 6; this theorem's value is the ROUTE — the first
refutation→search→adversary composition formalized in THIS development; no
claim about the wider literature is made — not the number.) -/
theorem phpCNF32_traceQueryOrder_length_ge_four_via_search
    (π : BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :
    4 ≤ (traceQueryOrder π.proof).length := by
  have hfloor := threeTwoPHPFalsifiedClauseSearchDepthFloor_four
    (extractQueryTreeUnpadded π)
    (extractQueryTreeUnpadded_searchCorrect π)
  rw [extractQueryTreeUnpadded_depth] at hfloor
  calc 4 ≤ (orderToFin6 (traceQueryOrder π.proof)).length := hfloor
    _ ≤ (traceQueryOrder π.proof).length := List.length_filterMap_le _ _

end TraceSearchConnection
end PvNP
