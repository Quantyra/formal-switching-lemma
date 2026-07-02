import PvNP.PHPSearchFloorTightness

/-!
# The family trace-to-search route: refutation → search tree → `2h` floor

The FAMILY version of the composed route: for every `h > 0` and every
bounded-depth refutation trace of `phpCNF (h+1) h`, an extracted correct
falsified-clause search tree whose depth is EXACTLY the trace's `litEM`
query-order length; composed with the parameterized `2h` search floor this
yields `2*h ≤` query-order length `≤` trace size — a growing-family trace
bound obtained THROUGH the search connection.

Ingredients: a total valid selector for the `(h+1) x h` search problem
(every assignment falsifies some clause, by the finite pigeonhole principle),
precomposed with a support restriction so that leaf outputs depend only on the
PHP variables; the family coverage theorem then makes the UNPADDED extraction
correct.

## HONEST SCOPE STATEMENT (read this)

* The route bound (`2h`) is numerically weaker than the direct family
  coverage bound (`(h+1)*h`, `PHPFamilyCoverage.phpCNF_family_traceSize`)
  for every `h > 1` and equal at `h = 1`; the deliverable is the ROUTE — a
  family-level trace bound through the refutation→search→adversary
  composition — not the number.
* All bounds concern refutation traces of the LOCAL cut-free bounded-depth
  Tait system and are LINEAR in the number of PHP variables (no formal formula-size measure is stated).  NOT a Frege/PHP proof-size
  lower bound for any system with cut, NOT an NP/circuit lower bound, NOT a
  statement about P vs NP.
* The extracted trees and the selector are `noncomputable` (classical choice
  picks falsified clauses); everything is kernel-checked as usual.
* NON-VACUITY: the refutation-trace types quantified over are nonempty for
  every `h` (`BDTaitCompleteness.phpCNF_family_refutationTrace_nonempty`).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFamilyTraceSearchRoute

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor
open BDTraceToSearchExtraction
open BDVariableCoverage
open PHPCNFCoverage
open PHPSearchFloor
open PHPFamilyCoverage

/-! ## A total valid selector for `PHP(h+1, h)` -/

/-- Every assignment falsifies some clause of the `(h+1) x h` PHP view:
either some pigeon's clause is entirely false, or every pigeon picks a hole
and two must collide (finite pigeonhole). -/
theorem phpFalsifiedClause_exists (h : Nat)
    (a : Assignment (Nat.succ ((h + 1) * h))) :
    ∃ out : PHPFalsifiedClause (h + 1) h, PHPFalsifiedClause.Valid a out := by
  by_cases hpig : ∃ i : Fin (h + 1), ∀ j : Fin h,
      a (phpVar (h + 1) h i j) = false
  · obtain ⟨i, hi⟩ := hpig
    exact ⟨.pigeon i, hi⟩
  · have hf : ∀ i : Fin (h + 1), ∃ j : Fin h,
        a (phpVar (h + 1) h i j) = true := by
      intro i
      by_contra hno
      refine hpig ⟨i, fun j => ?_⟩
      cases hb : a (phpVar (h + 1) h i j) with
      | false => rfl
      | true => exact absurd ⟨j, hb⟩ hno
    choose f hf' using hf
    obtain ⟨i, k, hik, he⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    exact ⟨.collision i k (f i), hik, hf' i, by rw [he]; exact hf' k⟩

/-- Restrict an assignment to the PHP variables (ambient variable reads
`false`), so that selector outputs depend only on the PHP support. -/
def restrictPHP (h : Nat) (a : Assignment (Nat.succ ((h + 1) * h))) :
    Assignment (Nat.succ ((h + 1) * h)) :=
  fun w => if w.val < (h + 1) * h then a w else false

theorem restrictPHP_agree {h : Nat}
    {acc a : Assignment (Nat.succ ((h + 1) * h))}
    (hagree : ∀ w : Fin (Nat.succ ((h + 1) * h)),
      w.val < (h + 1) * h → acc w = a w) :
    restrictPHP h acc = restrictPHP h a := by
  funext w
  by_cases hw : w.val < (h + 1) * h
  · simp [restrictPHP, hw, hagree w hw]
  · simp [restrictPHP, hw]

/-- Validity only reads PHP variables, so it transfers across the
restriction. -/
theorem valid_restrictPHP {h : Nat}
    (a : Assignment (Nat.succ ((h + 1) * h)))
    (out : PHPFalsifiedClause (h + 1) h)
    (hv : PHPFalsifiedClause.Valid (restrictPHP h a) out) :
    PHPFalsifiedClause.Valid a out := by
  have hread : ∀ (i : Fin (h + 1)) (j : Fin h),
      restrictPHP h a (phpVar (h + 1) h i j) = a (phpVar (h + 1) h i j) := by
    intro i j
    simp [restrictPHP, phpVar_lt i j]
  cases out with
  | pigeon i =>
      intro j
      rw [← hread i j]
      exact hv j
  | collision i k j =>
      obtain ⟨hik, h1, h2⟩ := hv
      exact ⟨hik, by rw [← hread i j]; exact h1, by rw [← hread k j]; exact h2⟩

/-- The total selector: a falsified clause of the restricted assignment,
chosen classically.  Depends only on the PHP variables by construction. -/
noncomputable def phpSelector (h : Nat)
    (a : Assignment (Nat.succ ((h + 1) * h))) : PHPFalsifiedClause (h + 1) h :=
  Classical.choose (phpFalsifiedClause_exists h (restrictPHP h a))

/-- The selector always names a falsified clause. -/
theorem phpSelector_valid (h : Nat)
    (a : Assignment (Nat.succ ((h + 1) * h))) :
    PHPFalsifiedClause.Valid a (phpSelector h a) :=
  valid_restrictPHP a _
    (Classical.choose_spec (phpFalsifiedClause_exists h (restrictPHP h a)))

/-- Selector congruence: agreement on the PHP variables determines the
output. -/
theorem phpSelector_congr {h : Nat}
    {acc a : Assignment (Nat.succ ((h + 1) * h))}
    (hagree : ∀ w : Fin (Nat.succ ((h + 1) * h)),
      w.val < (h + 1) * h → acc w = a w) :
    phpSelector h acc = phpSelector h a :=
  congrArg (fun b => Classical.choose (phpFalsifiedClause_exists h b))
    (restrictPHP_agree hagree)

/-! ## The family extraction -/

/-- Overwrite one recorded answer. -/
def updAcc {n : Nat} (acc : Assignment n) (v : Fin n) (b : Bool) :
    Assignment n :=
  fun w => if w = v then b else acc w

/-- Build a search tree that queries the given ambient variables in order and
outputs the selector of the recorded answers at the leaves. -/
noncomputable def phpBuildTree (h : Nat) :
    List (Fin (Nat.succ ((h + 1) * h))) →
    Assignment (Nat.succ ((h + 1) * h)) →
    QueryTree (Nat.succ ((h + 1) * h)) (PHPFalsifiedClause (h + 1) h)
  | [], acc => .leaf (phpSelector h acc)
  | v :: rest, acc =>
      .node v (phpBuildTree h rest (updAcc acc v false))
        (phpBuildTree h rest (updAcc acc v true))

/-- Correctness of the constructed tree: if the query order covers every PHP
variable not already correctly recorded, the tree computes the selector. -/
theorem phpBuildTree_eval {h : Nat}
    (a : Assignment (Nat.succ ((h + 1) * h))) :
    ∀ (order : List (Fin (Nat.succ ((h + 1) * h))))
      (acc : Assignment (Nat.succ ((h + 1) * h))),
      (∀ w : Fin (Nat.succ ((h + 1) * h)), w.val < (h + 1) * h →
        w ∈ order ∨ acc w = a w) →
      queryEval a (phpBuildTree h order acc) = phpSelector h a := by
  intro order
  induction order with
  | nil =>
      intro acc hinv
      show phpSelector h acc = phpSelector h a
      refine phpSelector_congr fun w hw => ?_
      rcases hinv w hw with hmem | hacc
      · exact absurd hmem (List.not_mem_nil w)
      · exact hacc
  | cons v rest ih =>
      intro acc hinv
      have hstep : ∀ b : Bool, a v = b →
          queryEval a (phpBuildTree h rest (updAcc acc v b)) =
            phpSelector h a := by
        intro b hb
        apply ih
        intro w hw
        by_cases hwv : w = v
        · right
          subst hwv
          simp [updAcc, hb]
        · rcases hinv w hw with hmem | hacc
          · rcases List.mem_cons.mp hmem with hveq | hrest
            · exact absurd hveq hwv
            · exact Or.inl hrest
          · right
            simpa [updAcc, hwv] using hacc
      cases hav : a v with
      | false =>
          have := hstep false hav
          simpa [phpBuildTree, queryEval, hav] using this
      | true =>
          have := hstep true hav
          simpa [phpBuildTree, queryEval, hav] using this

/-- The constructed tree's depth is exactly its query-order length. -/
theorem phpBuildTree_depth {h : Nat} :
    ∀ (order : List (Fin (Nat.succ ((h + 1) * h))))
      (acc : Assignment (Nat.succ ((h + 1) * h))),
      queryDepth (phpBuildTree h order acc) = order.length
  | [], _ => rfl
  | v :: rest, acc => by
      simp [phpBuildTree, queryDepth, phpBuildTree_depth rest, Nat.max_self]

/-- **Family unpadded extraction.**  The query schedule is EXACTLY the
refutation trace's `litEM` order; correctness (below) consumes the family
coverage theorem. -/
noncomputable def phpExtractTree {h : Nat}
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    QueryTree (Nat.succ ((h + 1) * h)) (PHPFalsifiedClause (h + 1) h) :=
  phpBuildTree h (traceQueryOrder π.proof) (fun _ => false)

/-- **Family trace-dependent correctness**: the extracted tree computes the
selector because — and only because — a refutation trace must query every PHP
variable (`phpCNF_family_refutationTrace_queries_var`). -/
theorem phpExtractTree_eval {h : Nat} (hh : 0 < h)
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)])
    (a : Assignment (Nat.succ ((h + 1) * h))) :
    queryEval a (phpExtractTree π) = phpSelector h a := by
  apply phpBuildTree_eval
  intro w hw
  left
  have := phpCNF_family_refutationTrace_queries_var hh π
    (pigeonOf w hw) (holeOf w hw)
  rwa [phpVar_pigeonOf_holeOf w hw] at this

/-- The extracted tree is a correct falsified-clause search tree. -/
theorem phpExtractTree_searchCorrect {h : Nat} (hh : 0 < h)
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    ∀ a : Assignment (Nat.succ ((h + 1) * h)),
      PHPFalsifiedClause.Valid a (queryEval a (phpExtractTree π)) := by
  intro a
  rw [phpExtractTree_eval hh π a]
  exact phpSelector_valid h a

/-- **Trace-resource relation**: the extracted tree's depth is EXACTLY the
trace's `litEM` query-order length. -/
theorem phpExtractTree_depth {h : Nat}
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    queryDepth (phpExtractTree π) = (traceQueryOrder π.proof).length :=
  phpBuildTree_depth _ _

/-! ## The composed family bound -/

/-- **The family route, composed.**  For every `h > 0`, every bounded-depth
refutation trace of `phpCNF (h+1) h` has `litEM` query-order length at least
`2*h` — obtained THROUGH the search connection: extraction (depth = query
count) + the parameterized adversary floor.  (The direct coverage bound
`(h+1)*h` is numerically stronger for `h > 1`; the ROUTE is the deliverable —
the first family-level trace bound through the refutation→search→adversary
composition formalized in this development.) -/
theorem phpCNF_family_traceQueryOrder_length_ge_two_h_via_search {h : Nat}
    (hh : 0 < h) (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    2 * h ≤ (traceQueryOrder π.proof).length := by
  have hfloor := phpFalsifiedClauseSearchDepthFloor (h + 1) h
    (phpExtractTree π) (phpExtractTree_searchCorrect hh π)
  rwa [phpExtractTree_depth π] at hfloor

/-- The composed family bound transferred to trace size.  (Variable-coverage
route through the search floor for the LOCAL cut-free Tait trace system;
linear in the number of PHP variables; not a Frege/PHP bound — see the module header.) -/
theorem phpCNF_family_traceSize_ge_two_h_via_search {h : Nat}
    (hh : 0 < h) (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    2 * h ≤ π.size :=
  Nat.le_trans (phpCNF_family_traceQueryOrder_length_ge_two_h_via_search hh π)
    (traceQueryOrder_length_le_size π.proof)

end PHPFamilyTraceSearchRoute
end PvNP
