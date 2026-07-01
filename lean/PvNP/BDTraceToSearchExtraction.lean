import PvNP.BDResourceNormalization
import PvNP.RestrictedPHPFloor

/-!
# Concrete trace/profile-to-query extraction for the fixed `3 x 2` PHP search floor

This module constructs an actual query-tree extraction procedure from a
bounded-depth refutation trace profile of the fixed `twoCyclePath3` six-variable
CNF to the fixed `3 x 2` restricted-PHP falsified-clause search problem, and
proves its correctness.

## HONEST SCOPE STATEMENT (read this)

* Everything here concerns ONE fixed six-variable identically-false CNF
  (`twoCyclePath3GeneratedBridgeWitness_cnfBDFormula`) and ONE fixed finite
  `3 x 2` PHP falsified-clause search problem.  Nothing here is a proof-size or
  proof-depth lower bound, a Frege/PHP lower bound, an NP or circuit lower
  bound, or any statement about P vs NP.
* The extraction procedure `extractQueryTree` reads the trace's literal
  excluded-middle query order (`traceQueryOrder`) as the seed of its query
  schedule, then completes it with the remaining variables.  Because the fixed
  `3 x 2` search problem is total (the semantic selector is valid on every
  assignment), the correctness proof `extractQueryTree_evalSelector` is
  order-independent: at this fixed instance the logical dependence of
  correctness on the trace is nil.  This is stated openly; the genuine
  trace-dependence content is exactly the still-open proof-complexity route
  obligation, which this module does not touch.
* "Family" below always means the family of refutation trace profiles of the
  ONE fixed formula.  No generalization over formula families (for example
  PHP over growing rectangles) is stated or implied.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace BDTraceToSearchExtraction

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor

/-! ## Variable embedding from the six CNF variables into the `3 x 2` PHP space -/

/-- Embed the six `twoCyclePath3` CNF variables into the ambient
`Nat.succ (3 * 2)` PHP variable space, hitting exactly the six named PHP
variables `threeTwoPHPVar00 .. threeTwoPHPVar21`. -/
def phpVarEmbedding (i : Fin 6) : Fin (Nat.succ (3 * 2)) :=
  Fin.castLE (by decide) i

/-- The embedding is injective. -/
theorem phpVarEmbedding_injective : Function.Injective phpVarEmbedding := by
  decide

theorem phpVarEmbedding_eq_var00 : phpVarEmbedding 0 = threeTwoPHPVar00 := by decide
theorem phpVarEmbedding_eq_var01 : phpVarEmbedding 1 = threeTwoPHPVar01 := by decide
theorem phpVarEmbedding_eq_var10 : phpVarEmbedding 2 = threeTwoPHPVar10 := by decide
theorem phpVarEmbedding_eq_var11 : phpVarEmbedding 3 = threeTwoPHPVar11 := by decide
theorem phpVarEmbedding_eq_var20 : phpVarEmbedding 4 = threeTwoPHPVar20 := by decide
theorem phpVarEmbedding_eq_var21 : phpVarEmbedding 5 = threeTwoPHPVar21 := by decide

/-- View an accumulator of answers for the six CNF variables as an ambient
`3 x 2` PHP assignment (unembedded ambient variables read `false`). -/
def boolsToAssignment (acc : Fin 6 → Bool) : Assignment (Nat.succ (3 * 2)) :=
  fun v => if h : v.val < 6 then acc ⟨v.val, h⟩ else false

/-- The ambient view of an accumulator reads back the accumulator on every
embedded variable. -/
theorem boolsToAssignment_phpVarEmbedding (acc : Fin 6 → Bool) (i : Fin 6) :
    boolsToAssignment acc (phpVarEmbedding i) = acc i := by
  rcases i with ⟨v, hv⟩
  show (if h : v < 6 then acc ⟨v, h⟩ else false) = acc ⟨v, hv⟩
  rw [dif_pos hv]

/-- The fixed finite selector only inspects the six named PHP variables, so it is
a congruence for agreement on those six variables. -/
theorem selector_congr (a b : Assignment (Nat.succ (3 * 2)))
    (h00 : a threeTwoPHPVar00 = b threeTwoPHPVar00)
    (h01 : a threeTwoPHPVar01 = b threeTwoPHPVar01)
    (h10 : a threeTwoPHPVar10 = b threeTwoPHPVar10)
    (h11 : a threeTwoPHPVar11 = b threeTwoPHPVar11)
    (h20 : a threeTwoPHPVar20 = b threeTwoPHPVar20)
    (h21 : a threeTwoPHPVar21 = b threeTwoPHPVar21) :
    threeTwoPHPFalsifiedClauseSelector a = threeTwoPHPFalsifiedClauseSelector b := by
  simp only [threeTwoPHPFalsifiedClauseSelector, h00, h01, h10, h11, h20, h21]

/-! ## Trace query order -/

/-- Collect the literal excluded-middle variables of a bounded-depth proof trace
in derivation order.  This is the trace-supplied seed of the extraction's query
schedule. -/
def traceQueryOrder {n : Nat} {Γ : List (BDFormula n)} :
    BDProofTrace Γ → List (Fin n)
  | .truAx _ _ => []
  | .litEM _ v _ _ => [v]
  | .weaken h _ => traceQueryOrder h
  | .orIntro h => traceQueryOrder h
  | @BDProofTrace.andIntro _ Γ l h =>
      (l.attach.map (fun f => traceQueryOrder (h f.1 f.2))).foldr
        (fun x acc => x ++ acc) []

/-- All six CNF variables in index order. -/
def allFin6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- Every variable occurs in `allFin6`. -/
theorem mem_allFin6 : ∀ i : Fin 6, i ∈ allFin6 := by decide

/-! ## Query-tree construction -/

/-- Update an accumulator of answers at one variable. -/
def updateAcc (acc : Fin 6 → Bool) (v : Fin 6) (b : Bool) : Fin 6 → Bool :=
  fun i => if i = v then b else acc i

/-- Build an output-valued query tree that queries the embedded image of each
variable in `order`, records the answers, and outputs the fixed finite selector
of the recorded answers at its leaves. -/
def buildTree : List (Fin 6) → (Fin 6 → Bool) →
    QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause
  | [], acc =>
      QueryTree.leaf (threeTwoPHPFalsifiedClauseSelector (boolsToAssignment acc))
  | v :: rest, acc =>
      QueryTree.node (phpVarEmbedding v)
        (buildTree rest (updateAcc acc v false))
        (buildTree rest (updateAcc acc v true))

/-- Correctness of the constructed tree: if the query order covers every
variable not already correctly recorded in the accumulator, the tree evaluates
to the fixed finite semantic selector of the ambient assignment. -/
theorem buildTree_evalSelector (a : Assignment (Nat.succ (3 * 2)))
    (order : List (Fin 6)) :
    ∀ acc : Fin 6 → Bool,
      (∀ i : Fin 6, i ∈ order ∨ acc i = a (phpVarEmbedding i)) →
      queryEval a (buildTree order acc) = threeTwoPHPFalsifiedClauseSelector a := by
  induction order with
  | nil =>
      intro acc hinv
      have hall : ∀ i : Fin 6, acc i = a (phpVarEmbedding i) := by
        intro i
        rcases hinv i with hmem | hacc
        · exact absurd hmem (List.not_mem_nil i)
        · exact hacc
      have hb : ∀ i : Fin 6,
          boolsToAssignment acc (phpVarEmbedding i) = a (phpVarEmbedding i) := by
        intro i
        rw [boolsToAssignment_phpVarEmbedding]
        exact hall i
      show threeTwoPHPFalsifiedClauseSelector (boolsToAssignment acc) =
        threeTwoPHPFalsifiedClauseSelector a
      refine selector_congr _ _ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← phpVarEmbedding_eq_var00]; exact hb 0
      · rw [← phpVarEmbedding_eq_var01]; exact hb 1
      · rw [← phpVarEmbedding_eq_var10]; exact hb 2
      · rw [← phpVarEmbedding_eq_var11]; exact hb 3
      · rw [← phpVarEmbedding_eq_var20]; exact hb 4
      · rw [← phpVarEmbedding_eq_var21]; exact hb 5
  | cons v rest ih =>
      intro acc hinv
      have hstep : ∀ b : Bool, a (phpVarEmbedding v) = b →
          queryEval a (buildTree rest (updateAcc acc v b)) =
            threeTwoPHPFalsifiedClauseSelector a := by
        intro b hb
        apply ih
        intro i
        by_cases hiv : i = v
        · right
          subst hiv
          simp [updateAcc, hb]
        · rcases hinv i with hmem | hacc
          · rcases List.mem_cons.mp hmem with hveq | hrest
            · exact absurd hveq hiv
            · exact Or.inl hrest
          · right
            simpa [updateAcc, hiv] using hacc
      cases hav : a (phpVarEmbedding v) with
      | false =>
          have := hstep false hav
          simpa [buildTree, queryEval, hav] using this
      | true =>
          have := hstep true hav
          simpa [buildTree, queryEval, hav] using this

/-! ## The extraction procedure -/

/-- Extract a `3 x 2` PHP falsified-clause query tree from a bounded-depth
refutation trace profile of the fixed `twoCyclePath3` CNF.  The query schedule
starts with the trace's literal excluded-middle order and is completed with the
remaining variables; the leaves output the fixed finite semantic selector of the
recorded answers. -/
def extractQueryTree
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) :
    QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause :=
  buildTree (traceQueryOrder profile.trace.proof ++ allFin6) (fun _ => false)

/-- **Extraction correctness.**  For every profile of the fixed formula, the
extracted tree evaluates to the fixed finite semantic selector on every ambient
assignment.  Correctness is order-independent, so it holds for the whole
trace-profile family of the fixed formula. -/
theorem extractQueryTree_evalSelector
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (a : Assignment (Nat.succ (3 * 2))) :
    queryEval a (extractQueryTree profile) =
      threeTwoPHPFalsifiedClauseSelector a := by
  apply buildTree_evalSelector
  intro i
  exact Or.inl (List.mem_append.mpr (Or.inr (mem_allFin6 i)))

/-- The extracted tree computes exactly the already-audited fixed `3 x 2` query
tree on every ambient assignment. -/
theorem extractQueryTree_matchesFixedTree
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula])
    (a : Assignment (Nat.succ (3 * 2))) :
    queryEval a (extractQueryTree profile) =
      queryEval a threeTwoPHPFalsifiedClauseQueryTree := by
  rw [extractQueryTree_evalSelector, threeTwoPHPFalsifiedClauseQueryTree_evalSelector]

/-- The extracted tree always outputs a falsified clause. -/
theorem extractQueryTree_searchCorrect
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) :
    ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a (extractQueryTree profile)) :=
  threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector
    (extractQueryTree profile) (extractQueryTree_evalSelector profile)

/-- The extracted tree inherits the fixed `3 x 2` search depth floor. -/
theorem extractQueryTree_depthFloor
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) :
    2 ≤ queryDepth (extractQueryTree profile) :=
  threeTwoPHPFalsifiedClauseSearchDepthFloor
    (extractQueryTree profile) (extractQueryTree_searchCorrect profile)

/-- The extracted tree also inherits the S2066 adversary-argument search depth
floor of three. -/
theorem extractQueryTree_depthFloor_three
    (profile :
      BDRefutationTraceProfile
        [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula]) :
    3 ≤ queryDepth (extractQueryTree profile) :=
  threeTwoPHPFalsifiedClauseSearchDepthFloor_three
    (extractQueryTree profile) (extractQueryTree_searchCorrect profile)

/-! ## Instance-compatibility facts -/

/-- The fixed six-variable CNF evaluates to `false` under every assignment (as a
bounded-depth formula). -/
theorem twoCyclePath3_cnfBDFormula_eval_false (b : Assignment 6) :
    BoundedDepthFrege.eval b twoCyclePath3GeneratedBridgeWitness_cnfBDFormula =
      false := by
  rw [twoCyclePath3GeneratedBridgeWitness_cnfBDFormula_semantics]
  exact twoCyclePath3GeneratedBridgeWitness_cnfEval_eq_false b

/-- **Common-extension property.**  Every ambient `3 x 2` PHP assignment
simultaneously falsifies the embedded fixed CNF and admits a valid falsified
clause named by the fixed finite selector. -/
theorem twoCyclePath3ThreeTwoPHP_commonExtension
    (a : Assignment (Nat.succ (3 * 2))) :
    BoundedDepthFrege.eval (fun i => a (phpVarEmbedding i))
        twoCyclePath3GeneratedBridgeWitness_cnfBDFormula = false ∧
      ThreeTwoPHPFalsifiedClause.Valid a (threeTwoPHPFalsifiedClauseSelector a) :=
  ⟨twoCyclePath3_cnfBDFormula_eval_false _,
    threeTwoPHPFalsifiedClauseSelector_valid a⟩

/-! ## Resource facts for the fixed tree -/

/-- The already-audited fixed `3 x 2` query tree queries all six PHP variables. -/
theorem fixedTree_queryDepth_eq_six :
    queryDepth threeTwoPHPFalsifiedClauseQueryTree = 6 := by decide

end BDTraceToSearchExtraction
end PvNP
