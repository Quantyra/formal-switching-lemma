import PvNP.FormulaSyntacticDNF

/-!
# DNF normalization: duplicate-literal removal and contradictory-term deletion (S2162 core)

`PvNP.FormulaSyntacticDNF` expands raw `BDFormula` syntax into a semantically
faithful syntactic DNF, but its view constructor `syntacticDNFView` still
*assumes* `SimpleDNF (syntacticDNF F)`: the raw expansion may repeat a variable
inside a term or contain contradictory terms.  This module closes that gap with
a normalization pass:

* `dedupTerm` removes duplicate literals inside a term;
* `termContradictoryB` detects terms containing a variable with both signs;
* `normalizeDNF` dedups every term and deletes the contradictory ones.

The pass preserves pointwise evaluation (`dnfEval_normalizeDNF`), always yields
a `SimpleDNF` (`simpleDNF_normalizeDNF`, with **no hypotheses**), and never
increases DNF width (`widthDNF_normalizeDNF_le`).  Consequently every raw
bounded-depth formula gets an unconditional bottom-layer DNF view
(`normalizedDNFView`).

## HONEST SCOPE STATEMENT (read this)

* This is normalization **bookkeeping** for syntactic DNF expansions:
  duplicate-literal removal and contradictory-term deletion, with pointwise
  semantic preservation and a non-increasing width bound.
* It does **not** claim minimality or canonicity of the normalized DNF, and it
  proves no complexity property beyond the stated width inequality.
* It is not arbitrary-class width synthesis, not a full B4 theorem, not a PHP
  switching lemma, not a Frege/PHP lower bound, not an NP/circuit lower bound,
  not a Gate A result, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaSyntacticDNFNormalization

open CNFModel
open BoundedDepthFrege
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open SwitchingLemmaStatement
open SwitchingEncodeConstruct
open FormulaSyntacticDNF

/-! ## Normalization operations -/

/-- Remove duplicate literals from a term, keeping one occurrence of each
literal (`List.dedup` retains the last occurrence; the CNF-side precedent
`CNFModel.dedupClause` uses `eraseDups`, which retains the first — no lemma
here depends on which occurrence survives).  This is literal-level
deduplication only; it does not touch distinct literals sharing a variable
(those are handled by contradictory-term deletion). -/
def dedupTerm {n : Nat} (t : Term n) : Term n :=
  t.dedup

/-- Boolean test that a term is *contradictory*: it contains two literals with
the same variable and opposite signs, so it evaluates to `false` under every
assignment.  Mirrors `CNFModel.clauseHasComplementaryPair` on the term side. -/
def termContradictoryB {n : Nat} (t : Term n) : Bool :=
  t.any (fun l => t.any (literalComplementary l))

/-- Normalize a DNF: dedup every term, then delete the contradictory terms.
The order (map, then filter) mirrors `CNFModel.branchFreeCleanupStep`.  This is
a single bookkeeping pass; it claims no minimality or canonical form. -/
def normalizeDNF {n : Nat} (D : DNF n) : DNF n :=
  (D.map dedupTerm).filter (fun t => !termContradictoryB t)

/-- Propositional characterization of `termContradictoryB`: the term contains a
complementary literal pair (same variable, opposite signs). -/
theorem termContradictoryB_eq_true_iff {n : Nat} (t : Term n) :
    termContradictoryB t = true ↔
      ∃ l ∈ t, ∃ r ∈ t, l.var = r.var ∧ l.sign = !r.sign := by
  simp [termContradictoryB, literalComplementary, List.any_eq_true]

/-- Structure of membership in a normalized DNF: every surviving term is the
dedup of an original term and is itself non-contradictory. -/
theorem mem_normalizeDNF {n : Nat} {D : DNF n} {u : Term n}
    (hu : u ∈ normalizeDNF D) :
    ∃ t, t ∈ D ∧ u = dedupTerm t ∧ termContradictoryB u = false := by
  simp only [normalizeDNF] at hu
  rcases List.mem_filter.mp hu with ⟨hmap, hpred⟩
  rcases List.mem_map.mp hmap with ⟨t, htD, rfl⟩
  exact ⟨t, htD, rfl, by simpa using hpred⟩

/-- The literal list produced by `dedupTerm` has no duplicate literals. -/
theorem nodup_dedupTerm {n : Nat} (t : Term n) : (dedupTerm t).Nodup :=
  List.nodup_dedup t

/-! ## Semantic preservation -/

/-- Deduplication never changes the value of a term: `termEval` is a
conjunction over the literals present, so duplicates are absorbed. -/
theorem termEval_dedupTerm {n : Nat} (a : Assignment n) (t : Term n) :
    termEval a (dedupTerm t) = termEval a t := by
  cases h : termEval a t with
  | true =>
      simp only [termEval, List.all_eq_true] at h
      exact List.all_eq_true.mpr fun l hl =>
        h l (List.mem_dedup.mp hl)
  | false =>
      cases h' : termEval a (dedupTerm t) with
      | false => rfl
      | true =>
          exfalso
          simp only [termEval, dedupTerm, List.all_eq_true] at h'
          have hall : termEval a t = true :=
            List.all_eq_true.mpr fun l hl => h' l (List.mem_dedup.mpr hl)
          rw [h] at hall
          exact Bool.false_ne_true hall

/-- Complementary literals evaluate to complementary values. -/
private theorem litEval_complement {n : Nat} (a : Assignment n)
    {l r : Literal n} (hvar : l.var = r.var) (hsign : l.sign = !r.sign) :
    litEval a l = !litEval a r := by
  simp only [litEval, hvar, hsign]
  cases hs : r.sign <;> simp [hs]

/-- A contradictory term evaluates to `false` under every assignment: a literal
and its complement cannot both hold. -/
theorem termEval_eq_false_of_contradictory {n : Nat} {t : Term n}
    (h : termContradictoryB t = true) (a : Assignment n) :
    termEval a t = false := by
  rcases (termContradictoryB_eq_true_iff t).mp h with ⟨l, hl, r, hr, hvar, hsign⟩
  cases hev : termEval a t with
  | false => rfl
  | true =>
      exfalso
      simp only [termEval, List.all_eq_true] at hev
      have hl' : litEval a l = true := hev l hl
      have hr' : litEval a r = true := hev r hr
      have hcomp := litEval_complement a hvar hsign
      rw [hl', hr'] at hcomp
      simp at hcomp

/-- **Pointwise semantic preservation of normalization.**  Dedup rewrites each
term to a pointwise-equal term, and only always-false (contradictory) terms are
deleted, so the disjunction is unchanged under every assignment. -/
theorem dnfEval_normalizeDNF {n : Nat} (a : Assignment n) (D : DNF n) :
    dnfEval a (normalizeDNF D) = dnfEval a D := by
  induction D with
  | nil => rfl
  | cons t D ih =>
      cases hc : termContradictoryB (dedupTerm t) with
      | true =>
          have hnorm : normalizeDNF (t :: D) = normalizeDNF D := by
            simp [normalizeDNF, hc]
          have hdead : termEval a t = false := by
            rw [← termEval_dedupTerm a t]
            exact termEval_eq_false_of_contradictory hc a
          rw [hnorm, ih, dnfEval_cons, hdead, Bool.false_or]
      | false =>
          have hnorm : normalizeDNF (t :: D) = dedupTerm t :: normalizeDNF D := by
            simp [normalizeDNF, hc]
          rw [hnorm, dnfEval_cons, dnfEval_cons, ih, termEval_dedupTerm]

/-! ## Unconditional simplicity -/

/-- A term with no duplicate literals and no complementary pair is simple: two
distinct literals cannot share a variable (same variable plus
non-contradictory forces the same sign, hence equal literals), so the variable
map is injective on the term. -/
theorem simpleTerm_of_nodup_not_contradictory {n : Nat} {t : Term n}
    (hnd : t.Nodup) (hc : termContradictoryB t = false) : SimpleTerm t := by
  show (t.map (·.var)).Nodup
  apply List.Nodup.map_on
  · intro l hl r hr hvar
    have hsign : l.sign = r.sign := by
      by_contra hne
      have hopp : l.sign = !r.sign := by
        cases hls : l.sign <;> cases hrs : r.sign <;> simp_all
      have hcontr : termContradictoryB t = true :=
        (termContradictoryB_eq_true_iff t).mpr ⟨l, hl, r, hr, hvar, hopp⟩
      rw [hc] at hcontr
      exact Bool.false_ne_true hcontr
    cases l
    cases r
    simp_all
  · exact hnd

/-- **Unconditional simplicity of normalized DNFs.**  Every surviving term is a
deduped (literal-level `Nodup`) non-contradictory term, hence variable-level
`Nodup`.  No hypotheses on `D`. -/
theorem simpleDNF_normalizeDNF {n : Nat} (D : DNF n) :
    SimpleDNF (normalizeDNF D) := by
  intro u hu
  rcases mem_normalizeDNF hu with ⟨t, -, rfl, hcu⟩
  exact simpleTerm_of_nodup_not_contradictory (nodup_dedupTerm t) hcu

/-! ## Width bounds -/

/-- Deduplication never lengthens a term (`dedup` is a sublist). -/
theorem termWidth_dedupTerm_le {n : Nat} (t : Term n) :
    termWidth (dedupTerm t) ≤ termWidth t :=
  List.Sublist.length_le (List.dedup_sublist t)

private theorem widthDNF_le_of_forall_termWidth_le {n B : Nat} :
    ∀ D : DNF n, (∀ t ∈ D, termWidth t ≤ B) → widthDNF D ≤ B
  | [], _ => by simp
  | t :: D, h => by
      rw [widthDNF_cons]
      exact Nat.max_le.mpr
        ⟨h t (List.mem_cons_self t D),
          widthDNF_le_of_forall_termWidth_le D
            (fun u hu => h u (List.mem_cons_of_mem t hu))⟩

/-- **Normalization never increases width**: dedup never lengthens a term and
filtering never adds terms. -/
theorem widthDNF_normalizeDNF_le {n : Nat} (D : DNF n) :
    widthDNF (normalizeDNF D) ≤ widthDNF D := by
  apply widthDNF_le_of_forall_termWidth_le
  intro u hu
  rcases mem_normalizeDNF hu with ⟨t, htD, rfl, -⟩
  exact Nat.le_trans (termWidth_dedupTerm_le t) (termWidth_le_widthDNF htD)

/-! ## The unconditional DNF view -/

/-- **Unconditional bottom-layer DNF view of any raw bounded-depth formula**:
normalize the syntactic DNF expansion.  Semantics is `eval_syntacticDNF`
composed with `dnfEval_normalizeDNF`; simplicity is `simpleDNF_normalizeDNF`.
Unlike `syntacticDNFView`, **no** simplicity hypothesis on `F` is required. -/
def normalizedDNFView {n : Nat} (F : BDFormula n) : DNFView F where
  D := normalizeDNF (syntacticDNF F)
  sem_eq := fun a =>
    (eval_syntacticDNF a F).trans (dnfEval_normalizeDNF a (syntacticDNF F)).symm
  simple := simpleDNF_normalizeDNF (syntacticDNF F)

/-- Definitional unfolding of the normalized view's DNF, for downstream
rewriting. -/
theorem normalizedDNFView_D {n : Nat} (F : BDFormula n) :
    (normalizedDNFView F).D = normalizeDNF (syntacticDNF F) := rfl

/-- The normalized view's width is bounded by the raw syntactic DNF width
(thin corollary of `widthDNF_normalizeDNF_le`). -/
theorem widthDNF_normalizedDNFView_le {n : Nat} (F : BDFormula n) :
    widthDNF (normalizedDNFView F).D ≤ widthDNF (syntacticDNF F) :=
  widthDNF_normalizeDNF_le (syntacticDNF F)

end FormulaSyntacticDNFNormalization
end PvNP
