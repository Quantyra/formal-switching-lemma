import PvNP.FormulaRecursiveSizeBound

/-!
# Syntactic DNF views with formula-size width bounds

`FormulaTruthTableView` gives every formula a semantic DNF view by querying all
ambient variables.  That route is broad, but its width bound is only `n`.

This module adds a syntactic DNF expansion for raw `BDFormula` syntax.  Its
terms can be exponentially many, but every term width is bounded by the raw
formula size `formulaSize F`.  This is the next honest B4-facing width-control
increment: it is structural and syntactic, not a final efficient decomposition
or product/counting theorem.

## HONEST SCOPE STATEMENT (read this)

* The syntactic DNF expansion is semantic and formula-size width bounded.
* The view constructor still requires `SimpleDNF (syntacticDNF F)`.  This
  module does not normalize repeated variables or contradictory terms.
* This does not synthesize product/counting hypotheses, ratio regimes, or a
  global formula-class `t(d,s)` theorem.
* It is not a PHP switching lemma, not a Frege/PHP lower bound, not an
  NP/circuit lower bound, and not a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaSyntacticDNF

open CNFModel
open BoundedDepthFrege
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthFregeSwitchingBridge
open FormulaRecursiveSizeBound
open GeneratedIteratedCollapseFinal
open SwitchingLemmaStatement
open SwitchingEncodeConstruct
open TreePathViews

/-! ## DNF Boolean operations -/

/-- DNF for the constant true formula. -/
def trueDNF {n : Nat} : DNF n := [[]]

/-- DNF for the constant false formula. -/
def falseDNF {n : Nat} : DNF n := []

/-- DNF for a single literal. -/
def literalDNF {n : Nat} (l : Literal n) : DNF n := [[l]]

/-- Disjunction of two DNFs. -/
def orDNF {n : Nat} (D E : DNF n) : DNF n := D ++ E

/-- Conjunction of two DNFs by distributing terms. -/
def andDNF {n : Nat} (D E : DNF n) : DNF n :=
  D.bind (fun t => E.map (fun u => t ++ u))

mutual
  /-- Syntactic DNF expansion of a raw formula. -/
  def syntacticDNF {n : Nat} : BDFormula n -> DNF n
    | .tru => trueDNF
    | .fls => falseDNF
    | .lit l => literalDNF l
    | .and children => syntacticAndDNF children
    | .or children => syntacticOrDNF children

  /-- Syntactic DNF expansion of an unbounded-fanin conjunction. -/
  def syntacticAndDNF {n : Nat} : List (BDFormula n) -> DNF n
    | [] => trueDNF
    | F :: rest => andDNF (syntacticDNF F) (syntacticAndDNF rest)

  /-- Syntactic DNF expansion of an unbounded-fanin disjunction. -/
  def syntacticOrDNF {n : Nat} : List (BDFormula n) -> DNF n
    | [] => falseDNF
    | F :: rest => orDNF (syntacticDNF F) (syntacticOrDNF rest)
end

/-! ## Semantics -/

theorem dnfEval_trueDNF {n : Nat} (a : Assignment n) :
    dnfEval a (trueDNF : DNF n) = true := by
  simp [trueDNF, dnfEval, termEval]

theorem dnfEval_falseDNF {n : Nat} (a : Assignment n) :
    dnfEval a (falseDNF : DNF n) = false := by
  simp [falseDNF, dnfEval]

theorem dnfEval_literalDNF {n : Nat} (a : Assignment n) (l : Literal n) :
    dnfEval a (literalDNF l) = litEval a l := by
  cases h : litEval a l <;> simp [literalDNF, dnfEval, termEval, h]

theorem dnfEval_orDNF {n : Nat} (a : Assignment n) (D E : DNF n) :
    dnfEval a (orDNF D E) = (dnfEval a D || dnfEval a E) := by
  simp [orDNF, dnfEval, List.any_append]

private theorem dnfEval_map_append_left {n : Nat} (a : Assignment n)
    (t : Term n) :
    forall E : DNF n,
      dnfEval a (E.map (fun u => t ++ u)) =
        (termEval a t && dnfEval a E)
  | [] => by
      simp [dnfEval]
  | u :: E => by
      rw [List.map_cons, dnfEval_cons, dnfEval_map_append_left a t E]
      rw [termEval_append]
      cases ht : termEval a t <;> cases hu : termEval a u <;>
        cases hE : dnfEval a E <;> simp [ht, hu, hE]

theorem dnfEval_andDNF {n : Nat} (a : Assignment n) (D E : DNF n) :
    dnfEval a (andDNF D E) = (dnfEval a D && dnfEval a E) := by
  induction D with
  | nil =>
      simp [andDNF, dnfEval]
  | cons t D ih =>
      rw [andDNF, List.bind_cons]
      rw [dnfEval_append, dnfEval_map_append_left]
      have ih' :
          dnfEval a (D.bind fun t => List.map (fun u => t ++ u) E) =
            (dnfEval a D && dnfEval a E) := by
        simpa [andDNF] using ih
      rw [ih']
      cases ht : termEval a t <;> cases hD : dnfEval a D <;>
        cases hE : dnfEval a E <;> simp [dnfEval_cons, ht, hD, hE]

mutual
  theorem eval_syntacticDNF {n : Nat} (a : Assignment n) :
      forall F : BDFormula n, eval a F = dnfEval a (syntacticDNF F)
    | .tru => by
        rw [eval_tru, syntacticDNF, dnfEval_trueDNF]
    | .fls => by
        rw [eval_fls, syntacticDNF, dnfEval_falseDNF]
    | .lit l => by
        simp [syntacticDNF, dnfEval_literalDNF, eval_lit]
    | .and children => by
        rw [eval_and]
        exact eval_syntacticAndDNF a children
    | .or children => by
        rw [eval_or]
        exact eval_syntacticOrDNF a children

  theorem eval_syntacticAndDNF {n : Nat} (a : Assignment n) :
      forall children : List (BDFormula n),
        children.all (fun F => eval a F) =
          dnfEval a (syntacticAndDNF children)
    | [] => by
        simp [syntacticAndDNF, dnfEval_trueDNF]
    | F :: rest => by
        rw [List.all_cons, syntacticAndDNF, dnfEval_andDNF,
          (eval_syntacticDNF a F), (eval_syntacticAndDNF a rest)]

  theorem eval_syntacticOrDNF {n : Nat} (a : Assignment n) :
      forall children : List (BDFormula n),
        children.any (fun F => eval a F) =
          dnfEval a (syntacticOrDNF children)
    | [] => by
        simp [syntacticOrDNF, dnfEval_falseDNF]
    | F :: rest => by
        rw [List.any_cons, syntacticOrDNF, dnfEval_orDNF,
          (eval_syntacticDNF a F), (eval_syntacticOrDNF a rest)]
end

/-! ## Width bounds -/

private theorem widthDNF_le_of_forall {n B : Nat} :
    forall D : DNF n, (forall t, t ∈ D -> termWidth t <= B) ->
      widthDNF D <= B
  | [], _ => by
      simp
  | t :: D, h => by
      rw [widthDNF_cons]
      exact Nat.max_le.mpr
        ⟨h t (List.mem_cons_self t D),
          widthDNF_le_of_forall D
            (fun u hu => h u (List.mem_cons_of_mem t hu))⟩

theorem widthDNF_orDNF_le {n B : Nat} {D E : DNF n}
    (hD : widthDNF D <= B) (hE : widthDNF E <= B) :
    widthDNF (orDNF D E) <= B := by
  apply widthDNF_le_of_forall
  intro t ht
  rw [orDNF] at ht
  rcases List.mem_append.mp ht with htD | htE
  · exact Nat.le_trans (termWidth_le_widthDNF htD) hD
  · exact Nat.le_trans (termWidth_le_widthDNF htE) hE

private theorem mem_andDNF {n : Nat} {D E : DNF n} {v : Term n}
    (hv : v ∈ andDNF D E) :
    exists t, t ∈ D ∧ exists u, u ∈ E ∧ v = t ++ u := by
  rw [andDNF, List.mem_bind] at hv
  rcases hv with ⟨t, htD, hv⟩
  rw [List.mem_map] at hv
  rcases hv with ⟨u, huE, rfl⟩
  exact ⟨t, htD, u, huE, rfl⟩

theorem widthDNF_andDNF_le_add {n A B : Nat} {D E : DNF n}
    (hD : widthDNF D <= A) (hE : widthDNF E <= B) :
    widthDNF (andDNF D E) <= A + B := by
  apply widthDNF_le_of_forall
  intro v hv
  rcases mem_andDNF hv with ⟨t, htD, u, huE, rfl⟩
  have ht : termWidth t <= A := Nat.le_trans (termWidth_le_widthDNF htD) hD
  have hu : termWidth u <= B := Nat.le_trans (termWidth_le_widthDNF huE) hE
  simpa [termWidth, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    Nat.add_le_add ht hu

mutual
  theorem widthDNF_syntacticDNF_le_formulaSize {n : Nat} :
      forall F : BDFormula n, widthDNF (syntacticDNF F) <= formulaSize F
    | .tru => by
        simp [syntacticDNF, trueDNF, formulaSize, termWidth]
    | .fls => by
        simp [syntacticDNF, falseDNF, formulaSize]
    | .lit l => by
        simp [syntacticDNF, literalDNF, formulaSize, termWidth]
    | .and children => by
        rw [syntacticDNF, formulaSize_and]
        have h := widthDNF_syntacticAndDNF_le_formulaSizeSum children
        have h' :
            widthDNF (syntacticAndDNF children) <=
              (children.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
          simpa [formulaSizeSum] using h
        omega
    | .or children => by
        rw [syntacticDNF, formulaSize_or]
        have h := widthDNF_syntacticOrDNF_le_formulaSizeSum children
        have h' :
            widthDNF (syntacticOrDNF children) <=
              (children.map (fun f => formulaSize f)).foldr (· + ·) 0 := by
          simpa [formulaSizeSum] using h
        omega

  theorem widthDNF_syntacticAndDNF_le_formulaSizeSum {n : Nat} :
      forall children : List (BDFormula n),
        widthDNF (syntacticAndDNF children) <= formulaSizeSum children
    | [] => by
        simp [syntacticAndDNF, trueDNF, formulaSizeSum, termWidth]
    | F :: rest => by
        rw [syntacticAndDNF]
        have hF := widthDNF_syntacticDNF_le_formulaSize F
        have hrest := widthDNF_syntacticAndDNF_le_formulaSizeSum rest
        have hand := widthDNF_andDNF_le_add hF hrest
        simpa [formulaSizeSum] using hand

  theorem widthDNF_syntacticOrDNF_le_formulaSizeSum {n : Nat} :
      forall children : List (BDFormula n),
        widthDNF (syntacticOrDNF children) <= formulaSizeSum children
    | [] => by
        simp [syntacticOrDNF, falseDNF, formulaSizeSum]
    | F :: rest => by
        rw [syntacticOrDNF]
        have hF := widthDNF_syntacticDNF_le_formulaSize F
        have hrest := widthDNF_syntacticOrDNF_le_formulaSizeSum rest
        have hOr : widthDNF (orDNF (syntacticDNF F) (syntacticOrDNF rest)) <=
            formulaSize F + formulaSizeSum rest := by
          apply widthDNF_orDNF_le
          · exact Nat.le_trans hF (Nat.le_add_right _ _)
          · exact Nat.le_trans hrest (Nat.le_add_left _ _)
        simpa [formulaSizeSum] using hOr
end

/-! ## DNF views -/

/-- Semantic syntactic DNF view, when the syntactic expansion is simple. -/
def syntacticDNFView {n : Nat} (F : BDFormula n)
    (h : SimpleDNF (syntacticDNF F)) : DNFView F where
  D := syntacticDNF F
  sem_eq := fun a => eval_syntacticDNF a F
  simple := h

theorem widthDNF_syntacticDNFView_le_formulaSize {n : Nat}
    (F : BDFormula n) (h : SimpleDNF (syntacticDNF F)) :
    widthDNF (syntacticDNFView F h).D <= formulaSize F :=
  widthDNF_syntacticDNF_le_formulaSize F

end FormulaSyntacticDNF
end PvNP
