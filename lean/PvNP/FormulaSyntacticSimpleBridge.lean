import PvNP.FormulaSyntacticDNF

/-!
# Structurally simple syntactic DNF bridge

`FormulaSyntacticDNF` builds a semantic syntactic DNF expansion for arbitrary
raw `BDFormula` syntax and proves the formula-size width bound.  This module
adds an explicit sufficient condition under which that syntactic expansion is a
`SimpleDNF`, then routes those formulas through the already-proved simple-DNF
switching bridge.

## Honest scope

* The structural predicate is sufficient, not complete.
* This does not normalize duplicate variables, remove contradictory terms, or
  prove arbitrary syntactic DNFs simple.
* The switching conclusion is over `badSetTerm (syntacticDNF F)`, with witnesses
  computing the restricted raw formula semantically under agreeing assignments.
* This is not the efficient depth-d B4 decomposition, not a global `t(d,s)`
  theorem, not a PHP switching lemma, not a Frege/PHP lower bound, and not a
  P-vs-NP result.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaSyntacticSimpleBridge

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthFrege
open BoundedDepthCanonicalDT
open BoundedDepthFregeSwitchingBridge
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveSizeBound
open FormulaSyntacticDNF
open GeneratedIteratedCollapseFinal
open SwitchingEncodeConstruct
open SwitchingLemmaStatement

/-! ## Simple-DNF closure lemmas for the syntactic constructors -/

/-- Two DNFs are compatible when every distributed conjunction term remains a
simple term.  This is a sufficient local condition for conjunction synthesis. -/
def CompatibleDNF {n : Nat} (D E : DNF n) : Prop :=
  forall t, t ∈ D -> forall u, u ∈ E -> SimpleTerm (t ++ u)

theorem simpleDNF_trueDNF {n : Nat} : SimpleDNF (trueDNF : DNF n) := by
  intro t ht
  simp [trueDNF] at ht
  subst t
  simp [SimpleTerm]

theorem simpleDNF_falseDNF {n : Nat} : SimpleDNF (falseDNF : DNF n) := by
  intro t ht
  cases ht

theorem simpleDNF_literalDNF {n : Nat} (l : Literal n) :
    SimpleDNF (literalDNF l) := by
  intro t ht
  simp [literalDNF] at ht
  subst t
  simp [SimpleTerm]

theorem simpleDNF_orDNF {n : Nat} {D E : DNF n}
    (hD : SimpleDNF D) (hE : SimpleDNF E) :
    SimpleDNF (orDNF D E) := by
  intro t ht
  rw [orDNF] at ht
  rcases List.mem_append.mp ht with htD | htE
  · exact hD t htD
  · exact hE t htE

theorem simpleDNF_andDNF_of_compatible {n : Nat} {D E : DNF n}
    (hDE : CompatibleDNF D E) :
    SimpleDNF (andDNF D E) := by
  intro v hv
  rw [andDNF, List.mem_bind] at hv
  rcases hv with ⟨t, htD, hv⟩
  rw [List.mem_map] at hv
  rcases hv with ⟨u, huE, rfl⟩
  exact hDE t htD u huE

/-! ## A structural sufficient predicate for syntactic DNF simplicity -/

mutual
  /-- Raw formulas whose syntactic DNF expansion is structurally certified
  simple by the list predicates below. -/
  def syntacticFormulaSimpleDNF {n : Nat} : BDFormula n -> Prop
    | .tru => True
    | .fls => True
    | .lit _ => True
    | .and children => syntacticAndListSimpleDNF children
    | .or children => syntacticOrListSimpleDNF children

  /-- A conjunction list is structurally simple when its head and tail are
  structurally simple and their distributed syntactic DNFs are compatible. -/
  def syntacticAndListSimpleDNF {n : Nat} : List (BDFormula n) -> Prop
    | [] => True
    | F :: rest =>
        syntacticFormulaSimpleDNF F /\
          syntacticAndListSimpleDNF rest /\
            CompatibleDNF (syntacticDNF F) (syntacticAndDNF rest)

  /-- A disjunction list is structurally simple when every disjunct is
  structurally simple; disjunction only appends terms. -/
  def syntacticOrListSimpleDNF {n : Nat} : List (BDFormula n) -> Prop
    | [] => True
    | F :: rest =>
        syntacticFormulaSimpleDNF F /\ syntacticOrListSimpleDNF rest
end

mutual
  theorem simpleDNF_syntacticDNF_of_simple {n : Nat} :
      forall F : BDFormula n,
        syntacticFormulaSimpleDNF F -> SimpleDNF (syntacticDNF F)
    | .tru, _ => by
        simpa [syntacticDNF] using (simpleDNF_trueDNF : SimpleDNF (trueDNF : DNF n))
    | .fls, _ => by
        simpa [syntacticDNF] using (simpleDNF_falseDNF : SimpleDNF (falseDNF : DNF n))
    | .lit l, _ => by
        simpa [syntacticDNF] using simpleDNF_literalDNF l
    | .and children, h => by
        rw [syntacticDNF]
        exact simpleDNF_syntacticAndDNF_of_simple children h
    | .or children, h => by
        rw [syntacticDNF]
        exact simpleDNF_syntacticOrDNF_of_simple children h

  theorem simpleDNF_syntacticAndDNF_of_simple {n : Nat} :
      forall children : List (BDFormula n),
        syntacticAndListSimpleDNF children ->
          SimpleDNF (syntacticAndDNF children)
    | [], _ => by
        simpa [syntacticAndDNF] using (simpleDNF_trueDNF : SimpleDNF (trueDNF : DNF n))
    | F :: rest, h => by
        rw [syntacticAndDNF]
        exact simpleDNF_andDNF_of_compatible h.2.2

  theorem simpleDNF_syntacticOrDNF_of_simple {n : Nat} :
      forall children : List (BDFormula n),
        syntacticOrListSimpleDNF children ->
          SimpleDNF (syntacticOrDNF children)
    | [], _ => by
        simpa [syntacticOrDNF] using
          (simpleDNF_falseDNF : SimpleDNF (falseDNF : DNF n))
    | F :: rest, h => by
        rw [syntacticOrDNF]
        exact simpleDNF_orDNF
          (simpleDNF_syntacticDNF_of_simple F h.1)
          (simpleDNF_syntacticOrDNF_of_simple rest h.2)
end

/-! ## View and switching bridge surfaces -/

/-- Semantic syntactic DNF view from the structural simplicity predicate. -/
def syntacticDNFViewOfFormulaSimple {n : Nat} (F : BDFormula n)
    (h : syntacticFormulaSimpleDNF F) : DNFView F :=
  syntacticDNFView F (simpleDNF_syntacticDNF_of_simple F h)

theorem widthDNF_syntacticDNFViewOfFormulaSimple_le_formulaSize {n : Nat}
    (F : BDFormula n) (h : syntacticFormulaSimpleDNF F) :
    widthDNF (syntacticDNFViewOfFormulaSimple F h).D <= formulaSize F :=
  widthDNF_syntacticDNF_le_formulaSize F

/-- Restricting the embedded syntactic DNF is semantically the same as
restricting the original raw formula under any agreeing total assignment. -/
theorem eval_restrict_syntacticDNF_eq {n : Nat}
    (rho : Restriction n) (a : Assignment n) (F : BDFormula n)
    (h : Agree rho a) :
    eval a (restrict rho (dnfToBD (syntacticDNF F))) =
      eval a (restrict rho F) := by
  rw [eval_restrict rho a (dnfToBD (syntacticDNF F)) h]
  rw [eval_restrict rho a F h]
  rw [eval_dnfToBD]
  exact (eval_syntacticDNF a F).symm

/-- Structurally simple raw formulas inherit the proved simple-DNF switching
bridge through their syntactic DNF, with formula-size width control. -/
theorem syntacticFormula_switching_bridge {n : Nat} (F : BDFormula n)
    (w s ell : Nat) (hSimple : syntacticFormulaSimpleDNF F)
    (hw : formulaSize F <= w) :
    (badSetTerm (syntacticDNF F) s ell).card <=
        (restrictionsWithStars n (ell - s)).card * (8 * w) ^ s /\
      forall rho : Restriction n, rho ∈ restrictionsWithStars n ell ->
        rho ∉ badSetTerm (syntacticDNF F) s ell ->
          exists T : DTree n,
            dtDepth T < s /\
              forall a : Assignment n, Agree rho a ->
                dtEval a T = eval a (restrict rho F) := by
  have hD : SimpleDNF (syntacticDNF F) :=
    simpleDNF_syntacticDNF_of_simple F hSimple
  have hwD : widthDNF (syntacticDNF F) <= w :=
    Nat.le_trans (widthDNF_syntacticDNF_le_formulaSize F) hw
  rcases bdDNF_switching_bridge (syntacticDNF F) w s ell hD hwD with
    ⟨hcard, hgood⟩
  refine ⟨hcard, ?_⟩
  intro rho hrhoStars hrhoGood
  rcases hgood rho hrhoStars hrhoGood with ⟨T, hdepth, hsem⟩
  refine ⟨T, hdepth, ?_⟩
  intro a ha
  rw [hsem a ha]
  exact eval_restrict_syntacticDNF_eq rho a F ha

end FormulaSyntacticSimpleBridge
end PvNP
