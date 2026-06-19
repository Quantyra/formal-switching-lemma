import PvNP.BoundedDepthRestriction
import PvNP.SwitchingClose2

/-!
AC0/proof-complexity infrastructure only: this module bridges the real
bounded-depth formula semantics for embedded DNFs to the proved term-canonical
switching lemma.  It is not a proof of `P ≠ NP`, not an NP/circuit lower bound,
and not a Frege lower bound.
-/

namespace PvNP
namespace BoundedDepthFregeSwitchingBridge

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct

/-- Embed a DNF term (a conjunction of literals) as an unbounded-fan-in
bounded-depth `and` formula. -/
def termToBD {n : Nat} (t : Term n) : BDFormula n :=
  BDFormula.and (t.map BDFormula.lit)

/-- Embed a DNF as an unbounded-fan-in `or` of embedded terms. -/
def dnfToBD {n : Nat} (D : DNF n) : BDFormula n :=
  BDFormula.or (D.map termToBD)

/-- The `termToBD` embedding has exactly the real term semantics. -/
theorem eval_termToBD {n : Nat} (a : Assignment n) (t : Term n) :
    eval a (termToBD t) = termEval a t := by
  unfold termToBD termEval
  rw [eval_and]
  induction t with
  | nil => rfl
  | cons l t ih =>
      simp [eval_lit, ih]

/-- The `dnfToBD` embedding has exactly the real DNF semantics. -/
theorem eval_dnfToBD {n : Nat} (a : Assignment n) (D : DNF n) :
    eval a (dnfToBD D) = dnfEval a D := by
  unfold dnfToBD dnfEval
  rw [eval_or]
  induction D with
  | nil => rfl
  | cons t D ih =>
      simp [eval_termToBD, ih]

/-- Semantically, restricting the embedded DNF agrees with restricting the DNF,
under every total assignment extending the partial restriction. -/
theorem eval_restrict_dnfToBD_eq_dnfRestrict {n : Nat} (ρ : Restriction n)
    (a : Assignment n) (D : DNF n) (h : Agree ρ a) :
    eval a (restrict ρ (dnfToBD D)) = dnfEval a (dnfRestrict ρ D) := by
  rw [eval_restrict ρ a (dnfToBD D) h]
  rw [eval_dnfToBD]
  exact (dnfEval_dnfRestrict ρ a h D).symm

/-- The term-canonical decision tree of the restricted DNF computes the restricted
embedded bounded-depth DNF formula, semantically under agreeing assignments. -/
theorem termCanonicalDT_computes_restrict_dnfToBD {n : Nat} (ρ : Restriction n)
    (a : Assignment n) (D : DNF n) (h : Agree ρ a) :
    dtEval a (termCanonicalDT (dnfRestrict ρ D)) =
      eval a (restrict ρ (dnfToBD D)) := by
  rw [dtEval_termCanonicalDT]
  exact (eval_restrict_dnfToBD_eq_dnfRestrict ρ a D h).symm

/-- Faithful bounded-depth DNF bridge to the proved term switching lemma for
simple DNFs: the proved counting bound is reused verbatim, and every good
restriction is witnessed by the real term-canonical decision tree computing the
real restricted bounded-depth formula. -/
theorem bdDNF_switching_bridge {n : Nat} (D : DNF n) (w s ℓ : Nat)
    (hD : SimpleDNF D) (hw : widthDNF D ≤ w) :
    (badSetTerm D s ℓ).card ≤
        (restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s ∧
      ∀ ρ : Restriction n, ρ ∈ restrictionsWithStars n ℓ → ρ ∉ badSetTerm D s ℓ →
        ∃ T : DTree n,
          dtDepth T < s ∧
            ∀ a : Assignment n, Agree ρ a →
              dtEval a T = eval a (restrict ρ (dnfToBD D)) := by
  constructor
  · exact SwitchingClose2.switchingLemmaTermSimple_proved D w s ℓ hD hw
  · intro ρ hρstars hρgood
    refine ⟨termCanonicalDT (dnfRestrict ρ D), ?_, ?_⟩
    · apply Nat.lt_of_not_ge
      intro hdeep
      apply hρgood
      unfold badSetTerm
      exact Finset.mem_filter.mpr ⟨hρstars, hdeep⟩
    · intro a ha
      exact termCanonicalDT_computes_restrict_dnfToBD ρ a D ha

end BoundedDepthFregeSwitchingBridge
end PvNP
