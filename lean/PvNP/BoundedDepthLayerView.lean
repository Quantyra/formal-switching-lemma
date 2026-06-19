import PvNP.BoundedDepthFregeSwitchingBridge

/-!
# Bottom-layer DNF views for bounded-depth formulas

P-vs-NP-relevant proof-complexity infrastructure under the repository's claims
boundary: this module exposes an explicit bottom-layer DNF view for real
`BDFormula` formulas and reuses the faithful switching bridge for one-step
collapse statements.  It is not a Frege/PHP lower bound yet, and it makes no
`P ≠ NP` or NP lower-bound claim.
-/

namespace PvNP
namespace BoundedDepthLayerView

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct

/-- A semantic bottom-layer DNF view of a real bounded-depth formula.  The view
records the concrete DNF and the exact Boolean-function equality to the formula;
simplicity is the hypothesis needed by the proved switching bridge. -/
structure DNFView {n : Nat} (F : BDFormula n) where
  D : DNF n
  sem_eq : ∀ a : Assignment n, eval a F = dnfEval a D
  simple : SimpleDNF D

namespace DNFView

/-- Restricting a formula carrying a DNF view agrees semantically with
restricting the viewed DNF, under every total assignment extending the partial
restriction. -/
theorem eval_restrict_eq_dnfRestrict {n : Nat} {F : BDFormula n} (V : DNFView F)
    (ρ : Restriction n) (a : Assignment n) (h : Agree ρ a) :
    eval a (restrict ρ F) = dnfEval a (dnfRestrict ρ V.D) := by
  rw [eval_restrict ρ a F h]
  rw [V.sem_eq a]
  exact (dnfEval_dnfRestrict ρ a h V.D).symm

end DNFView

/-- Any embedded DNF has the evident DNF view, provided the DNF is simple. -/
def dnfToBD_dnfView {n : Nat} (D : DNF n) (hD : SimpleDNF D) :
    DNFView (BoundedDepthFregeSwitchingBridge.dnfToBD D) where
  D := D
  sem_eq := fun a => BoundedDepthFregeSwitchingBridge.eval_dnfToBD a D
  simple := hD

/-- One-step switching collapse for any real bounded-depth formula equipped with
a simple DNF bottom-layer view.  The counting bound is exactly the bridge's DNF
bound, and good restrictions yield a shallow decision tree computing the real
restricted formula. -/
theorem bdFormula_dnfView_switching_collapse {n : Nat} {F : BDFormula n}
    (V : DNFView F) (w s ℓ : Nat) (hw : widthDNF V.D ≤ w) :
    (badSetTerm V.D s ℓ).card ≤ (restrictionsWithStars n (ℓ - s)).card * (8 * w)^s ∧
    ∀ ρ, ρ ∈ restrictionsWithStars n ℓ → ρ ∉ badSetTerm V.D s ℓ →
      ∃ T : DTree n, dtDepth T < s ∧
        ∀ a : Assignment n, Agree ρ a → dtEval a T = eval a (restrict ρ F) := by
  rcases BoundedDepthFregeSwitchingBridge.bdDNF_switching_bridge V.D w s ℓ V.simple hw with
    ⟨hcard, hcollapse⟩
  constructor
  · exact hcard
  · intro ρ hρstars hρgood
    rcases hcollapse ρ hρstars hρgood with ⟨T, hdepth, hT⟩
    refine ⟨T, hdepth, ?_⟩
    intro a ha
    calc
      dtEval a T = eval a (restrict ρ (BoundedDepthFregeSwitchingBridge.dnfToBD V.D)) :=
        hT a ha
      _ = eval a (BoundedDepthFregeSwitchingBridge.dnfToBD V.D) :=
        eval_restrict ρ a (BoundedDepthFregeSwitchingBridge.dnfToBD V.D) ha
      _ = dnfEval a V.D :=
        BoundedDepthFregeSwitchingBridge.eval_dnfToBD a V.D
      _ = eval a F :=
        (V.sem_eq a).symm
      _ = eval a (restrict ρ F) :=
        (eval_restrict ρ a F ha).symm

/-- Minimal non-vacuity witness: the empty DNF embeds as a bounded-depth formula
with a simple DNF view. -/
def emptyDNFView (n : Nat) :
    DNFView (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n)) :=
  dnfToBD_dnfView ([] : DNF n) (by intro t ht; cases ht)

/-- The switching-collapse theorem instantiated on the empty embedded DNF view. -/
theorem emptyDNFView_switching_collapse (n w s ℓ : Nat) :
    (badSetTerm (emptyDNFView n).D s ℓ).card ≤
        (restrictionsWithStars n (ℓ - s)).card * (8 * w)^s ∧
      ∀ ρ, ρ ∈ restrictionsWithStars n ℓ → ρ ∉ badSetTerm (emptyDNFView n).D s ℓ →
        ∃ T : DTree n, dtDepth T < s ∧
          ∀ a : Assignment n, Agree ρ a →
            dtEval a T = eval a (restrict ρ (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n))) := by
  exact bdFormula_dnfView_switching_collapse (emptyDNFView n) w s ℓ (Nat.zero_le w)

end BoundedDepthLayerView
end PvNP
