import PvNP.PHPMatchingDistribution
import Mathlib.Data.Fintype.Perm

/-!
# The full matching-restriction space: subsets times permutations

Gate A rung 3 previously counted the identity-matching subfamily: choose the
fixed pigeon subset `S`, then fix those rows along the identity permutation.
This module removes that identity-only limitation by using the finite product
space

  `subsetSpace h s × Equiv.Perm (Fin h)`.

Each point fixes the pigeons in `S` along an arbitrary permutation.  The
variable-level star count is the old subset count multiplied by the number of
permutations, because whether `x_{i,j}` is free depends only on whether pigeon
`i` is outside `S`.  The existing partial-matching depth floor also transfers
to every point of this larger space.

## HONEST SCOPE STATEMENT (read this)

* This is exact finite counting and a probability-one floor transfer over the
  richer matching space.  It is still NOT a PHP switching lemma: no
  collapse-probability upper bound for restricted formulas is stated or proved.
* The space is permutations of `h` holes for `h` pigeons, not injections for
  rectangular `p > h` PHP.
* Formula/proof-complexity infrastructure only: NOT a Frege/PHP proof-size
  lower bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingDistribution

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPSearchFloor
open PHPBooleanDepthFloor
open PHPRestrictedDepthFloor
open PHPMatchingDistribution

/-! ## The full permutation-matching space -/

/-- The finite space of all hole permutations. -/
def permSpace (h : Nat) : Finset (Equiv.Perm (Fin h)) :=
  Finset.univ

/-- The full `h x h` matching-restriction space at fixed-set size `s`:
choose `s` pigeons and choose an arbitrary permutation for their matched holes. -/
def fullMatchingSpace (h s : Nat) :
    Finset (Finset (Fin h) × Equiv.Perm (Fin h)) :=
  (subsetSpace h s).product (permSpace h)

theorem card_permSpace (h : Nat) :
    (permSpace h).card = Fintype.card (Equiv.Perm (Fin h)) := by
  simp [permSpace]

/-- The full space cardinality is `choose h s` times the number of
permutations. -/
theorem card_fullMatchingSpace (h s : Nat) :
    (fullMatchingSpace h s).card =
      Nat.choose h s * Fintype.card (Equiv.Perm (Fin h)) := by
  calc
    (fullMatchingSpace h s).card
        = (subsetSpace h s).card * (permSpace h).card := by
          exact Finset.card_product (subsetSpace h s) (permSpace h)
    _ = Nat.choose h s * Fintype.card (Equiv.Perm (Fin h)) := by
          rw [card_subsetSpace, card_permSpace]

/-- The restriction associated to a point of the full matching space. -/
def fullRestrictionOf {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    Restriction (Nat.succ (h * h)) :=
  matchingRestriction (fun i => decide (i ∈ P.1)) (fun i => P.2 i)

/-- A PHP variable is free exactly when its pigeon row is not fixed; the
permutation component affects the fixed values but not the star set. -/
theorem fullRestrictionOf_phpVar_eq_none_iff {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) (i j : Fin h) :
    fullRestrictionOf P (phpVar h h i j) = none ↔ i ∉ P.1 := by
  have hlt := phpVar_lt (p := h) (h := h) i j
  rw [fullRestrictionOf, matchingRestriction, dif_pos hlt,
    pigeonOf_phpVar i j hlt]
  by_cases hi : i ∈ P.1
  · simp [hi]
  · simp [hi]

/-! ## Star counts in the full space -/

/-- Every PHP variable is free in `choose (h-1) s * h!` points of the full
matching space. -/
theorem phpVar_freeCount_full {h s : Nat} (i j : Fin h) :
    ((fullMatchingSpace h s).filter
      (fun P => fullRestrictionOf P (phpVar h h i j) = none)).card =
      Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)) := by
  have hfilter :
      (fullMatchingSpace h s).filter
        (fun P => fullRestrictionOf P (phpVar h h i j) = none) =
        ((subsetSpace h s).filter (fun S => i ∉ S)).product (permSpace h) := by
    ext P
    rw [Finset.mem_filter, fullRestrictionOf_phpVar_eq_none_iff,
      fullMatchingSpace, permSpace]
    constructor
    · rintro ⟨hmem, hfree⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).1, hfree⟩,
          by simp⟩
    · intro hmem
      have hp := Finset.mem_product.mp hmem
      have hS := Finset.mem_filter.mp hp.1
      exact ⟨Finset.mem_product.mpr ⟨hS.1, hp.2⟩, hS.2⟩
  calc
    ((fullMatchingSpace h s).filter
      (fun P => fullRestrictionOf P (phpVar h h i j) = none)).card
        = (((subsetSpace h s).filter (fun S => i ∉ S)).product
            (permSpace h)).card := by
          rw [hfilter]
    _ = ((subsetSpace h s).filter (fun S => i ∉ S)).card *
            (permSpace h).card := by
          exact Finset.card_product _ _
    _ = Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)) := by
          rw [freeCount_eq, card_permSpace]

/-- The exact star-probability ratio for the full space, in counting form. -/
theorem star_ratio_full (h s : Nat) :
    h * (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h))) =
      (h - s) * (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h))) := by
  calc
    h * (Nat.choose (h - 1) s * Fintype.card (Equiv.Perm (Fin h)))
        = (h * Nat.choose (h - 1) s) *
            Fintype.card (Equiv.Perm (Fin h)) := by
          rw [Nat.mul_assoc]
    _ = ((h - s) * Nat.choose h s) *
          Fintype.card (Equiv.Perm (Fin h)) := by
          rw [star_ratio h s]
    _ = (h - s) *
          (Nat.choose h s * Fintype.card (Equiv.Perm (Fin h))) := by
          rw [Nat.mul_assoc]

/-- Variable-level star ratio over the full matching space. -/
theorem phpVar_star_ratio_full {h s : Nat} (i j : Fin h) :
    h * ((fullMatchingSpace h s).filter
      (fun P => fullRestrictionOf P (phpVar h h i j) = none)).card =
      (h - s) * (fullMatchingSpace h s).card := by
  rw [phpVar_freeCount_full, card_fullMatchingSpace, star_ratio_full]

/-! ## The depth floor holds at every point of the full space -/

/-- **Probability-one floor transfer over the full matching space.**  For every
subset/permutation point, every decision tree computing the restricted `h x h`
PHP function has depth at least `(h - s) * h`. -/
theorem fullMatchingSpace_depthFloor {h s : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hP : P ∈ fullMatchingSpace h s)
    (T : DTree (Nat.succ (h * h)))
    (hT : ∀ a : Assignment (Nat.succ (h * h)),
      Agree (fullRestrictionOf P) a →
      dtEval a T =
        eval a (restrict (fullRestrictionOf P)
          (restrictedPHPFormula (fullPHPView h)))) :
    (h - s) * h ≤ dtDepth T := by
  have hSmem : P.1 ∈ subsetSpace h s := by
    have hP' : P ∈ (subsetSpace h s).product (permSpace h) := by
      simpa [fullMatchingSpace] using hP
    exact (Finset.mem_product.mp hP').1
  have hSmem' :
      P.1 ∈ Finset.powersetCard s (Finset.univ : Finset (Fin h)) := by
    simpa [subsetSpace] using hSmem
  have hScard : P.1.card = s := by
    exact (Finset.mem_powersetCard.mp hSmem').2
  have hmaster := matchingRestriction_depthFloor
    (fun i => decide (i ∈ P.1)) (fun i => P.2 i) (fun j => P.2.symm j)
    (by intro i; simp) (by intro j; simp) T (by
      simpa [fullRestrictionOf] using hT)
  rwa [freeVars_length, freeRows_card P.1 hScard] at hmaster

/-- Non-vacuity, pointwise: a full truth-table tree computes every restricted
function in the full matching space. -/
theorem fullMatchingSpace_correctTree_exists {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    ∃ T : DTree (Nat.succ (h * h)),
      (∀ a : Assignment (Nat.succ (h * h)),
        Agree (fullRestrictionOf P) a →
        dtEval a T =
          eval a (restrict (fullRestrictionOf P)
            (restrictedPHPFormula (fullPHPView h)))) ∧
      dtDepth T = h * h + 1 := by
  refine ⟨dtOfFun
    (fun a => eval a (restrict (fullRestrictionOf P)
      (restrictedPHPFormula (fullPHPView h))))
    (finList (Nat.succ (h * h))) (fun _ => false), fun a _ => ?_, ?_⟩
  · apply dtOfFun_eval
    intro v
    exact Or.inl (mem_finList _ v)
  · rw [dtOfFun_depth, finList_length]

end PHPFullMatchingDistribution
end PvNP
