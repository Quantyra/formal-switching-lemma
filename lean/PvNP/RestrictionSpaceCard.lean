import PvNP.SwitchingLemmaStatement
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Closed-form cardinality of the star-restriction space

This lightweight module isolates the exact count
`|restrictionsWithStars n ℓ| = C(n, ℓ) * 2 ^ (n - ℓ)` from the heavier
restriction-composition / generated-collapse development, so small concrete
consumers can use the count without importing the B4 composition route.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RestrictionSpaceCard

open BoundedDepthRestriction
open SwitchingLemmaStatement

/-! ## Closed-form cardinality of the star space -/

/-- The star set of a restriction (the variables it leaves free). -/
def starSet {n : Nat} (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ρ v = none)

theorem stars_eq_starSet_card {n : Nat} (ρ : Restriction n) :
    stars ρ = (starSet ρ).card := rfl

theorem mem_starSet {n : Nat} {ρ : Restriction n} {v : Fin n} :
    v ∈ starSet ρ ↔ ρ v = none := by
  simp [starSet]

/-- The fiber of restrictions whose star set is exactly `S`. -/
def starFiber {n : Nat} (S : Finset (Fin n)) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ => starSet ρ = S)

theorem mem_starFiber {n : Nat} {S : Finset (Fin n)} {ρ : Restriction n} :
    ρ ∈ starFiber S ↔ starSet ρ = S := by
  simp [starFiber]

/-- Each star-set fiber has exactly `2 ^ (n - |S|)` restrictions: the free
choice of a Boolean on every non-starred variable. -/
theorem starFiber_card {n : Nat} (S : Finset (Fin n)) :
    (starFiber S).card = 2 ^ (n - S.card) := by
  classical
  have hbij : (starFiber S).card =
      (Finset.univ : Finset ({v : Fin n // v ∈ Sᶜ} → Bool)).card := by
    refine Finset.card_bij'
      (fun ρ _ => fun v => (ρ v.1).getD false)
      (fun b _ => fun v =>
        if hv : v ∈ S then none else some (b ⟨v, Finset.mem_compl.mpr hv⟩))
      ?hi ?hj ?hleft ?hright
    case hi =>
      intro ρ _
      exact Finset.mem_univ _
    case hj =>
      intro b _
      rw [mem_starFiber]
      ext v
      rw [mem_starSet]
      by_cases hv : v ∈ S
      · simp [hv]
      · simp [hv]
    case hleft =>
      intro ρ hρ
      rw [mem_starFiber] at hρ
      funext v
      by_cases hv : v ∈ S
      · have hnone : ρ v = none := by
          rw [← mem_starSet, hρ]
          exact hv
        simp [hv, hnone]
      · have hsome : ρ v ≠ none := fun hcontra =>
          hv (by rw [← hρ]; exact mem_starSet.mpr hcontra)
        cases hval : ρ v with
        | none => exact absurd hval hsome
        | some b => simp [hv, hval]
    case hright =>
      intro b _
      funext v
      have hv : v.1 ∉ S := Finset.mem_compl.mp v.2
      simp [hv]
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

/-- **Closed-form cardinality of the restriction space.**  There are exactly
`C(n, ℓ) * 2 ^ (n - ℓ)` restrictions with `ℓ` stars: choose the star set, then
fix the rest freely. -/
theorem restrictionsWithStars_card (n ℓ : Nat) :
    (restrictionsWithStars n ℓ).card = n.choose ℓ * 2 ^ (n - ℓ) := by
  classical
  have hfiber : ∀ ρ ∈ restrictionsWithStars n ℓ,
      starSet ρ ∈ Finset.univ.powersetCard ℓ := by
    intro ρ hρ
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [restrictionsWithStars, Finset.mem_filter] at hρ
    rw [← stars_eq_starSet_card]
    exact hρ.2
  rw [Finset.card_eq_sum_card_fiberwise hfiber]
  have hconst : ∀ S ∈ Finset.univ.powersetCard ℓ,
      ((restrictionsWithStars n ℓ).filter (fun ρ => starSet ρ = S)).card =
        2 ^ (n - ℓ) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hfe : (restrictionsWithStars n ℓ).filter (fun ρ => starSet ρ = S) =
        starFiber S := by
      ext ρ
      rw [Finset.mem_filter, starFiber, Finset.mem_filter,
        restrictionsWithStars, Finset.mem_filter]
      constructor
      · rintro ⟨⟨_, _⟩, hset⟩
        exact ⟨Finset.mem_univ _, hset⟩
      · rintro ⟨_, hset⟩
        refine ⟨⟨Finset.mem_univ _, ?_⟩, hset⟩
        rw [stars_eq_starSet_card, hset]
        exact hS.2
    rw [hfe, starFiber_card, hS.2]
  rw [Finset.sum_const_nat hconst, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

end RestrictionSpaceCard
end PvNP
