/-
# Injection cardinality backbone for the switching lemma assembly

The switching lemma's counting bound has the shape
`|badSet| ≤ |restrictionsWithStars (ℓ-s)| · (C·w)^s`.
Once the Razborov `encode` is shown injective on `badSet`, mapping each bad
restriction to a pair `(σ, code)` with `σ` in the smaller-star set and
`code` in a finite `Code` type of cardinality `(C·w)^s`, the bound follows from
the abstract fact below: an injection `S ↪ T × γ` (with first coordinate landing
in `T`) gives `|S| ≤ |T| · |γ|`.

This is a pure, reusable `Finset` cardinality lemma — INFRASTRUCTURE for the
switching-lemma assembly, NOT the switching lemma, NOT a lower bound, NOT P≠NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import PvNP.SwitchingLemmaStatement

namespace PvNP
namespace SwitchingCardLemma

open Finset

/-- **Injection cardinality bound.** If `f` maps `S` injectively into `β × γ`
with every first coordinate landing in a finite set `T` (and `γ` finite), then
`|S| ≤ |T| · |γ|`.  This is the backbone of the switching-lemma counting step:
take `f = encode`, `T = restrictionsWithStars n (ℓ-s)`, `γ = Code w s`. -/
theorem card_le_mul_of_injOn {α β γ : Type*} [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (S : Finset α) (T : Finset β) (f : α → β × γ)
    (hmem : ∀ a ∈ S, (f a).1 ∈ T)
    (hinj : Set.InjOn f S) :
    S.card ≤ T.card * Fintype.card γ := by
  have h1 : ∀ a ∈ S, f a ∈ T ×ˢ (Finset.univ : Finset γ) := by
    intro a ha
    rw [Finset.mem_product]
    exact ⟨hmem a ha, Finset.mem_univ _⟩
  have h2 : S.card ≤ (T ×ˢ (Finset.univ : Finset γ)).card :=
    Finset.card_le_card_of_injOn f h1 hinj
  rwa [Finset.card_product, Finset.card_univ] at h2

/-- Specialization to the switching-lemma code type `Code w s := Fin s → Fin w × Bool`,
whose cardinality is `(2·w)^s`.  An injection `badSet ↪ T × (Fin s → Fin w × Bool)`
with first coordinate in `T` gives `|badSet| ≤ |T| · (2·w)^s ≤ |T| · (8·w)^s`. -/
theorem card_le_mul_pow_of_injOn {α β : Type*} [DecidableEq β]
    (S : Finset α) (T : Finset β) (w s : Nat)
    (f : α → β × (Fin s → Fin w × Bool))
    (hmem : ∀ a ∈ S, (f a).1 ∈ T)
    (hinj : Set.InjOn f S) :
    S.card ≤ T.card * (2 * w) ^ s := by
  have hcard : Fintype.card (Fin s → Fin w × Bool) = (2 * w) ^ s := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm w 2]
  have h := card_le_mul_of_injOn S T f hmem hinj
  rwa [hcard] at h

end SwitchingCardLemma
end PvNP
