import PvNP.RestrictionComposition

/-!
# Refinement subspaces of the star space (renormalized-counting prerequisite)

`RefinesWith base ρ` — `ρ` extends every fixing of `base` exactly.  The
refinement subspace `refinesSubspace base ℓ` (the `ℓ`-star restrictions
refining `base`) is a sub-family of `consistentSubspace base ℓ` that is in
bijection with the `ℓ`-star restrictions over the `stars base`-variable free
subcube, so its cardinality has the closed form
`C(stars base, ℓ) * 2 ^ (stars base - ℓ)`.

This is the denominator side of the free-subcube renormalized counting that
the satisfiability-gap disclosure on Gate B/B4 identified as the open
ingredient.  This module is counting bookkeeping only.

## HONEST SCOPE STATEMENT (read this)

* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size bound, NOT
  an NP/circuit bound, NOT a statement about P vs NP.  Gate A rung 4 remains
  open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RefinedSubspace

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingLemmaStatement
open RestrictionComposition

/-! ## Refinement -/

/-- `ρ` refines `base`: every variable `base` fixes is fixed to the same value
by `ρ` (`ρ` may additionally fix variables `base` leaves free). -/
def RefinesWith {n : Nat} (base ρ : Restriction n) : Prop :=
  ∀ v b, base v = some b → ρ v = some b

theorem RefinesWith.consistentWith {n : Nat} {base ρ : Restriction n}
    (h : RefinesWith base ρ) : ConsistentWith base ρ := by
  intro v b₀ b₁ h₀ h₁
  rw [h v b₀ h₀] at h₁
  exact (Option.some.inj h₁).symm

theorem refinesWith_freeRestriction {n : Nat} (ρ : Restriction n) :
    RefinesWith (freeRestriction n) ρ := by
  intro v b h
  simp [freeRestriction] at h

/-- A refinement absorbs the base under first-wins composition. -/
theorem compose_eq_of_refinesWith {n : Nat} {base ρ : Restriction n}
    (h : RefinesWith base ρ) : compose base ρ = ρ := by
  funext v
  cases hb : base v with
  | none => rw [compose_free_left base ρ v hb]
  | some b => rw [compose_fixed_left base ρ v b hb, h v b hb]

/-- Stars of a refinement lie inside the base's star set. -/
theorem starSet_subset_of_refinesWith {n : Nat} {base ρ : Restriction n}
    (h : RefinesWith base ρ) : starSet ρ ⊆ starSet base := by
  intro v hv
  rw [mem_starSet] at hv ⊢
  cases hb : base v with
  | none => rfl
  | some b => rw [h v b hb] at hv; cases hv

/-! ## The refinement subspace -/

open Classical in
/-- The `ℓ`-star restrictions refining `base`. -/
noncomputable def refinesSubspace {n : Nat} (base : Restriction n) (ℓ : Nat) :
    Finset (Restriction n) :=
  (restrictionsWithStars n ℓ).filter (fun ρ => RefinesWith base ρ)

theorem mem_refinesSubspace {n : Nat} {base : Restriction n} {ℓ : Nat}
    {ρ : Restriction n} :
    ρ ∈ refinesSubspace base ℓ ↔
      ρ ∈ restrictionsWithStars n ℓ ∧ RefinesWith base ρ := by
  classical
  simp [refinesSubspace]

theorem refinesSubspace_subset_consistent {n : Nat} (base : Restriction n)
    (ℓ : Nat) : refinesSubspace base ℓ ⊆ consistentSubspace base ℓ := by
  classical
  intro ρ hρ
  rw [mem_refinesSubspace] at hρ
  rw [mem_consistentSubspace]
  exact ⟨hρ.1, hρ.2.consistentWith⟩

theorem refinesSubspace_freeRestriction (n ℓ : Nat) :
    refinesSubspace (freeRestriction n) ℓ = restrictionsWithStars n ℓ := by
  classical
  apply Finset.filter_true_of_mem
  intro ρ _
  exact refinesWith_freeRestriction ρ

/-- The refinement subspace is empty above the base's free capacity. -/
theorem refinesSubspace_eq_empty_of_lt {n : Nat} {base : Restriction n}
    {ℓ : Nat} (h : stars base < ℓ) : refinesSubspace base ℓ = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro ρ hρ
  rw [mem_refinesSubspace, mem_restrictionsWithStars] at hρ
  have hsub := starSet_subset_of_refinesWith hρ.2
  have hle : stars ρ ≤ stars base := by
    rw [stars_eq_starSet_card, stars_eq_starSet_card]
    exact Finset.card_le_card hsub
  rw [hρ.1] at hle
  omega

/-! ## The free-subcube enumeration -/

/-- Enumerate the base's free variables by `Fin (stars base)`. -/
noncomputable def freeEquiv {n : Nat} (base : Restriction n) :
    {v : Fin n // v ∈ starSet base} ≃ Fin (stars base) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, stars_eq_starSet_card])

/-- The embedding of the free subcube's coordinates into `Fin n`. -/
noncomputable def freeEmbed {n : Nat} (base : Restriction n)
    (i : Fin (stars base)) : Fin n :=
  ((freeEquiv base).symm i).1

theorem freeEmbed_mem {n : Nat} (base : Restriction n) (i : Fin (stars base)) :
    freeEmbed base i ∈ starSet base :=
  ((freeEquiv base).symm i).2

theorem freeEmbed_injective {n : Nat} (base : Restriction n) :
    Function.Injective (freeEmbed base) := by
  intro i j hij
  have h : (freeEquiv base).symm i = (freeEquiv base).symm j :=
    Subtype.ext hij
  exact (freeEquiv base).symm.injective h

theorem freeEmbed_freeEquiv {n : Nat} (base : Restriction n) (v : Fin n)
    (hv : v ∈ starSet base) : freeEmbed base (freeEquiv base ⟨v, hv⟩) = v := by
  show ((freeEquiv base).symm (freeEquiv base ⟨v, hv⟩)).1 = v
  rw [Equiv.symm_apply_apply]

theorem freeEquiv_freeEmbed {n : Nat} (base : Restriction n)
    (i : Fin (stars base)) :
    freeEquiv base ⟨freeEmbed base i, freeEmbed_mem base i⟩ = i := by
  show freeEquiv base ((freeEquiv base).symm i) = i
  exact (freeEquiv base).apply_symm_apply i

/-! ## Transport between the refinement subspace and the free subcube -/

/-- Push a refinement down to the free subcube. -/
noncomputable def downRestriction {n : Nat} (base : Restriction n)
    (ρ : Restriction n) : Restriction (stars base) :=
  fun i => ρ (freeEmbed base i)

open Classical in
/-- Lift a free-subcube restriction to a refinement of `base`. -/
noncomputable def upRestriction {n : Nat} (base : Restriction n)
    (σ : Restriction (stars base)) : Restriction n :=
  fun v => if hv : v ∈ starSet base then σ (freeEquiv base ⟨v, hv⟩) else base v

theorem upRestriction_refines {n : Nat} (base : Restriction n)
    (σ : Restriction (stars base)) : RefinesWith base (upRestriction base σ) := by
  intro v b hb
  have hv : v ∉ starSet base := by
    rw [mem_starSet, hb]
    simp
  simp [upRestriction, hv, hb]

theorem upRestriction_free_apply {n : Nat} (base : Restriction n)
    (σ : Restriction (stars base)) (v : Fin n) (hv : v ∈ starSet base) :
    upRestriction base σ v = σ (freeEquiv base ⟨v, hv⟩) := by
  simp [upRestriction, hv]

theorem downRestriction_upRestriction {n : Nat} (base : Restriction n)
    (σ : Restriction (stars base)) :
    downRestriction base (upRestriction base σ) = σ := by
  funext i
  rw [downRestriction,
    upRestriction_free_apply base σ (freeEmbed base i) (freeEmbed_mem base i),
    freeEquiv_freeEmbed]

theorem upRestriction_downRestriction {n : Nat} {base : Restriction n}
    {ρ : Restriction n} (h : RefinesWith base ρ) :
    upRestriction base (downRestriction base ρ) = ρ := by
  funext v
  by_cases hv : v ∈ starSet base
  · rw [upRestriction_free_apply base _ v hv, downRestriction,
      freeEmbed_freeEquiv base v hv]
  · have hb : ∃ b, base v = some b := by
      rw [mem_starSet] at hv
      cases hbase : base v with
      | none => exact absurd hbase hv
      | some b => exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hb
    simp [upRestriction, hv, hb, h v b hb]

/-- Star sets transport: the stars of `down ρ` enumerate the stars of `ρ`. -/
theorem starSet_downRestriction {n : Nat} {base : Restriction n}
    {ρ : Restriction n} (h : RefinesWith base ρ) :
    starSet (downRestriction base ρ) =
      (starSet ρ).attach.image
        (fun v => freeEquiv base
          ⟨v.1, starSet_subset_of_refinesWith h v.2⟩) := by
  classical
  ext i
  rw [mem_starSet]
  constructor
  · intro hi
    have hmem : freeEmbed base i ∈ starSet ρ := by
      rw [mem_starSet]
      exact hi
    refine Finset.mem_image.mpr ⟨⟨freeEmbed base i, hmem⟩, Finset.mem_attach _ _, ?_⟩
    have : (⟨freeEmbed base i,
        starSet_subset_of_refinesWith h hmem⟩ :
          {v : Fin n // v ∈ starSet base}) =
        ⟨freeEmbed base i, freeEmbed_mem base i⟩ := rfl
    rw [this, freeEquiv_freeEmbed]
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨v, _, rfl⟩
    show ρ (freeEmbed base _) = none
    rw [freeEmbed_freeEquiv base v.1 (starSet_subset_of_refinesWith h v.2)]
    exact mem_starSet.mp v.2

theorem stars_downRestriction {n : Nat} {base : Restriction n}
    {ρ : Restriction n} (h : RefinesWith base ρ) :
    stars (downRestriction base ρ) = stars ρ := by
  classical
  calc stars (downRestriction base ρ)
      = (starSet (downRestriction base ρ)).card := stars_eq_starSet_card _
    _ = ((starSet ρ).attach.image
          (fun v => freeEquiv base
            ⟨v.1, starSet_subset_of_refinesWith h v.2⟩)).card := by
        rw [starSet_downRestriction h]
    _ = (starSet ρ).attach.card := Finset.card_image_of_injective _ (by
        intro a b hab
        have h1 : a.1 = b.1 := by
          have := congrArg (fun x => ((freeEquiv base).symm x).1) hab
          simpa [Equiv.symm_apply_apply] using this
        exact Subtype.ext h1)
    _ = (starSet ρ).card := Finset.card_attach
    _ = stars ρ := (stars_eq_starSet_card ρ).symm

/-- Star sets transport upward as well. -/
theorem stars_upRestriction {n : Nat} (base : Restriction n)
    (σ : Restriction (stars base)) :
    stars (upRestriction base σ) = stars σ := by
  have h := stars_downRestriction (upRestriction_refines base σ)
  rw [downRestriction_upRestriction] at h
  exact h.symm

/-! ## Closed-form cardinality of the refinement subspace -/

/-- **Refinement-subspace cardinality (closed form).**  The `ℓ`-star
refinements of `base` are in bijection with the `ℓ`-star restrictions of the
`stars base`-variable free subcube:
`|refinesSubspace base ℓ| = C(stars base, ℓ) * 2 ^ (stars base - ℓ)`. -/
theorem refinesSubspace_card {n : Nat} (base : Restriction n) (ℓ : Nat) :
    (refinesSubspace base ℓ).card =
      (stars base).choose ℓ * 2 ^ (stars base - ℓ) := by
  classical
  have hbij : (refinesSubspace base ℓ).card =
      (restrictionsWithStars (stars base) ℓ).card := by
    refine Finset.card_bij'
      (fun ρ _ => downRestriction base ρ)
      (fun σ _ => upRestriction base σ)
      ?hi ?hj ?hleft ?hright
    case hi =>
      intro ρ hρ
      rw [mem_refinesSubspace, mem_restrictionsWithStars] at hρ
      rw [mem_restrictionsWithStars]
      rw [stars_downRestriction hρ.2]
      exact hρ.1
    case hj =>
      intro σ hσ
      rw [mem_restrictionsWithStars] at hσ
      rw [mem_refinesSubspace, mem_restrictionsWithStars]
      exact ⟨by rw [stars_upRestriction base σ]; exact hσ,
        upRestriction_refines base σ⟩
    case hleft =>
      intro ρ hρ
      rw [mem_refinesSubspace] at hρ
      exact upRestriction_downRestriction hρ.2
    case hright =>
      intro σ _
      exact downRestriction_upRestriction base σ
  rw [hbij, restrictionsWithStars_card]

/-- The refinement subspace is nonempty for `ℓ ≤ stars base`. -/
theorem refinesSubspace_nonempty {n : Nat} (base : Restriction n) {ℓ : Nat}
    (hℓ : ℓ ≤ stars base) : (refinesSubspace base ℓ).Nonempty := by
  classical
  rw [← Finset.card_pos, refinesSubspace_card]
  have hchoose : 0 < (stars base).choose ℓ := Nat.choose_pos hℓ
  have hpow : 0 < 2 ^ (stars base - ℓ) := Nat.pos_pow_of_pos _ (by omega)
  exact Nat.mul_pos hchoose hpow

end RefinedSubspace
end PvNP
