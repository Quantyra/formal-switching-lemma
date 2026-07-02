import PvNP.GeneratedGoodRestriction

/-!
# Gate B / B4 prerequisites: restriction composition and consistent-subspace counting

This module supplies the restriction-sequence ingredients that the final
generated iterated-collapse theorem consumes:

* `compose` — first-wins overlay of two partial restrictions, with the exact
  algebra lemma `restrict_compose` (`restrict (compose ρ₀ ρ₁) F =
  restrict ρ₁ (restrict ρ₀ F)`);
* `ConsistentWith` — no conflicting fixings, which is exactly what makes
  agreement transfer through a composition (`agree_compose_right`);
* `consistentSubspace` — the sub-Finset of the `ℓ`-star space consistent with a
  base restriction, with nonemptiness for `ℓ ≤ n` and the exact identity
  `consistentSubspace (freeRestriction n) ℓ = restrictionsWithStars n ℓ`;
* `goodRestriction_exists_of_subspace` / `simultaneousCollapse_exists_consistent`
  — the B1/B2 counting beat strengthened to any target sub-Finset: whenever the
  union bound beats the CONSISTENT subspace size, one restriction exists that is
  simultaneously good for every listed gate AND consistent with the base;
* `restrictionsWithStars_card` — the closed-form cardinality
  `|restrictionsWithStars n ℓ| = C(n, ℓ) * 2 ^ (n - ℓ)` (the recorded
  restriction-space cardinality prerequisite).

## HONEST SCOPE STATEMENT (read this)

* Formula-collapse infrastructure only: counting-form corollaries of the PROVED
  SimpleDNF switching lemma plus exact `Finset.card` counting.  No probability
  measure is introduced.
* NOT a Frege/PHP proof-size bound, NOT an NP/circuit bound, NOT a statement
  about P vs NP.  Gate A rung 4 remains open.
* The closed form is proved for the FULL `ℓ`-star space.  No closed form is
  claimed here for `consistentSubspace` cardinalities beyond nonemptiness and
  the free-base identity; iterated-collapse beat hypotheses against consistent
  subspaces are supplied by callers.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace RestrictionComposition

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement

/-! ## First-wins composition of restrictions -/

/-- First-wins overlay: every variable fixed by `ρ₀` keeps `ρ₀`'s value; the
variables `ρ₀` leaves free defer to `ρ₁`. -/
def compose {n : Nat} (ρ₀ ρ₁ : Restriction n) : Restriction n :=
  fun v =>
    match ρ₀ v with
    | some b => some b
    | none => ρ₁ v

theorem compose_fixed_left {n : Nat} (ρ₀ ρ₁ : Restriction n) (v : Fin n)
    (b : Bool) (h : ρ₀ v = some b) : compose ρ₀ ρ₁ v = some b := by
  unfold compose
  rw [h]

theorem compose_free_left {n : Nat} (ρ₀ ρ₁ : Restriction n) (v : Fin n)
    (h : ρ₀ v = none) : compose ρ₀ ρ₁ v = ρ₁ v := by
  unfold compose
  rw [h]

theorem compose_freeRestriction {n : Nat} (ρ : Restriction n) :
    compose (freeRestriction n) ρ = ρ := by
  funext v
  rfl

/-- Any assignment agreeing with a composition agrees with the first component
(the first component's fixings survive the overlay verbatim). -/
theorem agree_compose_left {n : Nat} {ρ₀ ρ₁ : Restriction n} {a : Assignment n}
    (h : Agree (compose ρ₀ ρ₁) a) : Agree ρ₀ a := by
  intro v b hv
  exact h v b (compose_fixed_left ρ₀ ρ₁ v b hv)

/-! ## Consistency between restrictions -/

/-- `ρ₁` is consistent with `ρ₀` when they never fix the same variable to
different values.  (Either may leave any variable free.) -/
def ConsistentWith {n : Nat} (ρ₀ ρ₁ : Restriction n) : Prop :=
  ∀ v b₀ b₁, ρ₀ v = some b₀ → ρ₁ v = some b₁ → b₁ = b₀

theorem consistentWith_freeRestriction {n : Nat} (ρ : Restriction n) :
    ConsistentWith (freeRestriction n) ρ := by
  intro v b₀ _ h₀ _
  simp [freeRestriction] at h₀

/-- Agreement transfers to the SECOND component of a composition exactly when
the components are consistent: wherever `ρ₀` overrode `ρ₁`, the values coincide
anyway. -/
theorem agree_compose_right {n : Nat} {ρ₀ ρ₁ : Restriction n}
    (hcons : ConsistentWith ρ₀ ρ₁) {a : Assignment n}
    (h : Agree (compose ρ₀ ρ₁) a) : Agree ρ₁ a := by
  intro v b hv
  cases h₀ : ρ₀ v with
  | none =>
      apply h v b
      rw [compose_free_left ρ₀ ρ₁ v h₀]
      exact hv
  | some b₀ =>
      have hb : b = b₀ := hcons v b₀ b h₀ hv
      subst hb
      exact h v b (compose_fixed_left ρ₀ ρ₁ v b h₀)

/-! ## Composition commutes with iterated restriction -/

/-- **The composition algebra lemma.**  Restricting by the first-wins overlay is
exactly restricting by `ρ₀` and then by `ρ₁`. -/
theorem restrict_compose {n : Nat} (ρ₀ ρ₁ : Restriction n) (F : BDFormula n) :
    restrict (compose ρ₀ ρ₁) F = restrict ρ₁ (restrict ρ₀ F) := by
  induction F using BDFormula.recAux with
  | htru => rw [restrict_tru, restrict_tru, restrict_tru]
  | hfls => rw [restrict_fls, restrict_fls, restrict_fls]
  | hlit l =>
      simp only [restrict]
      cases h₀ : ρ₀ l.var with
      | some b =>
          rw [compose_fixed_left ρ₀ ρ₁ l.var b h₀]
          cases hbs : (b == l.sign) <;> simp [hbs, restrict_tru, restrict_fls]
      | none =>
          rw [compose_free_left ρ₀ ρ₁ l.var h₀]
          simp only [restrict]
  | hand l ih =>
      rw [restrict_and, restrict_and, restrict_and, List.map_map]
      congr 1
      apply List.map_congr_left
      intro f hf
      exact ih f hf
  | hor l ih =>
      rw [restrict_or, restrict_or, restrict_or, List.map_map]
      congr 1
      apply List.map_congr_left
      intro f hf
      exact ih f hf

/-! ## Consistent subspaces of the star space -/

open Classical in
/-- The sub-Finset of the `ℓ`-star restrictions that are consistent with a base
restriction `ρ₀`. -/
noncomputable def consistentSubspace {n : Nat} (ρ₀ : Restriction n) (ℓ : Nat) :
    Finset (Restriction n) :=
  (restrictionsWithStars n ℓ).filter (fun ρ => ConsistentWith ρ₀ ρ)

theorem mem_consistentSubspace {n : Nat} {ρ₀ : Restriction n} {ℓ : Nat}
    {ρ : Restriction n} :
    ρ ∈ consistentSubspace ρ₀ ℓ ↔
      ρ ∈ restrictionsWithStars n ℓ ∧ ConsistentWith ρ₀ ρ := by
  classical
  simp [consistentSubspace]

theorem consistentSubspace_subset {n : Nat} (ρ₀ : Restriction n) (ℓ : Nat) :
    consistentSubspace ρ₀ ℓ ⊆ restrictionsWithStars n ℓ := by
  classical
  exact Finset.filter_subset _ _

/-- Against the free base, consistency is no constraint at all: the consistent
subspace IS the full `ℓ`-star space, so the B4 stage hypotheses generalize the
B3 full-space beat hypothesis exactly. -/
theorem consistentSubspace_freeRestriction (n ℓ : Nat) :
    consistentSubspace (freeRestriction n) ℓ = restrictionsWithStars n ℓ := by
  classical
  apply Finset.filter_true_of_mem
  intro ρ _
  exact consistentWith_freeRestriction ρ

/-- The threshold restriction: the first `ℓ` variables starred, the rest fixed
by a supplied value function. -/
def thresholdRestriction (n ℓ : Nat) (g : Fin n → Bool) : Restriction n :=
  fun v => if v.val < ℓ then none else some (g v)

theorem thresholdRestriction_mem {n ℓ : Nat} (hℓ : ℓ ≤ n) (g : Fin n → Bool) :
    thresholdRestriction n ℓ g ∈ restrictionsWithStars n ℓ := by
  classical
  rw [restrictionsWithStars, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [stars]
  have hset : (Finset.univ.filter
      (fun v : Fin n => thresholdRestriction n ℓ g v = none)) =
      Finset.univ.filter (fun v : Fin n => v.val < ℓ) := by
    apply Finset.filter_congr
    intro v _
    by_cases hv : v.val < ℓ
    · simp [thresholdRestriction, hv]
    · simp [thresholdRestriction, hv]
  rw [hset]
  have hsub : (Finset.univ.filter (fun v : Fin n => v.val < ℓ)).card =
      Fintype.card {v : Fin n // v.val < ℓ} :=
    (Fintype.card_subtype (fun v : Fin n => v.val < ℓ)).symm
  have hequiv : {v : Fin n // v.val < ℓ} ≃ Fin ℓ :=
    { toFun := fun v => ⟨v.1.val, v.2⟩
      invFun := fun m => ⟨⟨m.val, Nat.lt_of_lt_of_le m.isLt hℓ⟩, m.isLt⟩
      left_inv := fun v => rfl
      right_inv := fun m => rfl }
  rw [hsub, Fintype.card_congr hequiv, Fintype.card_fin]

/-- Consistent subspaces are nonempty whenever `ℓ ≤ n`: star the first `ℓ`
variables and copy the base's fixings (defaulting free ones) elsewhere. -/
theorem consistentSubspace_nonempty {n : Nat} (ρ₀ : Restriction n) {ℓ : Nat}
    (hℓ : ℓ ≤ n) : (consistentSubspace ρ₀ ℓ).Nonempty := by
  refine ⟨thresholdRestriction n ℓ (fun v => (ρ₀ v).getD false), ?_⟩
  rw [mem_consistentSubspace]
  refine ⟨thresholdRestriction_mem hℓ _, ?_⟩
  intro v b₀ b₁ h₀ h₁
  by_cases hv : v.val < ℓ
  · simp [thresholdRestriction, hv] at h₁
  · simp [thresholdRestriction, hv, h₀] at h₁
    exact h₁.symm

/-! ## Counting generates good restrictions inside any large enough subspace -/

/-- **Subspace counting beat.**  If strictly fewer restrictions are jointly bad
than the size of ANY target Finset `T`, then `T` contains a restriction good for
every listed gate.  (Instantiated below with consistent subspaces.) -/
theorem goodRestriction_exists_of_subspace {n : Nat} (gates : List (GateSpec n))
    (s ℓ : Nat) (T : Finset (Restriction n))
    (hcard : (jointBadSet gates s ℓ).card < T.card) :
    ∃ ρ ∈ T, ∀ g ∈ gates, ρ ∉ badSetTerm g.theDNF s ℓ := by
  classical
  have hsdiff : 0 < (T \ jointBadSet gates s ℓ).card := by
    have hle := Finset.le_card_sdiff (jointBadSet gates s ℓ) T
    omega
  obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp hsdiff
  rw [Finset.mem_sdiff] at hρ
  refine ⟨ρ, hρ.1, ?_⟩
  intro g hg hbad
  exact hρ.2 (mem_jointBadSet.mpr ⟨g, hg, hbad⟩)

/-- **B4 stage keystone: consistent simultaneous collapse by counting.**  When
the union bound beats the size of the subspace consistent with a base
restriction, ONE restriction exists that lies in the `ℓ`-star space, is
consistent with the base, and collapses EVERY listed gate to a decision tree of
depth `< s`.  No restriction is supplied; the counting generates it inside the
consistent subspace. -/
theorem simultaneousCollapse_exists_consistent {n : Nat} (ρ₀ : Restriction n)
    (gates : List (GateSpec n)) (w s ℓ : Nat)
    (hwidth : ∀ g ∈ gates, widthDNF g.theDNF ≤ w)
    (hbeat : gates.length *
        ((restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s) <
      (consistentSubspace ρ₀ ℓ).card) :
    ∃ ρ ∈ restrictionsWithStars n ℓ, ConsistentWith ρ₀ ρ ∧
      ∀ g ∈ gates, ∃ T : DTree n, dtDepth T < s ∧
        ∀ a : Assignment n, Agree ρ a →
          dtEval a T = eval a (restrict ρ g.formula) := by
  have hcard : (jointBadSet gates s ℓ).card < (consistentSubspace ρ₀ ℓ).card :=
    Nat.lt_of_le_of_lt (jointBadSet_card_le gates w s ℓ hwidth) hbeat
  obtain ⟨ρ, hρmem, hgood⟩ :=
    goodRestriction_exists_of_subspace gates s ℓ (consistentSubspace ρ₀ ℓ) hcard
  rw [mem_consistentSubspace] at hρmem
  exact ⟨ρ, hρmem.1, hρmem.2, fun g hg =>
    gate_collapse g w s ℓ (hwidth g hg) ρ hρmem.1 (hgood g hg)⟩

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

/-- **Closed-form cardinality of the restriction space (B4 prerequisite).**
There are exactly `C(n, ℓ) * 2 ^ (n - ℓ)` restrictions with `ℓ` stars: choose
the star set, then fix the rest freely. -/
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

end RestrictionComposition
end PvNP
