import PvNP.RestrictionComposition
import PvNP.RestrictedPHPFloor

/-!
# GA-1: matching composition algebra (S2185)

First formal rung of the Gate A rung-4 reopening arc (S2184 packet, GA-1).
Mirror: `RestrictionComposition.lean`. The design is mirror-faithful to the
boolean lane: the object of composition is a **raw** matching map with no
invariant (`MatchingMap p h := Fin p → Option (Fin h)`), composition is
total first-wins on pigeons, and all content lives in lemmas:

* `compose` is unconditionally associative with the empty matching as a
  two-sided unit;
* `IsMatching` (hole-injectivity on the defined part) transfers to a
  composite under `CrossConsistent` (the second map assigns no used hole to
  a free pigeon) — the only channel by which first-wins can break
  hole-injectivity;
* `MatchingConsistentWith` mirrors the boolean `ConsistentWith` (agreement
  on the common pigeon domain), with empty-matching, compose-right, and
  `DisjointExtension` transfer lemmas;
* `toRestriction` maps a raw matching map to a boolean restriction on the
  `phpVar` variable rectangle (pigeon channel wins; a used hole silences
  the other pigeons' variables on that hole);
* the `restrict_compose` analogue — `toRestriction (compose mu0 mu1) =
  RestrictionComposition.compose (toRestriction mu0) (toRestriction mu1)` —
  holds under `DisjointExtension mu0 mu1` (the extension is silent on fixed
  pigeons AND hole-disjoint), and **machine-checked counterexamples** pin
  that BOTH disjointness channels are necessary; in particular the second
  counterexample is `CrossConsistent`, so cross-consistency alone cannot
  support the homomorphism;
* free-pigeon (star) counting: composition with an extension fixing `s`
  previously-free pigeons drops the free count by exactly `s`.

Signatures are rectangular-ready throughout (pigeons `p` and holes `h` are
separate parameters); the witnesses exercise a square and a rectangular
instance, each with a genuinely partial matching (0 < fixed < p).

Matching-side composition bookkeeping only. This is not a PHP switching
lemma, not a bad-set bound, not the extension encode (GA-3), not Gate A
closure, not a Frege/PHP or NP/circuit lower bound, and not P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingComposition

open BoundedDepthFrege
open BoundedDepthRestriction
open RestrictedPHPFloor

/-! ## Raw matching maps and first-wins composition -/

/-- Raw partial-matching map: each pigeon is unassigned or names a hole.
No invariant — mirroring `Restriction n = Fin n → Option Bool`. -/
def MatchingMap (p h : Nat) : Type :=
  Fin p → Option (Fin h)

/-- The empty matching: every pigeon free. -/
def emptyMatching (p h : Nat) : MatchingMap p h :=
  fun _ => none

/-- First-wins overlay on pigeons: the first map's assignments survive;
pigeons it leaves free defer to the second map. Mirrors
`RestrictionComposition.compose`. -/
def compose {p h : Nat} (mu0 mu1 : MatchingMap p h) : MatchingMap p h :=
  fun i =>
    match mu0 i with
    | some a => some a
    | none => mu1 i

theorem compose_fixed_left {p h : Nat} (mu0 mu1 : MatchingMap p h) (i : Fin p)
    (a : Fin h) (hi : mu0 i = some a) : compose mu0 mu1 i = some a := by
  unfold compose
  rw [hi]

theorem compose_free_left {p h : Nat} (mu0 mu1 : MatchingMap p h) (i : Fin p)
    (hi : mu0 i = none) : compose mu0 mu1 i = mu1 i := by
  unfold compose
  rw [hi]

/-- The empty matching is a left unit. -/
theorem compose_empty_left {p h : Nat} (mu : MatchingMap p h) :
    compose (emptyMatching p h) mu = mu := by
  funext i
  rfl

/-- The empty matching is a right unit. -/
theorem compose_empty_right {p h : Nat} (mu : MatchingMap p h) :
    compose mu (emptyMatching p h) = mu := by
  funext i
  unfold compose emptyMatching
  cases mu i <;> rfl

/-- First-wins composition is unconditionally associative on raw maps. -/
theorem compose_assoc {p h : Nat} (mu0 mu1 mu2 : MatchingMap p h) :
    compose (compose mu0 mu1) mu2 = compose mu0 (compose mu1 mu2) := by
  funext i
  unfold compose
  cases mu0 i <;> rfl

/-! ## Matching property and consistency -/

/-- Hole-injectivity on the defined part: no two pigeons share a hole. -/
def IsMatching {p h : Nat} (mu : MatchingMap p h) : Prop :=
  ∀ i j a, mu i = some a → mu j = some a → i = j

theorem isMatching_empty (p h : Nat) : IsMatching (emptyMatching p h) := by
  intro i j a hi
  cases hi

/-- Cross-consistency: the second map assigns no first-map-used hole to a
first-map-free pigeon — the only channel by which first-wins can break
hole-injectivity. -/
def CrossConsistent {p h : Nat} (mu0 mu1 : MatchingMap p h) : Prop :=
  ∀ i j a, mu0 i = some a → mu0 j = none → mu1 j = some a → False

/-- `IsMatching` transfers to a first-wins composite under cross-consistency. -/
theorem isMatching_compose {p h : Nat} {mu0 mu1 : MatchingMap p h}
    (h0 : IsMatching mu0) (h1 : IsMatching mu1)
    (hc : CrossConsistent mu0 mu1) : IsMatching (compose mu0 mu1) := by
  intro i j a hi hj
  cases hi0 : mu0 i with
  | some b =>
      have hib : compose mu0 mu1 i = some b := compose_fixed_left mu0 mu1 i b hi0
      rw [hi] at hib
      cases hib
      cases hj0 : mu0 j with
      | some c =>
          have hjc : compose mu0 mu1 j = some c := compose_fixed_left mu0 mu1 j c hj0
          rw [hj] at hjc
          cases hjc
          exact h0 i j a hi0 hj0
      | none =>
          have hj1 : mu1 j = some a := by
            have hcf := compose_free_left mu0 mu1 j hj0
            rw [hj] at hcf
            exact hcf.symm
          exact absurd (hc i j a hi0 hj0 hj1) not_false
  | none =>
      have hi1 : mu1 i = some a := by
        have hcf := compose_free_left mu0 mu1 i hi0
        rw [hi] at hcf
        exact hcf.symm
      cases hj0 : mu0 j with
      | some c =>
          have hjc : compose mu0 mu1 j = some c := compose_fixed_left mu0 mu1 j c hj0
          rw [hj] at hjc
          cases hjc
          exact absurd (hc j i a hj0 hi0 hi1) not_false
      | none =>
          have hj1 : mu1 j = some a := by
            have hcf := compose_free_left mu0 mu1 j hj0
            rw [hj] at hcf
            exact hcf.symm
          exact h1 i j a hi1 hj1

/-- Converse direction, making "the only channel" kernel-backed: a
cross-consistency violation always breaks the composite's matching property
(two distinct pigeons land in the violated hole), with no hypotheses on the
parts. -/
theorem not_isMatching_compose_of_not_crossConsistent {p h : Nat}
    {mu0 mu1 : MatchingMap p h} (hnc : ¬ CrossConsistent mu0 mu1) :
    ¬ IsMatching (compose mu0 mu1) := by
  intro hm
  apply hnc
  intro i j a hi hj0 hj1
  have hci : compose mu0 mu1 i = some a := compose_fixed_left mu0 mu1 i a hi
  have hcj : compose mu0 mu1 j = some a := by
    rw [compose_free_left mu0 mu1 j hj0]
    exact hj1
  have hij : i = j := hm i j a hci hcj
  rw [hij, hj0] at hi
  cases hi

/-- Pigeon-level consistency, mirroring the boolean `ConsistentWith`: the two
maps never send the same pigeon to different holes (either may leave any
pigeon free). -/
def MatchingConsistentWith {p h : Nat} (mu0 mu1 : MatchingMap p h) : Prop :=
  ∀ i a b, mu0 i = some a → mu1 i = some b → b = a

theorem matchingConsistentWith_empty {p h : Nat} (mu : MatchingMap p h) :
    MatchingConsistentWith (emptyMatching p h) mu := by
  intro i a b h0
  cases h0

/-- Mirror of `agree_compose_right`'s content at the map level: under
pigeon-level consistency the second component's fixings survive the
first-wins overlay verbatim (wherever the first component overrode the
second, the values coincide anyway). -/
theorem matchingConsistentWith_compose_right {p h : Nat}
    {mu0 mu1 : MatchingMap p h} (hcons : MatchingConsistentWith mu0 mu1)
    (i : Fin p) (a : Fin h) (h1 : mu1 i = some a) :
    compose mu0 mu1 i = some a := by
  cases h0 : mu0 i with
  | some b =>
      have hba : a = b := hcons i b a h0 h1
      rw [compose_fixed_left mu0 mu1 i b h0, hba]
  | none =>
      rw [compose_free_left mu0 mu1 i h0]
      exact h1

/-- Disjoint extension: the extension is silent on fixed pigeons and touches
no used hole. This is the intended GA-3 use case (the planned extension
encode composes pairs onto free pigeons and free holes only) and the exact
hypothesis of the restriction homomorphism below. -/
def DisjointExtension {p h : Nat} (mu0 mu1 : MatchingMap p h) : Prop :=
  (∀ i a, mu0 i = some a → mu1 i = none) ∧
  (∀ i j a, mu0 i = some a → mu1 j ≠ some a)

theorem disjointExtension_crossConsistent {p h : Nat}
    {mu0 mu1 : MatchingMap p h} (hd : DisjointExtension mu0 mu1) :
    CrossConsistent mu0 mu1 :=
  fun i j a hi _ hj => hd.2 i j a hi hj

/-- A disjoint extension is pigeon-level consistent (vacuously: the domains
are disjoint). -/
theorem disjointExtension_matchingConsistentWith {p h : Nat}
    {mu0 mu1 : MatchingMap p h} (hd : DisjointExtension mu0 mu1) :
    MatchingConsistentWith mu0 mu1 := by
  intro i a b h0 h1
  rw [hd.1 i a h0] at h1
  cases h1

/-! ## Free pigeons (stars) -/

/-- The free-pigeon set of a raw matching map. -/
def freePigeons {p h : Nat} (mu : MatchingMap p h) : Finset (Fin p) :=
  Finset.univ.filter (fun i => mu i = none)

theorem mem_freePigeons {p h : Nat} (mu : MatchingMap p h) (i : Fin p) :
    i ∈ freePigeons mu ↔ mu i = none := by
  simp [freePigeons]

/-- A pigeon is free in a composite exactly when it is free in both parts. -/
theorem freePigeons_compose {p h : Nat} (mu0 mu1 : MatchingMap p h) :
    freePigeons (compose mu0 mu1) = freePigeons mu0 ∩ freePigeons mu1 := by
  ext i
  simp only [mem_freePigeons, Finset.mem_inter]
  constructor
  · intro hc
    have h0 : mu0 i = none := by
      cases h0 : mu0 i with
      | some a =>
          rw [compose_fixed_left mu0 mu1 i a h0] at hc
          exact absurd hc (by simp)
      | none => rfl
    refine ⟨h0, ?_⟩
    rw [compose_free_left mu0 mu1 i h0] at hc
    exact hc
  · rintro ⟨h0, h1⟩
    rw [compose_free_left mu0 mu1 i h0]
    exact h1

/-- Star-drop arithmetic: if the extension fixes exactly the pigeons of a set
`T`, all previously free, the composite's free count is the base free count
minus `T.card`. Rectangular signature; this is the star-drop input the
GA-3 rung is planned to consume. -/
theorem freePigeons_compose_card {p h : Nat} (mu0 mu1 : MatchingMap p h)
    (T : Finset (Fin p)) (hT : ∀ i, mu1 i = none ↔ i ∉ T)
    (hTfree : T ⊆ freePigeons mu0) :
    (freePigeons (compose mu0 mu1)).card = (freePigeons mu0).card - T.card := by
  have hset : freePigeons (compose mu0 mu1) = freePigeons mu0 \ T := by
    rw [freePigeons_compose]
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, mem_freePigeons, hT i]
  rw [hset, Finset.card_sdiff hTfree]

/-! ## The boolean-restriction image -/

/-- Whether some pigeon of the map uses hole `a` (decidable Bool form). -/
def holeUsed {p h : Nat} (mu : MatchingMap p h) (a : Fin h) : Bool :=
  (finList p).any (fun i => mu i == some a)

theorem holeUsed_eq_true_iff {p h : Nat} (mu : MatchingMap p h) (a : Fin h) :
    holeUsed mu a = true ↔ ∃ i, mu i = some a := by
  unfold holeUsed
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, _, hbeq⟩
    exact ⟨i, by simpa using hbeq⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, by simpa using hi⟩
    unfold finList
    exact List.mem_pmap.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

/-- The boolean restriction induced by a raw matching map on the `phpVar`
rectangle: the variable "pigeon `i` in hole `a`" is `true` iff the map sends
`i` to `a`, `false` if pigeon `i` is assigned elsewhere or hole `a` is used
while `i` is free, and free otherwise. The pigeon channel wins, so the map
is total on raw maps (well-defined without `IsMatching`). Variables outside
the rectangle (the ambient padding index) stay free. -/
def toRestriction {p h : Nat} (mu : MatchingMap p h) :
    Restriction (Nat.succ (p * h)) :=
  fun v =>
    if hv : v.val < p * h then
      if hh : 0 < h then
        match mu ⟨v.val / h,
            Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hv (Nat.mul_comm p h))⟩ with
        | some b => some (b == (⟨v.val % h, Nat.mod_lt _ hh⟩ : Fin h))
        | none =>
            if holeUsed mu (⟨v.val % h, Nat.mod_lt _ hh⟩ : Fin h) then
              some false
            else none
      else none
    else none

theorem toRestriction_out_of_range {p h : Nat} (mu : MatchingMap p h)
    (v : Fin (Nat.succ (p * h))) (hv : ¬ v.val < p * h) :
    toRestriction mu v = none := by
  unfold toRestriction
  rw [dif_neg hv]

/-- Value of `phpVar` on the real rectangle (the ambient `mod` is inert). -/
theorem phpVar_val {pigeons holes : Nat} (P : Fin pigeons) (H : Fin holes) :
    (phpVar pigeons holes P H).val = P.val * holes + H.val := by
  unfold phpVar
  apply Nat.mod_eq_of_lt
  have hP : P.val + 1 ≤ pigeons := P.isLt
  have hstep : (P.val + 1) * holes ≤ pigeons * holes :=
    Nat.mul_le_mul_right holes hP
  have hexp : (P.val + 1) * holes = P.val * holes + holes := by
    rw [Nat.succ_mul]
  have hH : H.val < holes := H.isLt
  omega

theorem phpVar_val_lt {pigeons holes : Nat} (P : Fin pigeons) (H : Fin holes) :
    (phpVar pigeons holes P H).val < pigeons * holes := by
  rw [phpVar_val]
  have hP : P.val + 1 ≤ pigeons := P.isLt
  have hstep : (P.val + 1) * holes ≤ pigeons * holes :=
    Nat.mul_le_mul_right holes hP
  have hexp : (P.val + 1) * holes = P.val * holes + holes := by
    rw [Nat.succ_mul]
  have hH : H.val < holes := H.isLt
  omega

/-- Evaluation of the induced restriction on a rectangle variable. -/
theorem toRestriction_phpVar {p h : Nat} (mu : MatchingMap p h)
    (P : Fin p) (H : Fin h) :
    toRestriction mu (phpVar p h P H) =
      (match mu P with
        | some b => some (b == H)
        | none => if holeUsed mu H then some false else none) := by
  have hlt : (phpVar p h P H).val < p * h := phpVar_val_lt P H
  have hh : 0 < h := H.pos
  have hdiv : (phpVar p h P H).val / h = P.val := by
    rw [phpVar_val, Nat.add_comm, Nat.add_mul_div_right _ _ hh,
      Nat.div_eq_of_lt H.isLt, Nat.zero_add]
  have hmod : (phpVar p h P H).val % h = H.val := by
    rw [phpVar_val, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt H.isLt]
  unfold toRestriction
  rw [dif_pos hlt, dif_pos hh]
  simp only [hdiv, hmod, Fin.eta]

/-- Hole usage of a first-wins composite is exactly the union of the parts'
usage, under only the silence conjunct of `DisjointExtension` (the extension
never acts on fixed pigeons, so no extension assignment is dropped by
first-wins; the forward inclusions are unconditional). The `ceDom`
counterexample violates precisely this hypothesis. -/
theorem holeUsed_compose {p h : Nat} (mu0 mu1 : MatchingMap p h)
    (hd1 : ∀ i a, mu0 i = some a → mu1 i = none) (a : Fin h) :
    holeUsed (compose mu0 mu1) a = (holeUsed mu0 a || holeUsed mu1 a) := by
  cases hu : (holeUsed mu0 a || holeUsed mu1 a) with
  | true =>
      rw [Bool.or_eq_true] at hu
      apply (holeUsed_eq_true_iff _ _).mpr
      cases hu with
      | inl h0 =>
          rcases (holeUsed_eq_true_iff _ _).mp h0 with ⟨i, hi⟩
          exact ⟨i, compose_fixed_left mu0 mu1 i a hi⟩
      | inr h1 =>
          rcases (holeUsed_eq_true_iff _ _).mp h1 with ⟨i, hi⟩
          cases h0i : mu0 i with
          | some b =>
              rw [hd1 i b h0i] at hi
              cases hi
          | none =>
              refine ⟨i, ?_⟩
              rw [compose_free_left mu0 mu1 i h0i]
              exact hi
  | false =>
      rw [Bool.or_eq_false_iff] at hu
      cases hcu : holeUsed (compose mu0 mu1) a with
      | false => rfl
      | true =>
          exfalso
          rcases (holeUsed_eq_true_iff _ _).mp hcu with ⟨i, hi⟩
          cases h0i : mu0 i with
          | some b =>
              rw [compose_fixed_left mu0 mu1 i b h0i] at hi
              cases hi
              have hused : holeUsed mu0 a = true :=
                (holeUsed_eq_true_iff _ _).mpr ⟨i, h0i⟩
              rw [hu.1] at hused
              cases hused
          | none =>
              rw [compose_free_left mu0 mu1 i h0i] at hi
              have hused : holeUsed mu1 a = true :=
                (holeUsed_eq_true_iff _ _).mpr ⟨i, hi⟩
              rw [hu.2] at hused
              cases hused

/-- Every rectangle variable is a `phpVar` (holes positive). -/
theorem exists_phpVar_of_lt {p h : Nat} (v : Fin (Nat.succ (p * h)))
    (hv : v.val < p * h) (hh : 0 < h) :
    ∃ (P : Fin p) (H : Fin h), v = phpVar p h P H := by
  refine ⟨⟨v.val / h, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hv (Nat.mul_comm p h))⟩,
    ⟨v.val % h, Nat.mod_lt _ hh⟩, ?_⟩
  apply Fin.ext
  rw [phpVar_val]
  have hdm : h * (v.val / h) + v.val % h = v.val := Nat.div_add_mod v.val h
  calc v.val = h * (v.val / h) + v.val % h := hdm.symm
    _ = v.val / h * h + v.val % h := by rw [Nat.mul_comm]

/-- **The `restrict_compose` analogue (GA-1 homomorphism).** Under a disjoint
extension, the induced restriction of a first-wins composite is the boolean
first-wins composition of the induced restrictions, so PHP formula
restriction under matching composition factors through the proved boolean
`RestrictionComposition.restrict_compose`. -/
theorem toRestriction_compose {p h : Nat} (mu0 mu1 : MatchingMap p h)
    (hd : DisjointExtension mu0 mu1) :
    toRestriction (compose mu0 mu1) =
      RestrictionComposition.compose (toRestriction mu0) (toRestriction mu1) := by
  funext v
  unfold RestrictionComposition.compose
  by_cases hv : v.val < p * h
  · by_cases hh : 0 < h
    · obtain ⟨P, H, rfl⟩ := exists_phpVar_of_lt v hv hh
      rw [toRestriction_phpVar, toRestriction_phpVar, toRestriction_phpVar]
      cases h0 : mu0 P with
      | some b =>
          rw [compose_fixed_left mu0 mu1 P b h0]
      | none =>
          rw [compose_free_left mu0 mu1 P h0]
          cases h1 : mu1 P with
          | some c =>
              cases hu0 : holeUsed mu0 H with
              | true =>
                  rcases (holeUsed_eq_true_iff mu0 H).mp hu0 with ⟨j, hj⟩
                  have hne : c ≠ H := by
                    intro hca
                    rw [hca] at h1
                    exact hd.2 j P H hj h1
                  have hbeq : (c == H) = false := by
                    cases hval : (c == H) with
                    | true => exact absurd (by simpa using hval) hne
                    | false => rfl
                  simp [hbeq]
              | false => rfl
          | none =>
              rw [holeUsed_compose mu0 mu1 hd.1 H]
              cases holeUsed mu0 H <;> cases holeUsed mu1 H <;> rfl
    · have h0 : h = 0 := Nat.eq_zero_of_not_pos hh
      subst h0
      exact absurd hv (by simp)
  · rw [toRestriction_out_of_range _ v hv, toRestriction_out_of_range _ v hv,
      toRestriction_out_of_range _ v hv]

/-- Formula-level corollary: restricting a PHP formula by a disjointly
extended composite is restricting by the base and then by the extension —
the matching-side `restrict_compose`, factored through the proved boolean
`RestrictionComposition.restrict_compose`. -/
theorem restrict_toRestriction_compose {p h : Nat} (mu0 mu1 : MatchingMap p h)
    (hd : DisjointExtension mu0 mu1) (F : BDFormula (Nat.succ (p * h))) :
    restrict (toRestriction (compose mu0 mu1)) F =
      restrict (toRestriction mu1) (restrict (toRestriction mu0) F) := by
  rw [toRestriction_compose mu0 mu1 hd]
  exact RestrictionComposition.restrict_compose (toRestriction mu0)
    (toRestriction mu1) F

/-! ## Machine-checked necessity of both disjointness channels -/

/-- Channel-2 counterexample (cross-hole collision, domains disjoint):
`p = 2, h = 1`, first map `{0 ↦ h0}`, extension `{1 ↦ h0}`. The composite
assigns pigeon 1 to the already-used hole, so the matching side reports
`true` at variable `x_{1,0}` while the boolean side has silenced it. -/
def ceHoleFst : MatchingMap 2 1 :=
  fun i => if i = (⟨0, by decide⟩ : Fin 2) then some ⟨0, by decide⟩ else none

def ceHoleSnd : MatchingMap 2 1 :=
  fun i => if i = (⟨1, by decide⟩ : Fin 2) then some ⟨0, by decide⟩ else none

theorem ceHole_not_disjointExtension :
    ¬ DisjointExtension ceHoleFst ceHoleSnd := by
  intro hd
  exact hd.2 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide) (by decide)

/-- Channel isolation: `ceHole` SATISFIES the silence conjunct (channel 1),
so its homomorphism failure is attributable to the hole channel alone. -/
theorem ceHole_silent_on_fixed :
    ∀ i a, ceHoleFst i = some a → ceHoleSnd i = none := by
  decide

theorem ceHole_homomorphism_fails :
    toRestriction (compose ceHoleFst ceHoleSnd) ≠
      RestrictionComposition.compose (toRestriction ceHoleFst)
        (toRestriction ceHoleSnd) := by
  intro hEq
  have hpt := congrFun hEq (phpVar 2 1 ⟨1, by decide⟩ ⟨0, by decide⟩)
  revert hpt
  decide

/-- Channel-1 counterexample (domain overlap, holes disjoint — this pair IS
`CrossConsistent`, so cross-consistency alone cannot support the
homomorphism): `p = 2, h = 2`, first map `{0 ↦ h0}`, extension `{0 ↦ h1}`.
First-wins drops the extension's assignment, but the boolean side still
silences hole `h1`. -/
def ceDomFst : MatchingMap 2 2 :=
  fun i => if i = (⟨0, by decide⟩ : Fin 2) then some ⟨0, by decide⟩ else none

def ceDomSnd : MatchingMap 2 2 :=
  fun i => if i = (⟨0, by decide⟩ : Fin 2) then some ⟨1, by decide⟩ else none

theorem ceDom_crossConsistent : CrossConsistent ceDomFst ceDomSnd := by
  intro i j a h0i h0j h1j
  revert h0i h0j h1j
  revert i j a
  decide

theorem ceDom_not_disjointExtension :
    ¬ DisjointExtension ceDomFst ceDomSnd := by
  intro hd
  have hnone := hd.1 ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
  revert hnone
  decide

/-- Channel isolation: `ceDom` SATISFIES the hole-disjointness conjunct
(channel 2) — strictly stronger than `ceDom_crossConsistent` — so its
homomorphism failure is attributable to the domain channel alone. -/
theorem ceDom_holeDisjoint :
    ∀ i j a, ceDomFst i = some a → ceDomSnd j ≠ some a := by
  decide

theorem ceDom_homomorphism_fails :
    toRestriction (compose ceDomFst ceDomSnd) ≠
      RestrictionComposition.compose (toRestriction ceDomFst)
        (toRestriction ceDomSnd) := by
  intro hEq
  have hpt := congrFun hEq (phpVar 2 2 ⟨1, by decide⟩ ⟨1, by decide⟩)
  revert hpt
  decide

/-! ## Genuinely partial witnesses (square and rectangular) -/

/-- Square witness `p = h = 3`: `{0 ↦ 0}` (one of three pigeons fixed —
genuinely partial), extended by `{1 ↦ 1}`. -/
def sqFst : MatchingMap 3 3 :=
  fun i => if i = (⟨0, by decide⟩ : Fin 3) then some ⟨0, by decide⟩ else none

def sqSnd : MatchingMap 3 3 :=
  fun i => if i = (⟨1, by decide⟩ : Fin 3) then some ⟨1, by decide⟩ else none

theorem sq_genuinely_partial :
    0 < (freePigeons sqFst).card ∧ (freePigeons sqFst).card < 3 := by
  decide

theorem sq_disjointExtension : DisjointExtension sqFst sqSnd := by
  constructor
  · intro i a
    revert i a
    decide
  · intro i j a
    revert i j a
    decide

theorem sq_isMatching_fst : IsMatching sqFst := by
  intro i j a
  revert i j a
  decide

theorem sq_isMatching_snd : IsMatching sqSnd := by
  intro i j a
  revert i j a
  decide

theorem sq_isMatching_compose : IsMatching (compose sqFst sqSnd) :=
  isMatching_compose sq_isMatching_fst sq_isMatching_snd
    (disjointExtension_crossConsistent sq_disjointExtension)

/-- Star drop: the extension fixes one previously-free pigeon, so the free
count drops from 2 to 1. -/
theorem sq_star_drop :
    (freePigeons (compose sqFst sqSnd)).card =
      (freePigeons sqFst).card - 1 := by
  decide

/-- The star-drop lemma exercised through its hypotheses at the square
witness (general-satisfiability discipline: `freePigeons_compose_card`'s
hypotheses are dischargeable, not just its conclusion decidable). -/
theorem sq_star_drop_via_lemma :
    (freePigeons (compose sqFst sqSnd)).card =
      (freePigeons sqFst).card -
        ({(⟨1, by decide⟩ : Fin 3)} : Finset (Fin 3)).card :=
  freePigeons_compose_card sqFst sqSnd {(⟨1, by decide⟩ : Fin 3)}
    (by intro i; revert i; decide)
    (by intro i hi; revert hi; revert i; decide)

theorem sq_homomorphism :
    toRestriction (compose sqFst sqSnd) =
      RestrictionComposition.compose (toRestriction sqFst)
        (toRestriction sqSnd) :=
  toRestriction_compose sqFst sqSnd sq_disjointExtension

/-- Rectangular witness `p = 3, h = 2` (more pigeons than holes — the PHP
shape): `{0 ↦ 0}`, extended by `{2 ↦ 1}`. -/
def rectFst : MatchingMap 3 2 :=
  fun i => if i = (⟨0, by decide⟩ : Fin 3) then some ⟨0, by decide⟩ else none

def rectSnd : MatchingMap 3 2 :=
  fun i => if i = (⟨2, by decide⟩ : Fin 3) then some ⟨1, by decide⟩ else none

theorem rect_genuinely_partial :
    0 < (freePigeons rectFst).card ∧ (freePigeons rectFst).card < 3 := by
  decide

theorem rect_disjointExtension : DisjointExtension rectFst rectSnd := by
  constructor
  · intro i a
    revert i a
    decide
  · intro i j a
    revert i j a
    decide

theorem rect_isMatching_compose : IsMatching (compose rectFst rectSnd) :=
  isMatching_compose
    (by intro i j a; revert i j a; decide)
    (by intro i j a; revert i j a; decide)
    (disjointExtension_crossConsistent rect_disjointExtension)

theorem rect_star_drop :
    (freePigeons (compose rectFst rectSnd)).card =
      (freePigeons rectFst).card - 1 := by
  decide

theorem rect_homomorphism :
    toRestriction (compose rectFst rectSnd) =
      RestrictionComposition.compose (toRestriction rectFst)
        (toRestriction rectSnd) :=
  toRestriction_compose rectFst rectSnd rect_disjointExtension

end PHPMatchingComposition
end PvNP
