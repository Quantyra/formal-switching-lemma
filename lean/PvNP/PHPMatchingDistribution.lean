import PvNP.PHPRestrictedDepthFloor

/-!
# The uniform matching-restriction space: exact star counting

Gate A rung 3, first increment: the PROBABILISTIC layer over partial-matching
restrictions, in exact COUNTING FORM (the same form as this repository's
proved SimpleDNF switching lemma).  The space is the uniform family of
`s`-subsets of pigeons, each fixed along the identity matching
(`restrictionOf S = matchingRestriction (· ∈ S) id`).  Proved here:

* the space has exactly `choose h s` elements;
* the STAR-COUNT primitive: each PHP variable is left free by exactly
  `choose (h-1) s` of the subsets (counting over subsets `S`, which the
  restriction map identifies with matchings), fixed by
  `choose h s - choose (h-1) s`, and
  the exact star-probability ratio holds in counting form:
  `h * choose (h-1) s = (h - s) * choose h s` — i.e. every variable is a star
  with probability `(h-s)/h`, the quantity switching-lemma arguments consume;
* the S2072 depth floor holds for EVERY element of the space (probability
  one): every correct tree for any restricted function has depth
  `≥ (h - s) * h`.

## HONEST SCOPE STATEMENT (read this)

* This is exact finite counting over a restriction DISTRIBUTION — the
  interface layer for a future PHP switching lemma — plus the
  probability-one transfer of the S2072 worst-case floors.  The distribution
  here varies WHICH pigeons are fixed but pins the matching to the identity;
  the uniform-over-injections space is the recorded successor.
* This is NOT a switching lemma: no collapse-probability upper bound for
  restricted formulas is stated or claimed (that is the genuinely hard open
  summit).  NOT a Frege/PHP proof-size bound, NOT an NP/circuit bound, NOT
  a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingDistribution

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPSearchFloor
open PHPBooleanDepthFloor
open PHPRestrictedDepthFloor

/-! ## The space -/

/-- The uniform space of `s`-subsets of pigeons. -/
def subsetSpace (h s : Nat) : Finset (Finset (Fin h)) :=
  Finset.powersetCard s (Finset.univ : Finset (Fin h))

theorem card_subsetSpace (h s : Nat) :
    (subsetSpace h s).card = Nat.choose h s := by
  rw [subsetSpace, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The restriction of an `s`-subset: its pigeons are fixed along the
identity matching; the rest are free. -/
def restrictionOf {h : Nat} (S : Finset (Fin h)) :
    Restriction (Nat.succ (h * h)) :=
  matchingRestriction (fun i => decide (i ∈ S)) (fun i => i)

/-- A PHP variable is left free exactly when its pigeon is not fixed. -/
theorem restrictionOf_phpVar_eq_none_iff {h : Nat} (S : Finset (Fin h))
    (i j : Fin h) :
    restrictionOf S (phpVar h h i j) = none ↔ i ∉ S := by
  have hlt := phpVar_lt (p := h) (h := h) i j
  rw [restrictionOf, matchingRestriction, dif_pos hlt,
    pigeonOf_phpVar i j hlt]
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi]

/-! ## Star and fix counts -/

/-- The subsets avoiding a pigeon are exactly the `s`-subsets of the other
`h - 1` pigeons. -/
theorem filter_not_mem_subsetSpace {h s : Nat} (i : Fin h) :
    (subsetSpace h s).filter (fun S => i ∉ S) =
      Finset.powersetCard s (Finset.univ.erase i) := by
  ext S
  simp only [subsetSpace, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_erase]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hnot⟩
    exact ⟨⟨hsub, hnot⟩, hcard⟩
  · rintro ⟨⟨hsub, hnot⟩, hcard⟩
    exact ⟨⟨hsub, hcard⟩, hnot⟩

/-- **Star count.**  Each pigeon is left free by exactly `choose (h-1) s`
restrictions of the space. -/
theorem freeCount_eq {h s : Nat} (i : Fin h) :
    ((subsetSpace h s).filter (fun S => i ∉ S)).card =
      Nat.choose (h - 1) s := by
  rw [filter_not_mem_subsetSpace, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

/-- **Fix count** (complement form). -/
theorem fixCount_eq {h s : Nat} (i : Fin h) :
    ((subsetSpace h s).filter (fun S => i ∈ S)).card =
      Nat.choose h s - Nat.choose (h - 1) s := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := subsetSpace h s) (p := fun S => i ∈ S)
  rw [card_subsetSpace] at hsplit
  have hfree : ((subsetSpace h s).filter (fun S => ¬ (i ∈ S))).card =
      Nat.choose (h - 1) s := freeCount_eq i
  omega

/-- **The exact star-probability ratio, in counting form:**
`h * choose (h-1) s = (h - s) * choose h s` — each variable is a star with
probability `(h - s) / h` over the space. -/
theorem star_ratio (h s : Nat) :
    h * Nat.choose (h - 1) s = (h - s) * Nat.choose h s := by
  cases h with
  | zero => simp
  | succ h' =>
      calc (h' + 1) * Nat.choose (h' + 1 - 1) s
          = Nat.choose (h' + 1) (s + 1) * (s + 1) := by
            rw [Nat.add_sub_cancel]
            exact Nat.succ_mul_choose_eq h' s
        _ = Nat.choose (h' + 1) s * (h' + 1 - s) :=
            Nat.choose_succ_right_eq (h' + 1) s
        _ = (h' + 1 - s) * Nat.choose (h' + 1) s := Nat.mul_comm _ _

/-- Variable-level star count: every PHP variable is left free by exactly
`choose (h-1) s` restrictions. -/
theorem phpVar_freeCount {h s : Nat} (i j : Fin h) :
    ((subsetSpace h s).filter
      (fun S => restrictionOf S (phpVar h h i j) = none)).card =
      Nat.choose (h - 1) s := by
  have hcongr : (subsetSpace h s).filter
      (fun S => restrictionOf S (phpVar h h i j) = none) =
      (subsetSpace h s).filter (fun S => i ∉ S) := by
    apply Finset.filter_congr
    intro S _
    simp [restrictionOf_phpVar_eq_none_iff]
  rw [hcongr, freeCount_eq]

/-! ## Row counting for the floor transfer -/

/-- Filter partition of a list length (complement predicate passed explicitly
to keep terms in beta-normal form). -/
private theorem length_filter_add_length_filter_not {α : Type _}
    (p q : α → Bool) (hq : ∀ x, q x = !(p x)) :
    ∀ l : List α,
      (l.filter p).length + (l.filter q).length = l.length
  | [] => rfl
  | x :: l => by
      have ih := length_filter_add_length_filter_not p q hq l
      cases hpx : p x <;>
        simp [List.filter_cons, hpx, hq x] <;>
        omega

/-- The fixed-row count over the full enumeration equals the subset's card. -/
private theorem filter_mem_finList_length {h : Nat} (S : Finset (Fin h)) :
    ((finList h).filter (fun i => decide (i ∈ S))).length = S.card := by
  have hnd : ((finList h).filter (fun i => decide (i ∈ S))).Nodup :=
    List.Nodup.filter _ (finList_nodup h)
  have htf : ((finList h).filter (fun i => decide (i ∈ S))).toFinset = S := by
    ext i
    simp [List.mem_toFinset, List.mem_filter, mem_finList h i]
  calc ((finList h).filter (fun i => decide (i ∈ S))).length
      = ((finList h).filter (fun i => decide (i ∈ S))).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ = S.card := by rw [htf]

/-- Free-row count for a subset of card `s`. -/
theorem freeRows_card {h s : Nat} (S : Finset (Fin h)) (hS : S.card = s) :
    (freeRows (fun i => decide (i ∈ S))).length = h - s := by
  have hpart := length_filter_add_length_filter_not
    (fun i => decide (i ∈ S)) (fun i => !(decide (i ∈ S)))
    (fun _ => rfl) (finList h)
  rw [filter_mem_finList_length, finList_length, hS] at hpart
  show ((finList h).filter (fun i => !(decide (i ∈ S)))).length = h - s
  omega

/-! ## The floor holds with probability one over the space -/

/-- **Probability-one floor transfer.**  For EVERY restriction in the uniform
`s`-subset space, every decision tree computing the restricted `h x h` PHP
function has depth at least `(h - s) * h` (the S2072 master floor, holding at
every point of the distribution). -/
theorem subsetSpace_depthFloor {h s : Nat} (S : Finset (Fin h))
    (hS : S ∈ subsetSpace h s)
    (T : DTree (Nat.succ (h * h)))
    (hT : ∀ a : Assignment (Nat.succ (h * h)),
      Agree (restrictionOf S) a →
      dtEval a T =
        eval a (restrict (restrictionOf S)
          (restrictedPHPFormula (fullPHPView h)))) :
    (h - s) * h ≤ dtDepth T := by
  have hScard : S.card = s := by
    have := Finset.mem_powersetCard.mp hS
    exact this.2
  have hmaster := matchingRestriction_depthFloor
    (fun i => decide (i ∈ S)) (fun i => i) (fun i => i)
    (fun _ => rfl) (fun _ => rfl) T hT
  rwa [freeVars_length, freeRows_card S hScard] at hmaster

/-- Non-vacuity, in fact for EVERY subset (not just members of the space): a
correct tree of depth `h*h + 1` exists for every restriction. -/
theorem subsetSpace_correctTree_exists {h : Nat} (S : Finset (Fin h)) :
    ∃ T : DTree (Nat.succ (h * h)),
      (∀ a : Assignment (Nat.succ (h * h)),
        Agree (restrictionOf S) a →
        dtEval a T =
          eval a (restrict (restrictionOf S)
            (restrictedPHPFormula (fullPHPView h)))) ∧
      dtDepth T = h * h + 1 := by
  refine ⟨dtOfFun
    (fun a => eval a (restrict (restrictionOf S)
      (restrictedPHPFormula (fullPHPView h))))
    (finList (Nat.succ (h * h))) (fun _ => false), fun a _ => ?_, ?_⟩
  · apply dtOfFun_eval
    intro v
    exact Or.inl (mem_finList _ v)
  · rw [dtOfFun_depth, finList_length]

end PHPMatchingDistribution
end PvNP
