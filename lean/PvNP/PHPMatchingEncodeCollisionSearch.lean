import PvNP.PHPMatchingEncodeInjectivity
import Mathlib.Tactic.FinCases

/-!
# S2199: genuine encode-preimage collision search (finite Fin-2 board)

Searches for (or rules out) collisions
`encodeMatch ρ₁ = encodeMatch ρ₂ ∧ enteredTermsOf ρ₁ ≠ enteredTermsOf ρ₂`
on the smallest square board `p = h = 2`, over the **complete** finite set of
hole-injective matchings.

This is a genuine preimage search over matchings (not a named-pair DNF-term
check).  Bounds are honest:

* board `Fin 2` only (7 hole-injective matchings, fully listed and complete);
* free-count `ell = 2` slice: unique preimage ⇒ no collision;
* free-count `ell = 1` at `t = 1`: entered-term length ≤ 1, so the S2198
  length-≤1 residual discharges equal-code entered-term equality — no
  length-2 collision on this slice;
* free-count `0` and `t ≥ 2` length-2 images remain open (no collision
  witness banked; no false exhaustion claim).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeCollisionSearch

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity

/-! ## Exhaustive Fin-2 matching enumeration -/

/-- Encode a raw `Fin 2 → Option (Fin 2)` matching from its two values. -/
def mkMap2 (a0 a1 : Option (Fin 2)) : MatchingMap 2 2 :=
  fun i => if i = (0 : Fin 2) then a0 else a1

/-- Explicit exhaustive list of the seven hole-injective Fin-2 matchings. -/
def allMatchings2 : List (MatchingMap 2 2) :=
  [mkMap2 none none,
    mkMap2 none (some 0),
    mkMap2 none (some 1),
    mkMap2 (some 0) none,
    mkMap2 (some 0) (some 1),
    mkMap2 (some 1) none,
    mkMap2 (some 1) (some 0)]

theorem allMatchings2_length : allMatchings2.length = 7 := rfl

private theorem isMatching_mkMap2_none_none :
    IsMatching (mkMap2 (none : Option (Fin 2)) none) := by
  intro i j a hi hj
  simp [mkMap2] at hi

private theorem isMatching_mkMap2_none_some (a : Fin 2) :
    IsMatching (mkMap2 none (some a)) := by
  intro i j b hi hj
  simp only [mkMap2] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all

private theorem isMatching_mkMap2_some_none (a : Fin 2) :
    IsMatching (mkMap2 (some a) none) := by
  intro i j b hi hj
  simp only [mkMap2] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all

private theorem isMatching_mkMap2_diag :
    IsMatching (mkMap2 (some (0 : Fin 2)) (some 1)) := by
  intro i j a hi hj
  simp only [mkMap2] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all

private theorem isMatching_mkMap2_anti :
    IsMatching (mkMap2 (some (1 : Fin 2)) (some 0)) := by
  intro i j a hi hj
  simp only [mkMap2] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all

theorem isMatching_of_mem_allMatchings2 {mu : MatchingMap 2 2}
    (h : mu ∈ allMatchings2) : IsMatching mu := by
  have h' :
      mu = mkMap2 none none ∨
        mu = mkMap2 none (some 0) ∨
        mu = mkMap2 none (some 1) ∨
        mu = mkMap2 (some 0) none ∨
        mu = mkMap2 (some 0) (some 1) ∨
        mu = mkMap2 (some 1) none ∨
        mu = mkMap2 (some 1) (some 0) := by
    simpa [allMatchings2] using h
  rcases h' with h | h | h | h | h | h | h
  · rw [h]; exact isMatching_mkMap2_none_none
  · rw [h]; exact isMatching_mkMap2_none_some 0
  · rw [h]; exact isMatching_mkMap2_none_some 1
  · rw [h]; exact isMatching_mkMap2_some_none 0
  · rw [h]; exact isMatching_mkMap2_diag
  · rw [h]; exact isMatching_mkMap2_some_none 1
  · rw [h]; exact isMatching_mkMap2_anti

/-- Completeness: every hole-injective Fin-2 matching equals one listed map. -/
theorem eq_mem_allMatchings2_of_isMatching (mu : MatchingMap 2 2)
    (hmu : IsMatching mu) :
    mu = mkMap2 none none ∨
      mu = mkMap2 none (some 0) ∨
      mu = mkMap2 none (some 1) ∨
      mu = mkMap2 (some 0) none ∨
      mu = mkMap2 (some 0) (some 1) ∨
      mu = mkMap2 (some 1) none ∨
      mu = mkMap2 (some 1) (some 0) := by
  cases h0 : mu 0 with
  | none =>
      cases h1 : mu 1 with
      | none =>
          left
          funext i; fin_cases i <;> simp [mkMap2, h0, h1]
      | some a =>
          fin_cases a
          · right; left
            funext i; fin_cases i <;> simp [mkMap2, h0, h1]
          · right; right; left
            funext i; fin_cases i <;> simp [mkMap2, h0, h1]
  | some a0 =>
      cases h1 : mu 1 with
      | none =>
          fin_cases a0
          · right; right; right; left
            funext i; fin_cases i <;> simp [mkMap2, h0, h1]
          · right; right; right; right; right; left
            funext i; fin_cases i <;> simp [mkMap2, h0, h1]
      | some a1 =>
          fin_cases a0 <;> fin_cases a1
          · exfalso
            have : (0 : Fin 2) = 1 := hmu 0 1 0 h0 h1
            exact absurd this (by decide)
          · right; right; right; right; left
            funext i; fin_cases i <;> simp [mkMap2, h0, h1]
          · right; right; right; right; right; right
            funext i; fin_cases i <;> simp [mkMap2, h0, h1]
          · exfalso
            have : (0 : Fin 2) = 1 := hmu 0 1 1 h0 h1
            exact absurd this (by decide)

theorem mem_allMatchings2_of_isMatching (mu : MatchingMap 2 2)
    (hmu : IsMatching mu) : mu ∈ allMatchings2 := by
  rcases eq_mem_allMatchings2_of_isMatching mu hmu with
    h | h | h | h | h | h | h
  · simp [allMatchings2, h]
  · simp [allMatchings2, h]
  · simp [allMatchings2, h]
  · simp [allMatchings2, h]
  · simp [allMatchings2, h]
  · simp [allMatchings2, h]
  · simp [allMatchings2, h]

/-! ## Search family -/

/-- Search DNF: two width-1 legal terms on distinct pairs. -/
def searchD : MDNF 2 2 :=
  [[((0 : Fin 2), (0 : Fin 2))], [((1 : Fin 2), (1 : Fin 2))]]

theorem searchD_width : ∀ term ∈ searchD, term.length ≤ 2 := by
  intro term ht
  have ht' : term = [((0 : Fin 2), (0 : Fin 2))] ∨
      term = [((1 : Fin 2), (1 : Fin 2))] := by
    simpa [searchD] using ht
  rcases ht' with h | h <;> subst h <;> decide

/-- Collision predicate on a pair of genuine encode preimages (`w = 2`). -/
def isEnteredTermsCollision {ell t : Nat}
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD rho₂)) : Prop :=
  encodeMatch (p := 2) (h := 2) (w := 2) (t := t) (ell := ell) rfl
      rho₁ searchD hrho₁ hell₁ ht₁ searchD_width =
    encodeMatch (p := 2) (h := 2) (w := 2) (t := t) (ell := ell) rfl
      rho₂ searchD hrho₂ hell₂ ht₂ searchD_width ∧
    enteredTermsOf rho₁ searchD t ≠ enteredTermsOf rho₂ searchD t

/-! ## Free-count classification -/

private theorem freePigeons_mkMap2_none_none :
    (freePigeons (mkMap2 (none : Option (Fin 2)) none)).card = 2 := by
  have h : freePigeons (mkMap2 (none : Option (Fin 2)) none) =
      (Finset.univ : Finset (Fin 2)) := by
    ext i; simp [freePigeons, mkMap2]
  rw [h, Finset.card_univ, Fintype.card_fin]

private theorem freePigeons_mkMap2_none_some (a : Fin 2) :
    (freePigeons (mkMap2 none (some a))).card = 1 := by
  have h : freePigeons (mkMap2 none (some a)) = ({(0 : Fin 2)} : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [freePigeons, mkMap2]
  rw [h, Finset.card_singleton]

private theorem freePigeons_mkMap2_some_none (a : Fin 2) :
    (freePigeons (mkMap2 (some a) none)).card = 1 := by
  have h : freePigeons (mkMap2 (some a) none) = ({(1 : Fin 2)} : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [freePigeons, mkMap2]
  rw [h, Finset.card_singleton]

private theorem freePigeons_mkMap2_diag :
    (freePigeons (mkMap2 (some (0 : Fin 2)) (some 1))).card = 0 := by
  have h : freePigeons (mkMap2 (some (0 : Fin 2)) (some 1)) =
      (∅ : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [freePigeons, mkMap2]
  rw [h, Finset.card_empty]

private theorem freePigeons_mkMap2_anti :
    (freePigeons (mkMap2 (some (1 : Fin 2)) (some 0))).card = 0 := by
  have h : freePigeons (mkMap2 (some (1 : Fin 2)) (some 0)) =
      (∅ : Finset (Fin 2)) := by
    ext i
    fin_cases i <;> simp [freePigeons, mkMap2]
  rw [h, Finset.card_empty]

/-- On Fin 2 the only free-count-2 matching is the empty matching. -/
theorem unique_ell_two (rho : MatchingMap 2 2) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = 2) :
    rho = mkMap2 none none := by
  rcases eq_mem_allMatchings2_of_isMatching rho hrho with
    h | h | h | h | h | h | h
  · exact h
  · subst h; rw [freePigeons_mkMap2_none_some] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_none_some] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_some_none] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_diag] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_some_none] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_anti] at hell; cases hell

/-- **No collision at ell = 2.**  Only one free-count-2 preimage exists. -/
theorem no_collision_ell_two {t : Nat}
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 2)
    (hell₂ : (freePigeons rho₂).card = 2)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD rho₂)) :
    ¬ isEnteredTermsCollision (t := t) (ell := 2)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨_, hterms⟩
  have h1 := unique_ell_two rho₁ hrho₁ hell₁
  have h2 := unique_ell_two rho₂ hrho₂ hell₂
  exact hterms (by rw [h1, h2])

/-- Free-count-1 matchings on Fin 2: the four singles. -/
theorem ell_one_classification (rho : MatchingMap 2 2) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = 1) :
    rho = mkMap2 none (some 0) ∨
      rho = mkMap2 none (some 1) ∨
      rho = mkMap2 (some 0) none ∨
      rho = mkMap2 (some 1) none := by
  rcases eq_mem_allMatchings2_of_isMatching rho hrho with
    h | h | h | h | h | h | h
  · subst h; rw [freePigeons_mkMap2_none_none] at hell; cases hell
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · subst h; rw [freePigeons_mkMap2_diag] at hell; cases hell
  · exact Or.inr (Or.inr (Or.inr h))
  · subst h; rw [freePigeons_mkMap2_anti] at hell; cases hell

/-- Free-count-0 matchings on Fin 2: the two perfect matchings. -/
theorem ell_zero_classification (rho : MatchingMap 2 2) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = 0) :
    rho = mkMap2 (some 0) (some 1) ∨ rho = mkMap2 (some 1) (some 0) := by
  rcases eq_mem_allMatchings2_of_isMatching rho hrho with
    h | h | h | h | h | h | h
  · subst h; rw [freePigeons_mkMap2_none_none] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_none_some] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_none_some] at hell; cases hell
  · subst h; rw [freePigeons_mkMap2_some_none] at hell; cases hell
  · exact Or.inl h
  · subst h; rw [freePigeons_mkMap2_some_none] at hell; cases hell
  · exact Or.inr h

/-! ## Entered-term length ≤ depth budget -/

private theorem join_length_ge_of_forall_ne_nil {α : Type*} :
    ∀ (ls : List (List α)), (∀ l ∈ ls, l ≠ []) →
      ls.length ≤ ls.join.length
  | [], _ => Nat.zero_le _
  | l :: ls, h => by
      have hl : l ≠ [] := h l (List.mem_cons_self _ _)
      have hpos : 0 < l.length := List.length_pos_of_ne_nil hl
      have htail := join_length_ge_of_forall_ne_nil ls
        (fun m hm => h m (List.mem_cons_of_mem _ hm))
      simp only [List.length_cons, List.join_cons, List.length_append]
      omega

/-- Every block of a `vevents` trace has a nonempty step list (live entries
always emit `enter` together with a first query step). -/
private theorem blocksOf_vevents_steps_ne_nil {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)) (B : VBlock p h),
      B ∈ blocksOf (vevents fuel mu pending D feed) → B.steps ≠ []
  | fuel, mu, [], [], feed, B, hB => by
      rw [vevents_nil, blocksOf_nil] at hB; cases hB
  | fuel, mu, [], t :: rest, feed, B, hB => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t rest feed hleg hfals] at hB
          exact blocksOf_vevents_steps_ne_nil fuel mu [] rest feed B hB
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t rest feed hleg hfals' hsat,
              blocksOf_nil] at hB
            cases hB
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t rest feed hleg hfals' hsat',
                  blocksOf_nil] at hB
                cases hB
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t rest feed hleg
                      hfals' hsat' htv, blocksOf_nil] at hB
                    cases hB
                | cons v vs =>
                    cases v with
                    | inl i =>
                        cases feed with
                        | nil =>
                            rw [vevents_entry_feed_nil fuel' mu t rest i vs
                              hleg hfals' hsat' htv, blocksOf_nil] at hB
                            cases hB
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents_entry_feed_illkind fuel' mu t rest
                                  i vs q fs hleg hfals' hsat' htv,
                                  blocksOf_nil] at hB
                                cases hB
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t
                                    rest i vs a fs hleg hfals' hsat' htv hha,
                                    blocksOf_nil] at hB
                                  cases hB
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t rest
                                    i vs a fs hleg hfals' hsat' htv hha',
                                    blocksOf_enter] at hB
                                  cases hB with
                                  | head =>
                                      simp [stepsPrefix]
                                  | tail _ hB' =>
                                      exact blocksOf_vevents_steps_ne_nil
                                        fuel'
                                        (compose mu (singleMatching i a)) vs
                                        (t :: rest) fs B
                                        (by
                                          rwa [← blocksOf_afterSteps])
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t rest feed hleg'] at hB
        exact blocksOf_vevents_steps_ne_nil fuel mu [] rest feed B hB
  | fuel, mu, v :: vs, D, feed, B, hB => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov] at hB
        exact blocksOf_vevents_steps_ne_nil fuel mu vs D feed B hB
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov', blocksOf_nil] at hB
            cases hB
        | succ fuel' =>
            cases v with
            | inl i =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov',
                      blocksOf_nil] at hB
                    cases hB
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents_block_pigeon_illkind fuel' mu i vs D q fs
                          hcov', blocksOf_nil] at hB
                        cases hB
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents_block_pigeon_dead fuel' mu i vs D a fs
                            hcov' hha, blocksOf_nil] at hB
                          cases hB
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a fs
                            hcov' hha', blocksOf_qstep] at hB
                          exact blocksOf_vevents_steps_ne_nil fuel'
                            (compose mu (singleMatching i a)) vs D fs B hB
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov',
                      blocksOf_nil] at hB
                    cases hB
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents_block_hole_illkind fuel' mu b vs D a fs
                          hcov', blocksOf_nil] at hB
                        cases hB
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents_block_hole_dead fuel' mu b vs D q fs
                            hcov' hq, blocksOf_nil] at hB
                          cases hB
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq', blocksOf_qstep] at hB
                          exact blocksOf_vevents_steps_ne_nil fuel'
                            (compose mu (singleMatching q b)) vs D fs B hB
  termination_by fuel _ pending D _ _ => (fuel, pending.length + D.length)

/-- On every encode image the entered-term list has length at most `t`. -/
theorem enteredTermsOf_length_le_t {p h : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    {t : Nat} (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    (enteredTermsOf rho D t).length ≤ t := by
  simp only [enteredTermsOf, List.length_map]
  let feed := leftmostLiveDeepFeed rho D t
  have hsteps :
      (eventsSteps (vtrace rho D feed)).length = t :=
    leftmostLiveDeepFeed_vtrace_eventsSteps_length hsq rho D hrho ht
  have hpart :
      eventsSteps (vtrace rho D feed) =
        ((blocksOf (vtrace rho D feed)).map VBlock.steps).join :=
    vtrace_steps_partition (freePigeons rho).card rho D feed
  have hne :
      ∀ l ∈ (blocksOf (vtrace rho D feed)).map VBlock.steps, l ≠ [] := by
    intro l hl
    rw [List.mem_map] at hl
    rcases hl with ⟨B, hB, rfl⟩
    exact blocksOf_vevents_steps_ne_nil (freePigeons rho).card rho [] D feed B
      hB
  have hle :=
    join_length_ge_of_forall_ne_nil
      ((blocksOf (vtrace rho D feed)).map VBlock.steps) hne
  have hlen_map :
      ((blocksOf (vtrace rho D feed)).map VBlock.steps).length =
        (blocksOf (vtrace rho D feed)).length :=
    List.length_map _ _
  calc
    (blocksOf (vtrace rho D feed)).length =
        ((blocksOf (vtrace rho D feed)).map VBlock.steps).length :=
      hlen_map.symm
    _ ≤ ((blocksOf (vtrace rho D feed)).map VBlock.steps).join.length := hle
    _ = (eventsSteps (vtrace rho D feed)).length := by rw [← hpart]
    _ = t := hsteps

/-- At `t = 1`, free-count-1 equal codes force equal entered-term lists. -/
theorem no_collision_ell_one_t_one
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 1)
    (hell₂ : (freePigeons rho₂).card = 1)
    (ht₁ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₂))
    (hcode :
      encodeMatch (p := 2) (h := 2) (w := 2) (t := 1) (ell := 1) rfl
        rho₁ searchD hrho₁ hell₁ ht₁ searchD_width =
      encodeMatch (p := 2) (h := 2) (w := 2) (t := 1) (ell := 1) rfl
        rho₂ searchD hrho₂ hell₂ ht₂ searchD_width) :
    enteredTermsOf rho₁ searchD 1 = enteredTermsOf rho₂ searchD 1 := by
  have hres :
      EncodeMatchEnteredTermsEqResidual (p := 2) (h := 2) (w := 2) (t := 1)
        (ell := 1) rfl searchD searchD_width :=
    encodeMatchEnteredTermsEqResidual_of_length_le_one (p := 2) (h := 2)
      (w := 2) (t := 1) (ell := 1) rfl searchD searchD_width
      (fun rho hrho _ ht => enteredTermsOf_length_le_t rfl rho searchD hrho ht)
  exact hres rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode

theorem no_collision_ell_one_t_one'
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 1)
    (hell₂ : (freePigeons rho₂).card = 1)
    (ht₁ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₂)) :
    ¬ isEnteredTermsCollision (t := 1) (ell := 1)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨hcode, hterms⟩
  exact hterms (no_collision_ell_one_t_one rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂
    ht₁ ht₂ hcode)

/-- **S2199 collision-search summary (Fin 2 / `searchD`).**

* Exhaustive matching list length 7 (`allMatchings2_length`), complete for
  `IsMatching` (`mem_allMatchings2_of_isMatching`).
* `ell = 2`: unique preimage ⇒ no collision (`no_collision_ell_two`).
* `ell = 1`, `t = 1`: equal codes ⇒ equal entered terms via length-≤1
  residual (`no_collision_ell_one_t_one'`); no length-2 collision possible
  because entered-term length ≤ `t = 1`.
* `ell = 0` and `t ≥ 2` length-2 images: open (no witness, no false
  exhaustion).  Next story: pin pairwise encode equality on the two perfect
  matchings and on free-count-1 maps at `t = 2`.
-/
theorem collision_search_fin2_summary :
    allMatchings2.length = 7 ∧
      (∀ (mu : MatchingMap 2 2), IsMatching mu → mu ∈ allMatchings2) ∧
      (∀ (rho₁ rho₂ : MatchingMap 2 2)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = 2)
        (hell₂ : (freePigeons rho₂).card = 2)
        (ht₁ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
        (ht₂ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
        ¬ isEnteredTermsCollision (t := 1) (ell := 2)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) ∧
      (∀ (rho₁ rho₂ : MatchingMap 2 2)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = 1)
        (hell₂ : (freePigeons rho₂).card = 1)
        (ht₁ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
        (ht₂ : 1 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
        ¬ isEnteredTermsCollision (t := 1) (ell := 1)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) :=
  ⟨allMatchings2_length,
    mem_allMatchings2_of_isMatching,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_two _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_one_t_one' _ _ _ _ _ _ _ _⟩

end PHPMatchingEncodeCollisionSearch
end PvNP
