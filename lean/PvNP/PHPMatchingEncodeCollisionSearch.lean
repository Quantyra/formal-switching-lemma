import PvNP.PHPMatchingEncodeInjectivity
import Mathlib.Tactic.FinCases

/-!
# S2199–S2203: genuine encode-preimage collision search

## S2199: Fin-2 entered-term collision search

Searches for (or rules out) collisions
`encodeMatch ρ₁ = encodeMatch ρ₂ ∧ enteredTermsOf ρ₁ ≠ enteredTermsOf ρ₂`
on the smallest square board `p = h = 2`, over the **complete** finite set of
hole-injective matchings.

Bounds are honest:

* board `Fin 2` only (7 hole-injective matchings, fully listed and complete);
* DNF fixed to the two-term search family `searchD` (not arbitrary DNF);
* free-count `ell = 2`: unique preimage ⇒ no collision (any `t`);
* free-count `ell = 1` at `t = 1`: entered-term length ≤ 1 residual;
* free-count `ell ∈ {0,1}` at `t = 2`: empty depth-eligible slice;
* free-count `ell = 2` at `t = 2`: unique preimage ⇒ no collision.

## S2202: Fin-3 path-exit collision gate

Board `Fin 3`, DNF `searchD3` (three width-1 diagonal terms), depth `t = 2`:

* width-≤1 barrier (board-independent): no length-2 encode image at `t = 2`;
* free-count `ell = 3`: unique empty matching; `ell ≤ 1`: empty depth slice;
* equal codes ⇒ equal entered terms (length-≤1 residual) and equal path exits;
* `EncodeMatchLengthTwoExitEqResidual` discharged vacuously on this package;
* no path-exit / entered-term collision witness; no bank stop-loss.

## S2203: width≥2 length-2 path-exit collision gate (non-vacuous)

Board `Fin 3`, DNF `searchDw2` (width-2 anti-diagonal first term plus a
width-1 closer), depth `t = 3`, empty matching:

* genuine width-2 first term `[(0,1),(1,0)]`;
* non-vacuous length-2 encode image under empty `ρ` (`enteredTermsOf` length 2);
* free-count `ell = 3`: unique empty preimage ⇒ no path-exit / entered-term
  collision; `ell < 3`: empty depth-eligible slice at `t = 3`;
* `EncodeMatchLengthTwoExitEqResidual` and the S2197 residual discharge on this
  package by unique-preimage (not by absence of length-2 images);
* no bank stop-loss.

**Still open:** packet-only walked-pair / G3-prefix path-exit recovery in
general (beyond unique-preimage packages); unconditional
`encodeMatch_subtype_injective`.

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
open RestrictedPHPFloor

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

/-! ## Depth eligibility barrier (canonical fuel = free-pigeon count) -/

/-- Canonical depth never exceeds free-pigeon count, so `ell < t` kills every
encode-preimage hypothesis `t ≤ vmdtDepth (canonicalVMDT searchD ρ)`. -/
theorem not_depth_eligible_of_free_lt_t {ell t : Nat}
    (rho : MatchingMap 2 2) (hell : (freePigeons rho).card = ell)
    (hlt : ell < t) :
    ¬ t ≤ vmdtDepth (canonicalVMDT searchD rho) := by
  intro ht
  have hle := vmdtDepth_canonicalVMDT_le_freePigeons searchD rho
  omega

/-- No free-count-1 matching is depth-eligible at `t = 2`. -/
theorem not_depth_eligible_ell_one_t_two (rho : MatchingMap 2 2)
    (hell : (freePigeons rho).card = 1) :
    ¬ 2 ≤ vmdtDepth (canonicalVMDT searchD rho) :=
  not_depth_eligible_of_free_lt_t (ell := 1) (t := 2) rho hell (by decide)

/-- No free-count-0 matching is depth-eligible at `t = 2`. -/
theorem not_depth_eligible_ell_zero_t_two (rho : MatchingMap 2 2)
    (hell : (freePigeons rho).card = 0) :
    ¬ 2 ≤ vmdtDepth (canonicalVMDT searchD rho) :=
  not_depth_eligible_of_free_lt_t (ell := 0) (t := 2) rho hell (by decide)

/-- On every encode image, entered-term length is at most the free-pigeon
count (via `length ≤ t ≤ depth ≤ ell`). -/
theorem enteredTermsOf_length_le_ell {ell t : Nat}
    (rho : MatchingMap 2 2) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT searchD rho)) :
    (enteredTermsOf rho searchD t).length ≤ ell := by
  have hlen := enteredTermsOf_length_le_t rfl rho searchD hrho ht
  have hdepth := vmdtDepth_canonicalVMDT_le_freePigeons searchD rho
  omega

/-- No length-2 encode image exists at free-count `ell ≤ 1`. -/
theorem no_length_two_encode_image_of_ell_le_one {ell t : Nat}
    (rho : MatchingMap 2 2) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell) (hell_le : ell ≤ 1)
    (ht : t ≤ vmdtDepth (canonicalVMDT searchD rho)) :
    (enteredTermsOf rho searchD t).length ≠ 2 := by
  intro hlen
  have hle := enteredTermsOf_length_le_ell (ell := ell) (t := t) rho hrho
    hell ht
  omega

/-! ## Fin-2 / `t = 2` genuine-preimage pair search -/

/-- **ell = 1, t = 2:** the four free-count-1 matchings are pairwise
non-colliding because none is depth-eligible — the encode-preimage slice is
empty, so the collision predicate cannot hold. -/
theorem no_collision_ell_one_t_two
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 1)
    (hell₂ : (freePigeons rho₂).card = 1)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)) :
    ¬ isEnteredTermsCollision (t := 2) (ell := 1)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  exact (not_depth_eligible_ell_one_t_two rho₁ hell₁ ht₁).elim

/-- **ell = 0, t = 2:** the two perfect matchings are pairwise non-colliding
because neither is depth-eligible — empty encode-preimage slice. -/
theorem no_collision_ell_zero_t_two
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 0)
    (hell₂ : (freePigeons rho₂).card = 0)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)) :
    ¬ isEnteredTermsCollision (t := 2) (ell := 0)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  exact (not_depth_eligible_ell_zero_t_two rho₁ hell₁ ht₁).elim

/-- **ell = 2, t = 2:** unique free-count-2 preimage ⇒ no collision. -/
theorem no_collision_ell_two_t_two
    (rho₁ rho₂ : MatchingMap 2 2)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 2)
    (hell₂ : (freePigeons rho₂).card = 2)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)) :
    ¬ isEnteredTermsCollision (t := 2) (ell := 2)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ :=
  no_collision_ell_two rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂

/-- Explicit ell=1 classification pin: every free-count-1 matching fails
depth ≥ 2 under `searchD`. -/
theorem ell_one_all_not_depth_eligible_t_two :
    ∀ rho ∈
        [mkMap2 none (some 0), mkMap2 none (some 1),
          mkMap2 (some 0) none, mkMap2 (some 1) none],
      (freePigeons rho).card = 1 ∧
        ¬ 2 ≤ vmdtDepth (canonicalVMDT searchD rho) := by
  intro rho hrho
  have h' :
      rho = mkMap2 none (some 0) ∨
        rho = mkMap2 none (some 1) ∨
        rho = mkMap2 (some 0) none ∨
        rho = mkMap2 (some 1) none := by
    simpa using hrho
  rcases h' with h | h | h | h
  · subst h
    exact ⟨freePigeons_mkMap2_none_some 0,
      not_depth_eligible_ell_one_t_two _ (freePigeons_mkMap2_none_some 0)⟩
  · subst h
    exact ⟨freePigeons_mkMap2_none_some 1,
      not_depth_eligible_ell_one_t_two _ (freePigeons_mkMap2_none_some 1)⟩
  · subst h
    exact ⟨freePigeons_mkMap2_some_none 0,
      not_depth_eligible_ell_one_t_two _ (freePigeons_mkMap2_some_none 0)⟩
  · subst h
    exact ⟨freePigeons_mkMap2_some_none 1,
      not_depth_eligible_ell_one_t_two _ (freePigeons_mkMap2_some_none 1)⟩

/-- Explicit ell=0 classification pin: both perfect matchings fail depth ≥ 2. -/
theorem ell_zero_all_not_depth_eligible_t_two :
    ∀ rho ∈
        [mkMap2 (some 0) (some 1), mkMap2 (some 1) (some 0)],
      (freePigeons rho).card = 0 ∧
        ¬ 2 ≤ vmdtDepth (canonicalVMDT searchD rho) := by
  intro rho hrho
  have h' :
      rho = mkMap2 (some 0) (some 1) ∨
        rho = mkMap2 (some 1) (some 0) := by
    simpa using hrho
  rcases h' with h | h
  · subst h
    exact ⟨freePigeons_mkMap2_diag,
      not_depth_eligible_ell_zero_t_two _ freePigeons_mkMap2_diag⟩
  · subst h
    exact ⟨freePigeons_mkMap2_anti,
      not_depth_eligible_ell_zero_t_two _ freePigeons_mkMap2_anti⟩

/-- **S2199 collision-search summary (Fin 2 / `searchD`).**

* Exhaustive matching list length 7 (`allMatchings2_length`), complete for
  `IsMatching` (`mem_allMatchings2_of_isMatching`).
* `ell = 2`: unique preimage ⇒ no collision (`no_collision_ell_two`).
* `ell = 1`, `t = 1`: equal codes ⇒ equal entered terms via length-≤1
  residual (`no_collision_ell_one_t_one'`); no length-2 collision possible
  because entered-term length ≤ `t = 1`.
* `ell = 1`, `t = 2`: empty depth-eligible slice
  (`no_collision_ell_one_t_two` / `ell_one_all_not_depth_eligible_t_two`).
* `ell = 0`, `t = 2`: empty depth-eligible slice
  (`no_collision_ell_zero_t_two` / `ell_zero_all_not_depth_eligible_t_two`).
* `ell = 2`, `t = 2`: unique preimage (`no_collision_ell_two_t_two`).
* No collision witness; no bank stop-loss.  DNF remains fixed to `searchD`.
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
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) ∧
      (∀ (rho₁ rho₂ : MatchingMap 2 2)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = 1)
        (hell₂ : (freePigeons rho₂).card = 1)
        (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
        (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
        ¬ isEnteredTermsCollision (t := 2) (ell := 1)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) ∧
      (∀ (rho₁ rho₂ : MatchingMap 2 2)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = 0)
        (hell₂ : (freePigeons rho₂).card = 0)
        (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
        (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
        ¬ isEnteredTermsCollision (t := 2) (ell := 0)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) ∧
      (∀ (rho₁ rho₂ : MatchingMap 2 2)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = 2)
        (hell₂ : (freePigeons rho₂).card = 2)
        (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
        (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
        ¬ isEnteredTermsCollision (t := 2) (ell := 2)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) :=
  ⟨allMatchings2_length,
    mem_allMatchings2_of_isMatching,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_two _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_one_t_one' _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_one_t_two _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_zero_t_two _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_two_t_two _ _ _ _ _ _ _ _⟩

/-- Packaged t=2 Fin-2 closure: every free-count class is collision-free on
the depth-eligible encode-preimage slice (empty for `ell < 2`, unique for
`ell = 2`). -/
theorem no_collision_fin2_t_two :
    (∀ (rho₁ rho₂ : MatchingMap 2 2)
      (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
      (hell₁ : (freePigeons rho₁).card = 0)
      (hell₂ : (freePigeons rho₂).card = 0)
      (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
      (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
      ¬ isEnteredTermsCollision (t := 2) (ell := 0)
        rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) ∧
    (∀ (rho₁ rho₂ : MatchingMap 2 2)
      (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
      (hell₁ : (freePigeons rho₁).card = 1)
      (hell₂ : (freePigeons rho₂).card = 1)
      (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
      (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
      ¬ isEnteredTermsCollision (t := 2) (ell := 1)
        rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) ∧
    (∀ (rho₁ rho₂ : MatchingMap 2 2)
      (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
      (hell₁ : (freePigeons rho₁).card = 2)
      (hell₂ : (freePigeons rho₂).card = 2)
      (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₁))
      (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD rho₂)),
      ¬ isEnteredTermsCollision (t := 2) (ell := 2)
        rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) :=
  ⟨fun _ _ _ _ _ _ _ _ => no_collision_ell_zero_t_two _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_one_t_two _ _ _ _ _ _ _ _,
    fun _ _ _ _ _ _ _ _ => no_collision_ell_two_t_two _ _ _ _ _ _ _ _⟩

/-! ## S2202: Fin-3 path-exit collision gate

Board `Fin 3`, search DNF `searchD3` (three width-1 diagonal terms).  Honest
bounds:

* free-count `ell = 3`: unique empty matching ⇒ no collision;
* free-count `ell < 2` at `t = 2`: empty depth-eligible slice;
* on **any** width-≤1 DNF, `t = 2` encode images have entered-term length
  ≤ 1 (`enteredTermsOf_length_le_one_of_width_le_one_t_two`): a length-2
  image would force a one-step first block whose walked pairs equal `σ′`,
  contradicting S2200 `second_block_entry_ne_compose_entry_sigmaFull`;
* therefore no length-2 path-exit / entered-term collision witness exists on
  this package; `EncodeMatchLengthTwoExitEqResidual` and the S2197
  entered-term residual both discharge at `t = 2`;
* equal codes force equal path exits
  (`firstBlockPathExitMatching_eq_of_encodeMatch_eq_searchD3_t_two`).

Still open outside this package: general multi-block (`t ≥ 3` or width ≥ 2)
path-exit recovery from the packet alone; unconditional
`encodeMatch_subtype_injective`.
-/

/-! ### Width-≤1 / t = 2 length barrier (board-independent) -/

private theorem pairUnresolved_of_length_one_undetermined {p h : Nat}
    (mu : MatchingMap p h) (e : Fin p × Fin h)
    (hfals : termFalsifiedB mu [e] = false)
    (hsat : termSatisfiedB mu [e] = false) :
    pairUnresolvedB mu e = true := by
  have htri := pair_status_trichotomy mu e
  have hfals' : pairFalsB mu e = false := by
    simpa [termFalsifiedB] using hfals
  have hsat' : pairSatB mu e = false := by
    simpa [termSatisfiedB] using hsat
  cases hs : pairSatB mu e with
  | true =>
      simp [hs] at hsat'
  | false =>
      cases hf : pairFalsB mu e with
      | true =>
          simp [hf] at hfals'
      | false =>
          simp [hs, hf] at htri
          exact htri

private theorem exists_eq_singleton_of_length_one {α : Type*} :
    ∀ (l : List α), l.length = 1 → ∃ x, l = [x]
  | [x], _ => ⟨x, rfl⟩
  | [], h => by cases h
  | _ :: _ :: _, h => by cases h

private theorem sigmaFull_eq_singleton_of_term_singleton {p h : Nat}
    (B : VBlock p h) (e : Fin p × Fin h) (hterm : B.term = [e])
    (hunres : pairUnresolvedB B.entry e = true) :
    sigmaFull B = [e] := by
  unfold sigmaFull
  simp [hterm, hunres]

private theorem pairs_eq_of_pairVertices_eq_singletons {p h : Nat}
    (e f : Fin p × Fin h)
    (h : pairVertices [e] = pairVertices [f]) : e = f := by
  have he1 : Sum.inl e.1 ∈ pairVertices [e] :=
    (mem_pairVertices_inl _ _).mpr ⟨e, List.mem_singleton_self _, rfl⟩
  have he2 : Sum.inr e.2 ∈ pairVertices [e] :=
    (mem_pairVertices_inr _ _).mpr ⟨e, List.mem_singleton_self _, rfl⟩
  have hf1 : Sum.inl e.1 ∈ pairVertices [f] := by rw [← h]; exact he1
  have hf2 : Sum.inr e.2 ∈ pairVertices [f] := by rw [← h]; exact he2
  rcases (mem_pairVertices_inl _ _).mp hf1 with ⟨f₁, hf₁mem, hf₁⟩
  rcases (mem_pairVertices_inr _ _).mp hf2 with ⟨f₂, hf₂mem, hf₂⟩
  have hf₁e : f₁ = f := List.mem_singleton.mp hf₁mem
  have hf₂e : f₂ = f := List.mem_singleton.mp hf₂mem
  subst hf₁e; subst hf₂e
  exact Prod.ext hf₁.symm hf₂.symm

/-- Non-final width-1 one-step block: walked pairs equal `σ′`. -/
theorem first_block_walked_eq_sigmaFull_of_width_one_one_step {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho)
    (B₀ B₁ : VBlock p h) (rest : List (VBlock p h))
    (hblocks : blocksOf (vtrace rho D feed) = B₀ :: B₁ :: rest)
    (hw : B₀.term.length = 1) (hsteps : B₀.steps.length = 1) :
    B₀.steps.map VStep.pair = sigmaFull B₀ := by
  rcases exists_eq_singleton_of_length_one B₀.term hw with ⟨e, hterm⟩
  rcases exists_eq_singleton_of_length_one B₀.steps hsteps with ⟨st, hst⟩
  have hB₀mem : B₀ ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]; exact List.mem_cons_self _ _
  have hspec₀ :=
    blocksOf_entry_spec (freePigeons rho).card rho [] D feed B₀ hB₀mem
  have hunres : pairUnresolvedB B₀.entry e = true :=
    pairUnresolved_of_length_one_undetermined B₀.entry e
      (by simpa [hterm] using hspec₀.2.2.1)
      (by simpa [hterm] using hspec₀.2.2.2)
  have hσ : sigmaFull B₀ = [e] :=
    sigmaFull_eq_singleton_of_term_singleton B₀ e hterm hunres
  have hsub :
      pairVertices (sigmaFull B₀) ⊆
        pairVertices (B₀.steps.map VStep.pair) := by
    have halign :=
      (blocksOf_segment_alignment (freePigeons rho).card rho D feed).2
    have hcons :
        List.Pairwise
          (fun B _ =>
            pairVertices (sigmaFull B) ⊆
              pairVertices (B.steps.map VStep.pair))
          (B₀ :: B₁ :: rest) := by
      change List.Pairwise _ (blocksOf (vtrace rho D feed)) at halign
      rwa [hblocks] at halign
    exact (List.pairwise_cons.mp hcons).1 B₁ (List.mem_cons_self _ _)
  have hwalk : B₀.steps.map VStep.pair = [st.pair] := by
    simp [hst]
  have hpd_σ : List.Pairwise PairDisjoint (sigmaFull B₀) :=
    sigmaFull_pairwise B₀ hspec₀.2.1
  have hnd_σ : (sigmaFull B₀).Nodup := sigmaFull_nodup B₀
  have hcard_σ :
      (pairVertices (sigmaFull B₀)).card = 2 := by
    rw [pairVertices_card_of_disjoint _ hnd_σ hpd_σ, hσ]
    simp
  have hset :
      pairVertices (sigmaFull B₀) =
        pairVertices (B₀.steps.map VStep.pair) := by
    have hle := Finset.card_le_card hsub
    have hcard_w := pairVertices_card_le (B₀.steps.map VStep.pair)
    have hcard_w' : (pairVertices (B₀.steps.map VStep.pair)).card ≤ 2 := by
      simpa [hwalk, List.length_singleton] using hcard_w
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have hpairs : e = st.pair :=
    pairs_eq_of_pairVertices_eq_singletons e st.pair (by
      simpa [hσ, hwalk] using hset)
  simp [hwalk, hσ, hpairs]

/-- **S2202 width-≤1 barrier.**  On every DNF whose terms have length ≤ 1,
no `t = 2` encode image has entered-term length 2. -/
theorem enteredTermsOf_length_ne_two_of_width_le_one_t_two {p h : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho)
    (hw : ∀ term ∈ D, term.length ≤ 1)
    (ht : 2 ≤ vmdtDepth (canonicalVMDT D rho)) :
    (enteredTermsOf rho D 2).length ≠ 2 := by
  intro hlen
  let feed := leftmostLiveDeepFeed rho D 2
  have hlenB : (blocksOf (vtrace rho D feed)).length = 2 := by
    simpa [enteredTermsOf, feed, List.length_map] using hlen
  have hsteps_len :
      (eventsSteps (vtrace rho D feed)).length = 2 :=
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
    exact blocksOf_vevents_steps_ne_nil (freePigeons rho).card rho [] D feed
      B hB
  match hblocks : blocksOf (vtrace rho D feed) with
  | [] =>
      simp [hblocks] at hlenB
  | [B] =>
      simp [hblocks] at hlenB
  | B₀ :: B₁ :: rest =>
      have hlen_rest : rest = [] := by
        have : (B₀ :: B₁ :: rest).length = 2 := by
          simpa [hblocks] using hlenB
        simp only [List.length_cons] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hlen_rest
      have hjoin_len :
          (B₀.steps ++ B₁.steps).length = 2 := by
        have hpart' :
            eventsSteps (vtrace rho D feed) =
              (B₀.steps ++ B₁.steps) := by
          rw [hpart, hblocks]
          simp
        rw [← hpart']
        exact hsteps_len
      have hs0 : B₀.steps ≠ [] := by
        apply hne
        rw [hblocks]
        simp
      have hs1 : B₁.steps ≠ [] := by
        apply hne
        rw [hblocks]
        simp
      have hpos0 : 0 < B₀.steps.length := List.length_pos_of_ne_nil hs0
      have hpos1 : 0 < B₁.steps.length := List.length_pos_of_ne_nil hs1
      have h1step0 : B₀.steps.length = 1 := by
        rw [List.length_append] at hjoin_len
        omega
      have hB₀mem : B₀ ∈ blocksOf (vtrace rho D feed) := by
        rw [hblocks]; exact List.mem_cons_self _ _
      have hspec₀ :=
        blocksOf_entry_spec (freePigeons rho).card rho [] D feed B₀ hB₀mem
      have hterm_mem : B₀.term ∈ D := by
        rcases blocksOf_entered_first (freePigeons rho).card rho [] D feed
            hrho B₀ hB₀mem with ⟨pre, suf, hD, _⟩
        rw [hD]
        exact List.mem_append_right _ (List.mem_cons_self _ _)
      have hw0 : B₀.term.length ≤ 1 := hw _ hterm_mem
      have hw0' : B₀.term.length = 1 := by
        have hpos : 0 < B₀.term.length := by
          cases ht0 : B₀.term with
          | nil =>
              have hsat : termSatisfiedB B₀.entry [] = true := by
                unfold termSatisfiedB; simp
              have hnsat := hspec₀.2.2.2
              rw [ht0] at hnsat
              exact absurd hsat (by simpa using hnsat)
          | cons _ _ => simp
        omega
      have hwalk :
          B₀.steps.map VStep.pair = sigmaFull B₀ :=
        first_block_walked_eq_sigmaFull_of_width_one_one_step rho D feed hrho
          B₀ B₁ [] hblocks hw0' h1step0
      have hpath :
          B₁.entry =
            compose B₀.entry
              (pairsToMatching (B₀.steps.map VStep.pair)) :=
        second_block_entry_eq_compose_first_steps rho D feed B₀ B₁ [] hblocks
      have hne_σ :
          B₁.entry ≠
            compose B₀.entry (pairsToMatching (sigmaFull B₀)) :=
        second_block_entry_ne_compose_entry_sigmaFull rho D feed hrho
          B₀ B₁ [] hblocks
      exact hne_σ (by rw [← hwalk]; exact hpath)

theorem enteredTermsOf_length_le_one_of_width_le_one_t_two {p h : Nat}
    (hsq : p = h) (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho)
    (hw : ∀ term ∈ D, term.length ≤ 1)
    (ht : 2 ≤ vmdtDepth (canonicalVMDT D rho)) :
    (enteredTermsOf rho D 2).length ≤ 1 := by
  have hle := enteredTermsOf_length_le_t hsq rho D hrho ht
  have hne :=
    enteredTermsOf_length_ne_two_of_width_le_one_t_two hsq rho D hrho hw ht
  omega

/-! ### Fin-3 search package -/

/-- Search DNF on Fin 3: three width-1 diagonal terms. -/
def searchD3 : MDNF 3 3 :=
  [[((0 : Fin 3), (0 : Fin 3))],
    [((1 : Fin 3), (1 : Fin 3))],
    [((2 : Fin 3), (2 : Fin 3))]]

theorem searchD3_width_le_one : ∀ term ∈ searchD3, term.length ≤ 1 := by
  intro term ht
  have ht' :
      term = [((0 : Fin 3), (0 : Fin 3))] ∨
        term = [((1 : Fin 3), (1 : Fin 3))] ∨
          term = [((2 : Fin 3), (2 : Fin 3))] := by
    simpa [searchD3] using ht
  rcases ht' with h | h | h <;> subst h <;> decide

theorem searchD3_width : ∀ term ∈ searchD3, term.length ≤ 3 := by
  intro term ht
  exact Nat.le_trans (searchD3_width_le_one term ht) (by decide)

/-- Path-exit collision predicate on genuine encode preimages (`w = 3`). -/
def isPathExitCollision {ell t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) : Prop :=
  encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₁ searchD3 hrho₁ hell₁ ht₁ searchD3_width =
    encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₂ searchD3 hrho₂ hell₂ ht₂ searchD3_width ∧
    firstBlockPathExitMatching rho₁ searchD3 t ≠
      firstBlockPathExitMatching rho₂ searchD3 t

/-- Entered-term collision predicate (Fin 3 / `searchD3`). -/
def isEnteredTermsCollision3 {ell t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) : Prop :=
  encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₁ searchD3 hrho₁ hell₁ ht₁ searchD3_width =
    encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₂ searchD3 hrho₂ hell₂ ht₂ searchD3_width ∧
    enteredTermsOf rho₁ searchD3 t ≠ enteredTermsOf rho₂ searchD3 t

/-! ### Free-count barriers on Fin 3 -/

theorem not_depth_eligible_of_free_lt_t_gen {p h ell t : Nat}
    (D : MDNF p h) (rho : MatchingMap p h)
    (hell : (freePigeons rho).card = ell) (hlt : ell < t) :
    ¬ t ≤ vmdtDepth (canonicalVMDT D rho) := by
  intro ht
  have hle := vmdtDepth_canonicalVMDT_le_freePigeons D rho
  omega

/-- The only free-count-3 matching on Fin 3 is the empty matching. -/
theorem unique_ell_three (rho : MatchingMap 3 3) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = 3) :
    rho = emptyMatching 3 3 := by
  funext i
  have hcard : (freePigeons rho).card = Fintype.card (Fin 3) := by
    simpa [Fintype.card_fin] using hell
  have huni : freePigeons rho = (Finset.univ : Finset (Fin 3)) := by
    apply Finset.eq_univ_of_card
    simpa [Fintype.card_fin] using hell
  have hi : i ∈ freePigeons rho := by
    rw [huni]; exact Finset.mem_univ _
  exact (mem_freePigeons rho i).mp hi

theorem no_path_exit_collision_ell_three {t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 3)
    (hell₂ : (freePigeons rho₂).card = 3)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) :
    ¬ isPathExitCollision (t := t) (ell := 3)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨_, hexit⟩
  have h1 := unique_ell_three rho₁ hrho₁ hell₁
  have h2 := unique_ell_three rho₂ hrho₂ hell₂
  exact hexit (by rw [h1, h2])

theorem no_entered_terms_collision_ell_three {t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 3)
    (hell₂ : (freePigeons rho₂).card = 3)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) :
    ¬ isEnteredTermsCollision3 (t := t) (ell := 3)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨_, hterms⟩
  have h1 := unique_ell_three rho₁ hrho₁ hell₁
  have h2 := unique_ell_three rho₂ hrho₂ hell₂
  exact hterms (by rw [h1, h2])

theorem not_depth_eligible_ell_lt_two_t_two (rho : MatchingMap 3 3)
    {ell : Nat} (hell : (freePigeons rho).card = ell) (hle : ell ≤ 1) :
    ¬ 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho) :=
  not_depth_eligible_of_free_lt_t_gen searchD3 rho hell (by omega)

theorem no_path_exit_collision_ell_lt_two_t_two
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    {ell : Nat}
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (hle : ell ≤ 1)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) :
    ¬ isPathExitCollision (t := 2) (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ :=
  (not_depth_eligible_ell_lt_two_t_two rho₁ hell₁ hle ht₁).elim

/-! ### t = 2 residual discharge on `searchD3` -/

theorem enteredTermsOf_length_le_one_searchD3_t_two
    {ell : Nat} (rho : MatchingMap 3 3) (hrho : IsMatching rho)
    (hell : (freePigeons rho).card = ell)
    (ht : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho)) :
    (enteredTermsOf rho searchD3 2).length ≤ 1 :=
  enteredTermsOf_length_le_one_of_width_le_one_t_two rfl rho searchD3 hrho
    searchD3_width_le_one ht

/-- **S2202:** on Fin 3 / `searchD3` / `t = 2`, equal codes force equal
entered-term sequences (length-≤1 residual via the width-1 barrier). -/
theorem encodeMatchEnteredTermsEqResidual_searchD3_t_two {ell : Nat} :
    EncodeMatchEnteredTermsEqResidual (p := 3) (h := 3) (w := 3) (t := 2)
      (ell := ell) rfl searchD3 searchD3_width :=
  encodeMatchEnteredTermsEqResidual_of_length_le_one rfl searchD3
    searchD3_width
    (fun rho hrho hell ht =>
      enteredTermsOf_length_le_one_searchD3_t_two (ell := ell) rho hrho hell
        ht)

/-- **S2202:** length-2 exit residual holds vacuously on this package (no
length-2 encode image under width ≤ 1 at `t = 2`). -/
theorem encodeMatchLengthTwoExitEqResidual_searchD3_t_two {ell : Nat} :
    EncodeMatchLengthTwoExitEqResidual (p := 3) (h := 3) (w := 3) (t := 2)
      (ell := ell) rfl searchD3 searchD3_width := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode hlen
  have hle :=
    enteredTermsOf_length_le_one_searchD3_t_two (ell := ell) rho₁ hrho₁
      hell₁ ht₁
  omega

/-- Equal codes force equal path exits on Fin 3 / `searchD3` / `t = 2`. -/
theorem firstBlockPathExitMatching_eq_of_encodeMatch_eq_searchD3_t_two
    {ell : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₂))
    (hcode :
      encodeMatch (p := 3) (h := 3) (w := 3) (t := 2) (ell := ell) rfl
        rho₁ searchD3 hrho₁ hell₁ ht₁ searchD3_width =
      encodeMatch (p := 3) (h := 3) (w := 3) (t := 2) (ell := ell) rfl
        rho₂ searchD3 hrho₂ hell₂ ht₂ searchD3_width) :
    firstBlockPathExitMatching rho₁ searchD3 2 =
      firstBlockPathExitMatching rho₂ searchD3 2 := by
  have hterms :
      enteredTermsOf rho₁ searchD3 2 = enteredTermsOf rho₂ searchD3 2 :=
    encodeMatchEnteredTermsEqResidual_searchD3_t_two (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode
  have hrho :
      rho₁ = rho₂ :=
    encodeMatch_eq_of_code_eq_of_entered_terms_eq rfl
      rho₁ rho₂ searchD3 hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ searchD3_width
      hcode (by simpa [enteredTermsOf] using hterms)
  simp [hrho]

theorem no_path_exit_collision_searchD3_t_two {ell : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) :
    ¬ isPathExitCollision (t := 2) (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨hcode, hexit⟩
  exact hexit
    (firstBlockPathExitMatching_eq_of_encodeMatch_eq_searchD3_t_two
      (ell := ell) rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode)

theorem no_entered_terms_collision_searchD3_t_two {ell : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
    (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)) :
    ¬ isEnteredTermsCollision3 (t := 2) (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨hcode, hterms⟩
  exact hterms
    (encodeMatchEnteredTermsEqResidual_searchD3_t_two (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode)

/-- **S2202 collision-search summary (Fin 3 / `searchD3` / `t = 2`).**

* Width-≤1 barrier: no length-2 encode image (`enteredTermsOf_length_ne_two_of_width_le_one_t_two`).
* `ell = 3`: unique empty preimage ⇒ no collision.
* `ell ≤ 1`: empty depth-eligible slice.
* Every free-count: equal codes ⇒ equal entered terms (length-≤1 residual)
  and equal path exits; no path-exit collision witness.
* `EncodeMatchLengthTwoExitEqResidual` discharged vacuously on this package.
* No bank stop-loss.  DNF fixed to `searchD3`; multi-block `t ≥ 3` remains open.
-/
theorem collision_search_fin3_t_two_summary :
    (∀ term ∈ searchD3, term.length ≤ 1) ∧
      (∀ (rho : MatchingMap 3 3) (hrho : IsMatching rho),
        (freePigeons rho).card = 3 → rho = emptyMatching 3 3) ∧
      (∀ (rho : MatchingMap 3 3) (ell : Nat),
        (freePigeons rho).card = ell → ell ≤ 1 →
          ¬ 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho)) ∧
      (∀ (ell : Nat) (rho : MatchingMap 3 3)
        (hrho : IsMatching rho)
        (hell : (freePigeons rho).card = ell)
        (ht : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho)),
        (enteredTermsOf rho searchD3 2).length ≤ 1) ∧
      (∀ (ell : Nat),
        EncodeMatchLengthTwoExitEqResidual (p := 3) (h := 3) (w := 3)
          (t := 2) (ell := ell) rfl searchD3 searchD3_width) ∧
      (∀ (ell : Nat),
        EncodeMatchEnteredTermsEqResidual (p := 3) (h := 3) (w := 3)
          (t := 2) (ell := ell) rfl searchD3 searchD3_width) ∧
      (∀ (ell : Nat) (rho₁ rho₂ : MatchingMap 3 3)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = ell)
        (hell₂ : (freePigeons rho₂).card = ell)
        (ht₁ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₁))
        (ht₂ : 2 ≤ vmdtDepth (canonicalVMDT searchD3 rho₂)),
        ¬ isPathExitCollision (t := 2) (ell := ell)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) :=
  ⟨searchD3_width_le_one,
    fun rho hrho hell => unique_ell_three rho hrho hell,
    fun rho _ell hell hle =>
      not_depth_eligible_ell_lt_two_t_two rho hell hle,
    fun ell rho hrho hell ht =>
      enteredTermsOf_length_le_one_searchD3_t_two (ell := ell) rho hrho hell
        ht,
    fun ell => encodeMatchLengthTwoExitEqResidual_searchD3_t_two (ell := ell),
    fun ell => encodeMatchEnteredTermsEqResidual_searchD3_t_two (ell := ell),
    fun ell rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ =>
      no_path_exit_collision_searchD3_t_two (ell := ell)
        rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂⟩

/-! ## S2203: width≥2 length-2 path-exit collision gate (non-vacuous)

Board `Fin 3`, search DNF `searchDw2` with a genuine width-2 first term
`[(0,1),(1,0)]` and closer `[(2,2)]`.  Under the empty matching the
leftmost live depth-3 path:

1. enters the width-2 term and walks pairs `(0,0),(1,1)` (two steps);
2. path-exit falsifies that term and opens the closer (one step).

Entered-term length is therefore 2.  Honest bounds:

* free-count `ell = 3`: unique empty matching ⇒ no collision;
* free-count `ell < 3` at `t = 3`: empty depth-eligible slice
  (`depth ≤ freePigeons`);
* residuals discharge by unique-preimage on the only eligible free-count
  (non-vacuous: a length-2 image exists);
* no bank stop-loss.  Packet-only walked-pair recovery remains open outside
  unique-preimage packages.
-/

/-- Width-2 first term of the S2203 search family. -/
def termW2 : MTerm 3 3 :=
  [((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (0 : Fin 3))]

/-- Width-1 closer of the S2203 search family. -/
def termW2close : MTerm 3 3 := [((2 : Fin 3), (2 : Fin 3))]

/-- Search DNF on Fin 3 with a genuine width-2 first term. -/
def searchDw2 : MDNF 3 3 := [termW2, termW2close]

theorem searchDw2_eq : searchDw2 = [termW2, termW2close] := rfl

theorem termW2_length : termW2.length = 2 := rfl

theorem searchDw2_has_width_ge_two : ∃ term ∈ searchDw2, 2 ≤ term.length :=
  ⟨termW2, by simp [searchDw2], by simp [termW2_length]⟩

theorem searchDw2_width : ∀ term ∈ searchDw2, term.length ≤ 3 := by
  intro term ht
  have ht' : term = termW2 ∨ term = termW2close := by
    simpa [searchDw2] using ht
  rcases ht' with h | h <;> subst h <;> decide

theorem searchDw2_width_le_two : ∀ term ∈ searchDw2, term.length ≤ 2 := by
  intro term ht
  have ht' : term = termW2 ∨ term = termW2close := by
    simpa [searchDw2] using ht
  rcases ht' with h | h <;> subst h <;> decide

private theorem freePigeons_empty3 :
    (freePigeons (emptyMatching 3 3)).card = 3 := by
  have h : freePigeons (emptyMatching 3 3) =
      (Finset.univ : Finset (Fin 3)) := by
    ext i; simp [freePigeons, emptyMatching]
  rw [h, Finset.card_univ, Fintype.card_fin]

private theorem finList_3 : finList 3 = [(0 : Fin 3), 1, 2] := by
  unfold finList
  simp [List.range_succ, List.range_zero]

private theorem termW2_legal : termMatchingLegalB termW2 = true := by
  unfold termW2 termMatchingLegalB hasDupB
  decide

private theorem termW2close_legal : termMatchingLegalB termW2close = true := by
  unfold termW2close termMatchingLegalB hasDupB
  decide

/-- Path matching after the first walked pair of the S2203 witness. -/
private def muW2_1 : MatchingMap 3 3 :=
  compose (emptyMatching 3 3) (singleMatching (0 : Fin 3) 0)

/-- Path matching after both walked pairs of the first S2203 block. -/
private def muW2_2 : MatchingMap 3 3 :=
  compose muW2_1 (singleMatching (1 : Fin 3) 1)

private theorem muW2_1_apply :
    muW2_1 = fun i => if i = (0 : Fin 3) then some (0 : Fin 3) else none := by
  funext i
  simp [muW2_1, compose, singleMatching, emptyMatching]

private theorem muW2_2_apply :
    muW2_2 = fun i =>
      if i = (0 : Fin 3) then some (0 : Fin 3)
      else if i = (1 : Fin 3) then some (1 : Fin 3) else none := by
  funext i
  simp [muW2_2, muW2_1, compose, singleMatching, emptyMatching]
  split_ifs <;> simp_all

private theorem holeUsed_empty (a : Fin 3) :
    holeUsed (emptyMatching 3 3) a = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩
  simp [emptyMatching] at hi

private theorem holeUsed_muW2_1_0 : holeUsed muW2_1 (0 : Fin 3) = true := by
  rw [holeUsed_eq_true_iff]
  exact ⟨0, by simp [muW2_1_apply]⟩

private theorem holeUsed_muW2_1_1 : holeUsed muW2_1 (1 : Fin 3) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [muW2_1_apply] at hi

private theorem holeUsed_muW2_1_2 : holeUsed muW2_1 (2 : Fin 3) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [muW2_1_apply] at hi

private theorem holeUsed_muW2_2_0 : holeUsed muW2_2 (0 : Fin 3) = true := by
  rw [holeUsed_eq_true_iff]
  exact ⟨0, by simp [muW2_2_apply]⟩

private theorem holeUsed_muW2_2_1 : holeUsed muW2_2 (1 : Fin 3) = true := by
  rw [holeUsed_eq_true_iff]
  exact ⟨1, by simp [muW2_2_apply]⟩

private theorem holeUsed_muW2_2_2 : holeUsed muW2_2 (2 : Fin 3) = false := by
  rw [Bool.eq_false_iff, ne_eq, holeUsed_eq_true_iff]
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [muW2_2_apply] at hi

private theorem termW2_not_fals_empty :
    termFalsifiedB (emptyMatching 3 3) termW2 = false := by
  unfold termFalsifiedB termW2 pairFalsB
  simp [emptyMatching, holeUsed_empty]

private theorem termW2_not_sat_empty :
    termSatisfiedB (emptyMatching 3 3) termW2 = false := by
  unfold termSatisfiedB termW2 pairSatB
  simp [emptyMatching]

private theorem termVertices_empty_termW2 :
    termVertices (emptyMatching 3 3) termW2 =
      [Sum.inl (0 : Fin 3), Sum.inr (1 : Fin 3),
        Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] := by
  unfold termVertices termW2 pairUnresolvedB
  simp [emptyMatching, holeUsed_empty]

private theorem vertexCovered_muW2_1_inr1 :
    vertexCoveredB muW2_1 (Sum.inr (1 : Fin 3)) = false := by
  simp [vertexCoveredB, holeUsed_muW2_1_1]

private theorem vertexCovered_muW2_2_inl1 :
    vertexCoveredB muW2_2 (Sum.inl (1 : Fin 3)) = true := by
  simp [vertexCoveredB, muW2_2_apply]

private theorem vertexCovered_muW2_2_inr0 :
    vertexCoveredB muW2_2 (Sum.inr (0 : Fin 3)) = true := by
  simp [vertexCoveredB, holeUsed_muW2_2_0]

private theorem termW2_fals_muW2_2 :
    termFalsifiedB muW2_2 termW2 = true := by
  unfold termFalsifiedB termW2 pairFalsB
  simp [muW2_2_apply]

private theorem termW2close_not_fals_muW2_2 :
    termFalsifiedB muW2_2 termW2close = false := by
  unfold termFalsifiedB termW2close pairFalsB
  have h2 : muW2_2 (2 : Fin 3) = none := by simp [muW2_2_apply]
  simp [h2, holeUsed_muW2_2_2]

private theorem termW2close_not_sat_muW2_2 :
    termSatisfiedB muW2_2 termW2close = false := by
  unfold termSatisfiedB termW2close pairSatB
  have h2 : muW2_2 (2 : Fin 3) = none := by simp [muW2_2_apply]
  simp [h2]

private theorem termVertices_muW2_2_termW2close :
    termVertices muW2_2 termW2close =
      [Sum.inl (2 : Fin 3), Sum.inr (2 : Fin 3)] := by
  unfold termVertices termW2close pairUnresolvedB
  have h2 : muW2_2 (2 : Fin 3) = none := by simp [muW2_2_apply]
  simp [h2, holeUsed_muW2_2_2]

private theorem muW2_2_two_isNone : (muW2_2 (2 : Fin 3)).isSome = false := by
  simp [muW2_2_apply]

/-! ### Depth ≥ 3 for empty / `searchDw2` -/

private theorem vwalk_muW2_2_termW2close :
    vwalkAux 1 muW2_2 [] [termW2close] =
      .pquery (2 : Fin 3) (fun a =>
        if holeUsed muW2_2 a = true then .leaf false
        else vwalkAux 0 (compose muW2_2 (singleMatching (2 : Fin 3) a))
          [Sum.inr (2 : Fin 3)] [termW2close]) := by
  simpa [termVertices_muW2_2_termW2close] using
    (vwalk_entry_pigeon (fuel' := 0) muW2_2 termW2close [] (2 : Fin 3)
      [Sum.inr (2 : Fin 3)] termW2close_legal termW2close_not_fals_muW2_2
      termW2close_not_sat_muW2_2 termVertices_muW2_2_termW2close)

private theorem vwalk_muW2_2_searchDw2 :
    vwalkAux 1 muW2_2 [] searchDw2 = vwalkAux 1 muW2_2 [] [termW2close] := by
  rw [searchDw2_eq]
  exact vwalk_skip_falsified 1 muW2_2 termW2 [termW2close]
    termW2_legal termW2_fals_muW2_2

private theorem depth_muW2_2_searchDw2 :
    1 ≤ vmdtDepth (vwalkAux 1 muW2_2 [] searchDw2) := by
  rw [vwalk_muW2_2_searchDw2, vwalk_muW2_2_termW2close, vmdtDepth_pquery]
  exact Nat.le_add_right 1 _

private theorem vwalk_muW2_2_pending :
    vwalkAux 1 muW2_2
        [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2 =
      vwalkAux 1 muW2_2 [] searchDw2 := by
  rw [vblock_skip_covered 1 muW2_2 (Sum.inl (1 : Fin 3))
    [Sum.inr (0 : Fin 3)] searchDw2 vertexCovered_muW2_2_inl1]
  exact vblock_skip_covered 1 muW2_2 (Sum.inr (0 : Fin 3)) [] searchDw2
    vertexCovered_muW2_2_inr0

private theorem depth_muW2_2_pending :
    1 ≤ vmdtDepth
      (vwalkAux 1 muW2_2
        [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2) := by
  rw [vwalk_muW2_2_pending]
  exact depth_muW2_2_searchDw2

private theorem vwalk_muW2_1_pending :
    vwalkAux 2 muW2_1
        [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
        searchDw2 =
      .hquery (1 : Fin 3) (fun q =>
        if (muW2_1 q).isSome = true then .leaf false
        else vwalkAux 1 (compose muW2_1 (singleMatching q (1 : Fin 3)))
          [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2) := by
  simpa using
    (vblock_query_hole (fuel' := 1) muW2_1 (1 : Fin 3)
      [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2
      vertexCovered_muW2_1_inr1)

private theorem depth_muW2_1_pending :
    2 ≤ vmdtDepth
      (vwalkAux 2 muW2_1
        [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
        searchDw2) := by
  rw [vwalk_muW2_1_pending, vmdtDepth_hquery]
  let child : Fin 3 → VMDTree 3 3 := fun q =>
    if (muW2_1 q).isSome = true then .leaf false
    else vwalkAux 1 (compose muW2_1 (singleMatching q (1 : Fin 3)))
      [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2
  have hq : (muW2_1 (1 : Fin 3)).isSome = false := by simp [muW2_1_apply]
  have hchild : 1 ≤ vmdtDepth (child 1) := by
    simp only [child, hq]
    simpa [muW2_2] using depth_muW2_2_pending
  have hle : vmdtDepth (child 1) ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) :=
    Finset.le_sup (f := fun q => vmdtDepth (child q)) (Finset.mem_univ (1 : Fin 3))
  have : 1 ≤ Finset.univ.sup (fun q => vmdtDepth (child q)) :=
    le_trans hchild hle
  simpa [child] using Nat.add_le_add_left this 1

private theorem vwalk_empty_searchDw2 :
    vwalkAux 3 (emptyMatching 3 3) [] searchDw2 =
      .pquery (0 : Fin 3) (fun a =>
        if holeUsed (emptyMatching 3 3) a = true then .leaf false
        else vwalkAux 2
          (compose (emptyMatching 3 3) (singleMatching (0 : Fin 3) a))
          [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
          searchDw2) := by
  rw [searchDw2_eq]
  simpa [termVertices_empty_termW2] using
    (vwalk_entry_pigeon (fuel' := 2) (emptyMatching 3 3) termW2 [termW2close]
      (0 : Fin 3)
      [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
      termW2_legal termW2_not_fals_empty termW2_not_sat_empty
      termVertices_empty_termW2)

/-- Canonical depth of empty / `searchDw2` is at least 3. -/
theorem searchDw2_empty_depth_ge_three :
    3 ≤ vmdtDepth (canonicalVMDT searchDw2 (emptyMatching 3 3)) := by
  unfold canonicalVMDT
  rw [freePigeons_empty3, vwalk_empty_searchDw2, vmdtDepth_pquery]
  let child : Fin 3 → VMDTree 3 3 := fun a =>
    if holeUsed (emptyMatching 3 3) a = true then .leaf false
    else vwalkAux 2
      (compose (emptyMatching 3 3) (singleMatching (0 : Fin 3) a))
      [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
      searchDw2
  have hchild : 2 ≤ vmdtDepth (child 0) := by
    simp only [child, holeUsed_empty]
    simpa [muW2_1] using depth_muW2_1_pending
  have hle : vmdtDepth (child 0) ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) :=
    Finset.le_sup (f := fun a => vmdtDepth (child a)) (Finset.mem_univ (0 : Fin 3))
  have : 2 ≤ Finset.univ.sup (fun a => vmdtDepth (child a)) :=
    le_trans hchild hle
  simpa [child] using Nat.add_le_add_left this 1

/-! ### Leftmost live feed = `[inr 0, inl 1, inr 2]` -/

private theorem liveHole_empty_s2_0 :
    liveHoleDepthB (emptyMatching 3 3) (0 : Fin 3) 2
      [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
      searchDw2 2 (0 : Fin 3) = true := by
  unfold liveHoleDepthB
  rw [if_pos (holeUsed_empty 0)]
  exact decide_eq_true (by
    simpa [muW2_1] using depth_muW2_1_pending)

private theorem leftmostLiveDepthHole_empty_s2 :
    leftmostLiveDepthHole? (emptyMatching 3 3) (0 : Fin 3) 2
      [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
      searchDw2 2 = some (0 : Fin 3) := by
  unfold leftmostLiveDepthHole?
  rw [finList_3]
  simp [List.find?_cons, liveHole_empty_s2_0]

private theorem livePigeon_muW2_1_s1_1 :
    livePigeonDepthB muW2_1 (1 : Fin 3) 1
      [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2 1
      (1 : Fin 3) = true := by
  unfold livePigeonDepthB
  have hq : (muW2_1 (1 : Fin 3)).isSome = false := by simp [muW2_1_apply]
  rw [if_pos hq]
  exact decide_eq_true (by simpa [muW2_2] using depth_muW2_2_pending)

private theorem livePigeon_muW2_1_s1_0 :
    livePigeonDepthB muW2_1 (1 : Fin 3) 1
      [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2 1
      (0 : Fin 3) = false := by
  unfold livePigeonDepthB
  have hq : (muW2_1 (0 : Fin 3)).isSome = true := by simp [muW2_1_apply]
  simp [hq]

private theorem leftmostLiveDepthPigeon_muW2_1_s1 :
    leftmostLiveDepthPigeon? muW2_1 (1 : Fin 3) 1
      [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2 1 =
      some (1 : Fin 3) := by
  unfold leftmostLiveDepthPigeon?
  rw [finList_3]
  simp [List.find?_cons, livePigeon_muW2_1_s1_0, livePigeon_muW2_1_s1_1]

private theorem liveHole_muW2_2_s0_2 :
    liveHoleDepthB muW2_2 (2 : Fin 3) 0
      [Sum.inr (2 : Fin 3)] [termW2close] 0 (2 : Fin 3) = true := by
  unfold liveHoleDepthB
  rw [if_pos holeUsed_muW2_2_2]
  exact decide_eq_true (Nat.zero_le _)

private theorem liveHole_muW2_2_s0_0 :
    liveHoleDepthB muW2_2 (2 : Fin 3) 0
      [Sum.inr (2 : Fin 3)] [termW2close] 0 (0 : Fin 3) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muW2_2_0]

private theorem liveHole_muW2_2_s0_1 :
    liveHoleDepthB muW2_2 (2 : Fin 3) 0
      [Sum.inr (2 : Fin 3)] [termW2close] 0 (1 : Fin 3) = false := by
  unfold liveHoleDepthB
  simp [holeUsed_muW2_2_1]

private theorem leftmostLiveDepthHole_muW2_2_s0 :
    leftmostLiveDepthHole? muW2_2 (2 : Fin 3) 0
      [Sum.inr (2 : Fin 3)] [termW2close] 0 = some (2 : Fin 3) := by
  unfold leftmostLiveDepthHole?
  rw [finList_3]
  simp [List.find?_cons, liveHole_muW2_2_s0_0, liveHole_muW2_2_s0_1,
    liveHole_muW2_2_s0_2]

private theorem leftmostLiveFeedAux_muW2_2_close :
    leftmostLiveFeedAux 1 muW2_2 [] [termW2close] 1 =
      [Sum.inr (2 : Fin 3)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp only [Nat.add_eq, Nat.add_zero]
  -- s+1 = 1 ⇒ s = 0 branch
  have hleg := termW2close_legal
  have hfals := termW2close_not_fals_muW2_2
  have hsat := termW2close_not_sat_muW2_2
  have htv := termVertices_muW2_2_termW2close
  have hleft := leftmostLiveDepthHole_muW2_2_s0
  -- Unfold one step: enter term, answer hole 2, then fuel 0 rest is []
  simp [hleg, hfals, hsat, htv, hleft, leftmostLiveFeedAux]

private theorem leftmostLiveFeedAux_muW2_2_search :
    leftmostLiveFeedAux 1 muW2_2 [] searchDw2 1 =
      [Sum.inr (2 : Fin 3)] := by
  rw [searchDw2_eq, leftmostLiveFeedAux.eq_def]
  simp [termW2_legal, termW2_fals_muW2_2, leftmostLiveFeedAux_muW2_2_close]

private theorem leftmostLiveFeedAux_muW2_2_pending :
    leftmostLiveFeedAux 1 muW2_2
        [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] searchDw2 1 =
      [Sum.inr (2 : Fin 3)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muW2_2_inl1]
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muW2_2_inr0, leftmostLiveFeedAux_muW2_2_search]

private theorem leftmostLiveFeedAux_muW2_1_pending :
    leftmostLiveFeedAux 2 muW2_1
        [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
        searchDw2 2 =
      [Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)] := by
  rw [leftmostLiveFeedAux.eq_def]
  simp [vertexCovered_muW2_1_inr1, leftmostLiveDepthPigeon_muW2_1_s1]
  -- after answering pigeon 1 for hole 1, state is muW2_2 pending
  exact leftmostLiveFeedAux_muW2_2_pending

private theorem leftmostLiveFeed_empty_searchDw2_three :
    leftmostLiveFeed (emptyMatching 3 3) searchDw2 3 =
      [Sum.inr (0 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)] := by
  unfold leftmostLiveFeed
  rw [freePigeons_empty3]
  -- Expand aux at fuel 3 / empty / [] / searchDw2 / 3
  have hstep :
      leftmostLiveFeedAux 3 (emptyMatching 3 3) [] searchDw2 3 =
        Sum.inr (0 : Fin 3) ::
          leftmostLiveFeedAux 2 muW2_1
            [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
            searchDw2 2 := by
    rw [searchDw2_eq, leftmostLiveFeedAux.eq_def]
    simp only [termW2_legal, termW2_not_fals_empty, termW2_not_sat_empty,
      termVertices_empty_termW2, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
    have hL :
        leftmostLiveDepthHole? (emptyMatching 3 3) (0 : Fin 3) 2
          [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
          [termW2, termW2close] 2 = some (0 : Fin 3) := by
      simpa [searchDw2] using leftmostLiveDepthHole_empty_s2
    simp [hL, muW2_1]
  rw [hstep, leftmostLiveFeedAux_muW2_1_pending]

theorem leftmostLiveDeepFeed_empty_searchDw2_three :
    leftmostLiveDeepFeed (emptyMatching 3 3) searchDw2 3 =
      [Sum.inr (0 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)] := by
  unfold leftmostLiveDeepFeed
  exact leftmostLiveFeed_empty_searchDw2_three

/-! ### Trace / blocks / entered-term length 2 -/

private theorem vtrace_empty_searchDw2_three :
    vtrace (emptyMatching 3 3) searchDw2
        [Sum.inr (0 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)] =
      [.enter termW2 (emptyMatching 3 3),
        .qstep ⟨Sum.inl (0 : Fin 3), ((0 : Fin 3), (0 : Fin 3))⟩,
        .qstep ⟨Sum.inr (1 : Fin 3), ((1 : Fin 3), (1 : Fin 3))⟩,
        .enter termW2close muW2_2,
        .qstep ⟨Sum.inl (2 : Fin 3), ((2 : Fin 3), (2 : Fin 3))⟩] := by
  unfold vtrace
  rw [freePigeons_empty3, searchDw2_eq]
  have htv := termVertices_empty_termW2
  rw [vevents_entry_pigeon_live (fuel' := 2) (emptyMatching 3 3) termW2
    [termW2close] (0 : Fin 3)
    [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
    (0 : Fin 3) [Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)]
    termW2_legal termW2_not_fals_empty termW2_not_sat_empty htv
    (holeUsed_empty 0)]
  -- fold first-step matching to muW2_1
  change
      _ :: _ ::
        vevents 2 muW2_1
          [Sum.inr (1 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
          [termW2, termW2close] [Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)] =
        _
  rw [vevents_block_hole_live (fuel' := 1) muW2_1 (1 : Fin 3)
    [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)] [termW2, termW2close]
    (1 : Fin 3) [Sum.inr (2 : Fin 3)] vertexCovered_muW2_1_inr1
    (by simp [muW2_1_apply])]
  change
      _ :: _ :: _ ::
        vevents 1 muW2_2 [Sum.inl (1 : Fin 3), Sum.inr (0 : Fin 3)]
          [termW2, termW2close] [Sum.inr (2 : Fin 3)] =
        _
  rw [vevents_block_skip_covered 1 muW2_2 (Sum.inl (1 : Fin 3))
    [Sum.inr (0 : Fin 3)] [termW2, termW2close] [Sum.inr (2 : Fin 3)]
    vertexCovered_muW2_2_inl1]
  rw [vevents_block_skip_covered 1 muW2_2 (Sum.inr (0 : Fin 3)) []
    [termW2, termW2close] [Sum.inr (2 : Fin 3)]
    vertexCovered_muW2_2_inr0]
  rw [vevents_skip_falsified 1 muW2_2 termW2 [termW2close]
    [Sum.inr (2 : Fin 3)] termW2_legal termW2_fals_muW2_2]
  rw [vevents_entry_pigeon_live (fuel' := 0) muW2_2 termW2close []
    (2 : Fin 3) [Sum.inr (2 : Fin 3)] (2 : Fin 3) []
    termW2close_legal termW2close_not_fals_muW2_2 termW2close_not_sat_muW2_2
    termVertices_muW2_2_termW2close holeUsed_muW2_2_2]
  have hcov :
      vertexCoveredB
        (compose muW2_2 (singleMatching (2 : Fin 3) 2))
        (Sum.inr (2 : Fin 3)) = true := by
    simp [vertexCoveredB, holeUsed, finList_3, compose, singleMatching,
      muW2_2_apply]
  rw [vevents_block_skip_covered 0 _ _ _ _ _ hcov]
  have hsat :
      termSatisfiedB
        (compose muW2_2 (singleMatching (2 : Fin 3) 2)) termW2close =
        true := by
    unfold termSatisfiedB termW2close pairSatB
    simp [compose, singleMatching, muW2_2_apply]
  have hfals' :
      termFalsifiedB
        (compose muW2_2 (singleMatching (2 : Fin 3) 2)) termW2close =
        false := by
    unfold termFalsifiedB termW2close pairFalsB
    simp [compose, singleMatching, muW2_2_apply, holeUsed, finList_3]
  rw [vevents_stop_satisfied 0 _ _ _ _ termW2close_legal hfals' hsat]

private theorem blocksOf_empty_searchDw2_three :
    blocksOf
        (vtrace (emptyMatching 3 3) searchDw2
          [Sum.inr (0 : Fin 3), Sum.inl (1 : Fin 3), Sum.inr (2 : Fin 3)]) =
      [⟨termW2, emptyMatching 3 3,
          [⟨Sum.inl (0 : Fin 3), ((0 : Fin 3), (0 : Fin 3))⟩,
            ⟨Sum.inr (1 : Fin 3), ((1 : Fin 3), (1 : Fin 3))⟩]⟩,
        ⟨termW2close, muW2_2,
          [⟨Sum.inl (2 : Fin 3), ((2 : Fin 3), (2 : Fin 3))⟩]⟩] := by
  rw [vtrace_empty_searchDw2_three]
  simp [blocksOf, stepsPrefix, afterSteps]

private theorem enteredTermsOf_empty_searchDw2_three :
    enteredTermsOf (emptyMatching 3 3) searchDw2 3 =
      [termW2, termW2close] := by
  simp only [enteredTermsOf, leftmostLiveDeepFeed_empty_searchDw2_three]
  rw [blocksOf_empty_searchDw2_three]
  rfl

/-- **S2203 non-vacuous length-2 witness.**  Empty matching on Fin 3 /
`searchDw2` / `t = 3` yields entered-term length 2, and the DNF has a
width-≥2 term. -/
theorem exists_length_two_encode_image_width_ge_two :
    ∃ (rho : MatchingMap 3 3) (D : MDNF 3 3) (t : Nat),
      IsMatching rho ∧
        (∃ term ∈ D, 2 ≤ term.length) ∧
        t ≤ vmdtDepth (canonicalVMDT D rho) ∧
        (enteredTermsOf rho D t).length = 2 := by
  refine ⟨emptyMatching 3 3, searchDw2, 3,
    isMatching_empty 3 3, searchDw2_has_width_ge_two,
    searchDw2_empty_depth_ge_three, ?_⟩
  rw [enteredTermsOf_empty_searchDw2_three]
  decide

theorem enteredTermsOf_empty_searchDw2_three_length :
    (enteredTermsOf (emptyMatching 3 3) searchDw2 3).length = 2 := by
  rw [enteredTermsOf_empty_searchDw2_three]
  decide

/-! ### Path-exit / entered-term collision predicates on `searchDw2` -/

/-- Path-exit collision predicate on genuine encode preimages (`w = 3`). -/
def isPathExitCollisionW2 {ell t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) : Prop :=
  encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₁ searchDw2 hrho₁ hell₁ ht₁ searchDw2_width =
    encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₂ searchDw2 hrho₂ hell₂ ht₂ searchDw2_width ∧
    firstBlockPathExitMatching rho₁ searchDw2 t ≠
      firstBlockPathExitMatching rho₂ searchDw2 t

/-- Entered-term collision predicate (Fin 3 / `searchDw2`). -/
def isEnteredTermsCollisionW2 {ell t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) : Prop :=
  encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₁ searchDw2 hrho₁ hell₁ ht₁ searchDw2_width =
    encodeMatch (p := 3) (h := 3) (w := 3) (t := t) (ell := ell) rfl
      rho₂ searchDw2 hrho₂ hell₂ ht₂ searchDw2_width ∧
    enteredTermsOf rho₁ searchDw2 t ≠ enteredTermsOf rho₂ searchDw2 t

/-! ### Free-count barriers at `t = 3` -/

theorem not_depth_eligible_ell_lt_three_t_three (rho : MatchingMap 3 3)
    {ell : Nat} (hell : (freePigeons rho).card = ell) (hle : ell ≤ 2) :
    ¬ 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho) :=
  not_depth_eligible_of_free_lt_t_gen searchDw2 rho hell (by omega)

theorem no_path_exit_collision_searchDw2_ell_three {t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 3)
    (hell₂ : (freePigeons rho₂).card = 3)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) :
    ¬ isPathExitCollisionW2 (t := t) (ell := 3)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨_, hexit⟩
  have h1 := unique_ell_three rho₁ hrho₁ hell₁
  have h2 := unique_ell_three rho₂ hrho₂ hell₂
  exact hexit (by rw [h1, h2])

theorem no_entered_terms_collision_searchDw2_ell_three {t : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = 3)
    (hell₂ : (freePigeons rho₂).card = 3)
    (ht₁ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : t ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) :
    ¬ isEnteredTermsCollisionW2 (t := t) (ell := 3)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨_, hterms⟩
  have h1 := unique_ell_three rho₁ hrho₁ hell₁
  have h2 := unique_ell_three rho₂ hrho₂ hell₂
  exact hterms (by rw [h1, h2])

theorem no_path_exit_collision_searchDw2_ell_lt_three_t_three
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    {ell : Nat}
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (hle : ell ≤ 2)
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) :
    ¬ isPathExitCollisionW2 (t := 3) (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ :=
  (not_depth_eligible_ell_lt_three_t_three rho₁ hell₁ hle ht₁).elim

/-! ### Residual discharge on `searchDw2` / `t = 3` (unique-preimage) -/

private theorem ell_eq_three_of_depth_ge_three {ell : Nat}
    (rho : MatchingMap 3 3)
    (hell : (freePigeons rho).card = ell)
    (ht : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho)) :
    ell = 3 := by
  have hle := vmdtDepth_canonicalVMDT_le_freePigeons searchDw2 rho
  have hcard : ell ≤ 3 := by
    have : (freePigeons rho).card ≤ Fintype.card (Fin 3) :=
      Finset.card_le_univ _
    simpa [hell, Fintype.card_fin] using this
  omega

/-- **S2203:** on Fin 3 / `searchDw2` / `t = 3`, equal codes force equal
entered-term sequences (unique free-count-3 empty preimage). -/
theorem encodeMatchEnteredTermsEqResidual_searchDw2_t_three {ell : Nat} :
    EncodeMatchEnteredTermsEqResidual (p := 3) (h := 3) (w := 3) (t := 3)
      (ell := ell) rfl searchDw2 searchDw2_width := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ _hcode
  have he1 := ell_eq_three_of_depth_ge_three rho₁ hell₁ ht₁
  have he2 := ell_eq_three_of_depth_ge_three rho₂ hell₂ ht₂
  have h1 := unique_ell_three rho₁ hrho₁ (by rw [hell₁, he1])
  have h2 := unique_ell_three rho₂ hrho₂ (by rw [hell₂, he2])
  simp [h1, h2]

/-- **S2203:** length-2 exit residual holds on this package by unique
preimage (and a length-2 image exists — see
`exists_length_two_encode_image_width_ge_two`). -/
theorem encodeMatchLengthTwoExitEqResidual_searchDw2_t_three {ell : Nat} :
    EncodeMatchLengthTwoExitEqResidual (p := 3) (h := 3) (w := 3) (t := 3)
      (ell := ell) rfl searchDw2 searchDw2_width := by
  intro rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ _hcode _hlen
  have he1 := ell_eq_three_of_depth_ge_three rho₁ hell₁ ht₁
  have he2 := ell_eq_three_of_depth_ge_three rho₂ hell₂ ht₂
  have h1 := unique_ell_three rho₁ hrho₁ (by rw [hell₁, he1])
  have h2 := unique_ell_three rho₂ hrho₂ (by rw [hell₂, he2])
  simp [h1, h2]

/-- Equal codes force equal path exits on Fin 3 / `searchDw2` / `t = 3`. -/
theorem firstBlockPathExitMatching_eq_of_encodeMatch_eq_searchDw2_t_three
    {ell : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂))
    (_hcode :
      encodeMatch (p := 3) (h := 3) (w := 3) (t := 3) (ell := ell) rfl
        rho₁ searchDw2 hrho₁ hell₁ ht₁ searchDw2_width =
      encodeMatch (p := 3) (h := 3) (w := 3) (t := 3) (ell := ell) rfl
        rho₂ searchDw2 hrho₂ hell₂ ht₂ searchDw2_width) :
    firstBlockPathExitMatching rho₁ searchDw2 3 =
      firstBlockPathExitMatching rho₂ searchDw2 3 := by
  have he1 := ell_eq_three_of_depth_ge_three rho₁ hell₁ ht₁
  have he2 := ell_eq_three_of_depth_ge_three rho₂ hell₂ ht₂
  have h1 := unique_ell_three rho₁ hrho₁ (by rw [hell₁, he1])
  have h2 := unique_ell_three rho₂ hrho₂ (by rw [hell₂, he2])
  simp [h1, h2]

theorem no_path_exit_collision_searchDw2_t_three {ell : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) :
    ¬ isPathExitCollisionW2 (t := 3) (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨hcode, hexit⟩
  exact hexit
    (firstBlockPathExitMatching_eq_of_encodeMatch_eq_searchDw2_t_three
      (ell := ell) rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode)

theorem no_entered_terms_collision_searchDw2_t_three {ell : Nat}
    (rho₁ rho₂ : MatchingMap 3 3)
    (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
    (hell₁ : (freePigeons rho₁).card = ell)
    (hell₂ : (freePigeons rho₂).card = ell)
    (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
    (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)) :
    ¬ isEnteredTermsCollisionW2 (t := 3) (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ := by
  intro ⟨hcode, hterms⟩
  exact hterms
    (encodeMatchEnteredTermsEqResidual_searchDw2_t_three (ell := ell)
      rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ hcode)

/-- **S2203 collision-search summary (Fin 3 / `searchDw2` / `t = 3`).**

* Genuine width-≥2 term in the DNF (`searchDw2_has_width_ge_two`).
* Non-vacuous length-2 encode image under empty matching
  (`exists_length_two_encode_image_width_ge_two`).
* `ell = 3`: unique empty preimage ⇒ no collision.
* `ell ≤ 2`: empty depth-eligible slice at `t = 3`.
* Every free-count: equal codes ⇒ equal entered terms and equal path exits;
  no path-exit collision witness.
* `EncodeMatchLengthTwoExitEqResidual` discharged by unique-preimage
  (non-vacuous length-2 image).
* No bank stop-loss.  Packet-only walked-pair recovery remains open outside
  unique-preimage packages.
-/
theorem collision_search_fin3_width_ge_two_t_three_summary :
    (∃ term ∈ searchDw2, 2 ≤ term.length) ∧
      (∃ (rho : MatchingMap 3 3),
        IsMatching rho ∧
          3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho) ∧
          (enteredTermsOf rho searchDw2 3).length = 2) ∧
      (∀ (rho : MatchingMap 3 3) (hrho : IsMatching rho),
        (freePigeons rho).card = 3 → rho = emptyMatching 3 3) ∧
      (∀ (rho : MatchingMap 3 3) (ell : Nat),
        (freePigeons rho).card = ell → ell ≤ 2 →
          ¬ 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho)) ∧
      (∀ (ell : Nat),
        EncodeMatchLengthTwoExitEqResidual (p := 3) (h := 3) (w := 3)
          (t := 3) (ell := ell) rfl searchDw2 searchDw2_width) ∧
      (∀ (ell : Nat),
        EncodeMatchEnteredTermsEqResidual (p := 3) (h := 3) (w := 3)
          (t := 3) (ell := ell) rfl searchDw2 searchDw2_width) ∧
      (∀ (ell : Nat) (rho₁ rho₂ : MatchingMap 3 3)
        (hrho₁ : IsMatching rho₁) (hrho₂ : IsMatching rho₂)
        (hell₁ : (freePigeons rho₁).card = ell)
        (hell₂ : (freePigeons rho₂).card = ell)
        (ht₁ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₁))
        (ht₂ : 3 ≤ vmdtDepth (canonicalVMDT searchDw2 rho₂)),
        ¬ isPathExitCollisionW2 (t := 3) (ell := ell)
          rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂) :=
  ⟨searchDw2_has_width_ge_two,
    ⟨emptyMatching 3 3, isMatching_empty 3 3,
      searchDw2_empty_depth_ge_three,
      enteredTermsOf_empty_searchDw2_three_length⟩,
    fun rho hrho hell => unique_ell_three rho hrho hell,
    fun rho _ell hell hle =>
      not_depth_eligible_ell_lt_three_t_three rho hell hle,
    fun ell => encodeMatchLengthTwoExitEqResidual_searchDw2_t_three (ell := ell),
    fun ell => encodeMatchEnteredTermsEqResidual_searchDw2_t_three (ell := ell),
    fun ell rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂ =>
      no_path_exit_collision_searchDw2_t_three (ell := ell)
        rho₁ rho₂ hrho₁ hrho₂ hell₁ hell₂ ht₁ ht₂⟩

end PHPMatchingEncodeCollisionSearch
end PvNP
