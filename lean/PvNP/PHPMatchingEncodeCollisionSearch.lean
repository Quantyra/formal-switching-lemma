import PvNP.PHPMatchingEncodeInjectivity
import Mathlib.Tactic.FinCases

/-!
# S2199–S2202: genuine encode-preimage collision search

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

**Still open:** general multi-block (`t ≥ 3` or width ≥ 2) path-exit recovery
from the packet alone; unconditional `encodeMatch_subtype_injective`.

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

end PHPMatchingEncodeCollisionSearch
end PvNP
