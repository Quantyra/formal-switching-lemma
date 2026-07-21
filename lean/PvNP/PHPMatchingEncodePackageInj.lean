import PvNP.PHPMatchingEncodeLengthTwoClass

/-!
# S2207: searchD4mp / t = 3 package subtype injectivity

Board `Fin 4`, dual width-2 DNF `searchD4mp`, depth `t = 3`.

Package-only discharge:

* Structural bound: `searchD4mp` has two terms and root traces never re-enter
  a completed term, so every depth-eligible encode image has
  `(enteredTermsOf ρ searchD4mp 3).length ≤ 2`.
* Entered-term residual via
  `encodeMatchEnteredTermsEqResidual_of_length_le_two_of_exit` plus the S2206
  length-2 path-exit residual.
* Subtype injectivity of `encodeMatch` on `vbadMatchings searchD4mp (t-1) ell`
  via `encodeMatch_subtype_injective_of_enteredTermsEqResidual`.

INTEGRITY: no sorry, no admit, no new axiom, no native_decide.
Honest bounds: Fin 4 / `searchD4mp` / `t = 3` only. No general GA-4.
No v0.11.0 tag (general residual remains open outside this package).
-/

namespace PvNP
namespace PHPMatchingEncodePackageInj

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity
open PHPMatchingEncodeCollisionSearch
open PHPMatchingEncodeMultiPreimage
open PHPMatchingEncodeFiberSearch
open PHPMatchingEncodeLengthTwoClass
open RestrictedPHPFloor

/-! ## Consecutive path-compose on every vevents block list -/

private def pathComposeAdj {p h : Nat} (B₀ B₁ : VBlock p h) : Prop :=
  B₁.entry =
    compose B₀.entry (pairsToMatching (B₀.steps.map VStep.pair))

private theorem vevents_blocks_chain_path_compose {p h : Nat} :
    ∀ (fuel : Nat) (mu : MatchingMap p h) (pending : List (Vertex p h))
      (D : MDNF p h) (feed : List (Vertex p h)),
      List.Chain' pathComposeAdj (blocksOf (vevents fuel mu pending D feed))
  | _, mu, [], [], feed => by
      rw [vevents_nil, blocksOf_nil]
      exact List.chain'_nil
  | fuel, mu, [], t :: restD, feed => by
      by_cases hleg : termMatchingLegalB t = true
      · by_cases hfals : termFalsifiedB mu t = true
        · rw [vevents_skip_falsified fuel mu t restD feed hleg hfals]
          exact vevents_blocks_chain_path_compose fuel mu [] restD feed
        · have hfals' : termFalsifiedB mu t = false :=
            Bool.eq_false_iff.mpr hfals
          by_cases hsat : termSatisfiedB mu t = true
          · rw [vevents_stop_satisfied fuel mu t restD feed hleg hfals' hsat,
              blocksOf_nil]
            exact List.chain'_nil
          · have hsat' : termSatisfiedB mu t = false :=
              Bool.eq_false_iff.mpr hsat
            cases fuel with
            | zero =>
                rw [vevents_entry_zero mu t restD feed hleg hfals' hsat',
                  blocksOf_nil]
                exact List.chain'_nil
            | succ fuel' =>
                cases htv : termVertices mu t with
                | nil =>
                    rw [vevents_entry_novertices fuel' mu t restD feed hleg
                      hfals' hsat' htv, blocksOf_nil]
                    exact List.chain'_nil
                | cons v vs =>
                    cases v with
                    | inl i =>
                        cases feed with
                        | nil =>
                            rw [vevents_entry_feed_nil fuel' mu t restD i vs
                              hleg hfals' hsat' htv, blocksOf_nil]
                            exact List.chain'_nil
                        | cons av fs =>
                            cases av with
                            | inl q =>
                                rw [vevents_entry_feed_illkind fuel' mu t restD
                                  i vs q fs hleg hfals' hsat' htv, blocksOf_nil]
                                exact List.chain'_nil
                            | inr a =>
                                by_cases hha : holeUsed mu a = true
                                · rw [vevents_entry_pigeon_dead fuel' mu t restD
                                    i vs a fs hleg hfals' hsat' htv hha,
                                    blocksOf_nil]
                                  exact List.chain'_nil
                                · have hha' : holeUsed mu a = false :=
                                    Bool.eq_false_iff.mpr hha
                                  rw [vevents_entry_pigeon_live fuel' mu t restD
                                    i vs a fs hleg hfals' hsat' htv hha',
                                    blocksOf_enter]
                                  set cont :=
                                    vevents fuel'
                                      (compose mu (singleMatching i a)) vs
                                      (t :: restD) fs with hcont
                                  have htail :
                                      blocksOf
                                          (afterSteps
                                            (VEvent.qstep
                                              ⟨Sum.inl i, (i, a)⟩ :: cont)) =
                                        blocksOf cont := by
                                    change
                                        blocksOf (afterSteps cont) =
                                          blocksOf cont
                                    exact blocksOf_afterSteps cont
                                  rw [htail]
                                  have hchain_tail :
                                      List.Chain' pathComposeAdj
                                        (blocksOf cont) := by
                                    rw [hcont]
                                    exact vevents_blocks_chain_path_compose
                                      fuel' (compose mu (singleMatching i a))
                                      vs (t :: restD) fs
                                  set B0 : VBlock p h :=
                                    ⟨t, mu,
                                      stepsPrefix
                                        (VEvent.qstep
                                          ⟨Sum.inl i, (i, a)⟩ :: cont)⟩
                                  match hBs : blocksOf cont with
                                  | [] =>
                                      exact List.chain'_singleton B0
                                  | B1 :: restB =>
                                      have hblocks :
                                          blocksOf
                                              (vevents (fuel' + 1) mu []
                                                (t :: restD)
                                                (Sum.inr a :: fs)) =
                                            B0 :: B1 :: restB := by
                                        rw [vevents_entry_pigeon_live fuel' mu t
                                          restD i vs a fs hleg hfals' hsat' htv
                                          hha', blocksOf_enter, htail, hBs]
                                      have hR : pathComposeAdj B0 B1 :=
                                        vevents_second_block_entry_eq_compose_first_steps
                                          (fuel' + 1) mu [] (t :: restD)
                                          (Sum.inr a :: fs) B0 B1 restB hblocks
                                      have hchain' :
                                          List.Chain' pathComposeAdj
                                            (B1 :: restB) := by
                                        rwa [hBs] at hchain_tail
                                      exact List.chain'_cons.mpr ⟨hR, hchain'⟩
                    | inr b =>
                        exact absurd htv
                          (termVertices_head_not_hole mu t b vs)
      · have hleg' : termMatchingLegalB t = false :=
          Bool.eq_false_iff.mpr hleg
        rw [vevents_skip_illegal fuel mu t restD feed hleg']
        exact vevents_blocks_chain_path_compose fuel mu [] restD feed
  | fuel, mu, v :: vs, D, feed => by
      by_cases hcov : vertexCoveredB mu v = true
      · rw [vevents_block_skip_covered fuel mu v vs D feed hcov]
        exact vevents_blocks_chain_path_compose fuel mu vs D feed
      · have hcov' : vertexCoveredB mu v = false :=
          Bool.eq_false_iff.mpr hcov
        cases fuel with
        | zero =>
            rw [vevents_block_zero mu v vs D feed hcov', blocksOf_nil]
            exact List.chain'_nil
        | succ fuel' =>
            cases v with
            | inl i =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov',
                      blocksOf_nil]
                    exact List.chain'_nil
                | cons av fs =>
                    cases av with
                    | inl q =>
                        rw [vevents_block_pigeon_illkind fuel' mu i vs D q fs
                          hcov', blocksOf_nil]
                        exact List.chain'_nil
                    | inr a =>
                        by_cases hha : holeUsed mu a = true
                        · rw [vevents_block_pigeon_dead fuel' mu i vs D a fs
                            hcov' hha, blocksOf_nil]
                          exact List.chain'_nil
                        · have hha' : holeUsed mu a = false :=
                            Bool.eq_false_iff.mpr hha
                          rw [vevents_block_pigeon_live fuel' mu i vs D a fs
                            hcov' hha', blocksOf_qstep]
                          exact vevents_blocks_chain_path_compose fuel'
                            (compose mu (singleMatching i a)) vs D fs
            | inr b =>
                cases feed with
                | nil =>
                    rw [vevents_block_feed_nil fuel' mu _ vs D hcov',
                      blocksOf_nil]
                    exact List.chain'_nil
                | cons av fs =>
                    cases av with
                    | inr a =>
                        rw [vevents_block_hole_illkind fuel' mu b vs D a fs
                          hcov', blocksOf_nil]
                        exact List.chain'_nil
                    | inl q =>
                        by_cases hq : (mu q).isSome = true
                        · rw [vevents_block_hole_dead fuel' mu b vs D q fs
                            hcov' hq, blocksOf_nil]
                          exact List.chain'_nil
                        · have hq' : (mu q).isSome = false :=
                            Bool.eq_false_iff.mpr hq
                          rw [vevents_block_hole_live fuel' mu b vs D q fs
                            hcov' hq', blocksOf_qstep]
                          exact vevents_blocks_chain_path_compose fuel'
                            (compose mu (singleMatching q b)) vs D fs
  termination_by fuel _ pending D _ => (fuel, pending.length + D.length)

private theorem blocks_chain_path_compose {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h)) :
    List.Chain' pathComposeAdj (blocksOf (vtrace rho D feed)) :=
  vevents_blocks_chain_path_compose (freePigeons rho).card rho [] D feed

/-! ## Frozen-cover determination -/

private theorem pairUnresolvedB_eq_false_of_inl_covered
    {p h : Nat} (mu : MatchingMap p h) (e : Fin p × Fin h)
    (hc : vertexCoveredB mu (Sum.inl e.1) = true) :
    pairUnresolvedB mu e = false := by
  unfold pairUnresolvedB vertexCoveredB at *
  cases hmu : mu e.1 <;> simp_all

private theorem pair_sat_or_fals_of_not_unresolved
    {p h : Nat} (mu : MatchingMap p h) (e : Fin p × Fin h)
    (h : pairUnresolvedB mu e = false) :
    pairSatB mu e = true ∨ pairFalsB mu e = true := by
  have tri := pair_status_trichotomy mu e
  cases hs : pairSatB mu e <;> cases hf : pairFalsB mu e <;>
    cases hu : pairUnresolvedB mu e <;> simp_all

private theorem pair_sat_or_fals_of_frozen_covered
    {p h : Nat} {mu nu : MatchingMap p h} (t : MTerm p h) (e : Fin p × Fin h)
    (he : e ∈ t) (hag : MAgree mu nu) (hnu : IsMatching nu)
    (hcov : ∀ w ∈ termVertices mu t, vertexCoveredB nu w = true) :
    pairSatB nu e = true ∨ pairFalsB nu e = true := by
  by_cases hun : pairUnresolvedB mu e = true
  · have hinl : Sum.inl e.1 ∈ termVertices mu t := by
      unfold termVertices
      exact List.mem_bind.mpr ⟨e, List.mem_filter.mpr ⟨he, hun⟩,
        List.mem_cons_self _ _⟩
    exact pair_sat_or_fals_of_not_unresolved nu e
      (pairUnresolvedB_eq_false_of_inl_covered nu e (hcov _ hinl))
  · have hun' : pairUnresolvedB mu e = false := Bool.eq_false_iff.mpr hun
    rcases pair_sat_or_fals_of_not_unresolved mu e hun' with hs | hf
    · left
      unfold pairSatB at hs ⊢
      cases hmu : mu e.1 with
      | none => simp [hmu] at hs
      | some b =>
          have hb : (b == e.2) = true := by simpa [hmu] using hs
          have hbeq : b = e.2 := beq_iff_eq.mp hb
          have hnu' : nu e.1 = some e.2 := by
            simpa [hbeq] using hag e.1 b hmu
          simp [hnu']
    · exact Or.inr (pairFalsB_mono hag hnu e hf)

private theorem term_determined_of_frozen_covered
    {p h : Nat} {mu nu : MatchingMap p h} (t : MTerm p h)
    (hag : MAgree mu nu) (hnu : IsMatching nu)
    (hcov : ∀ w ∈ termVertices mu t, vertexCoveredB nu w = true) :
    termSatisfiedB nu t = true ∨ termFalsifiedB nu t = true := by
  by_cases hf : termFalsifiedB nu t = true
  · exact Or.inr hf
  · left
    have hnf : termFalsifiedB nu t = false := Bool.eq_false_iff.mpr hf
    unfold termSatisfiedB
    rw [List.all_eq_true]
    intro e he
    rcases pair_sat_or_fals_of_frozen_covered t e he hag hnu hcov with hs | hpf
    · exact hs
    · have hany : termFalsifiedB nu t = true := by
        unfold termFalsifiedB
        exact List.any_eq_true.mpr ⟨e, he, hpf⟩
      exact absurd hany (ne_of_eq_of_ne hnf Bool.false_ne_true)

private theorem mAgree_of_pathComposeAdj {p h : Nat} {B₀ B₁ : VBlock p h}
    (h : pathComposeAdj B₀ B₁) : MAgree B₀.entry B₁.entry := by
  change B₁.entry =
      compose B₀.entry (pairsToMatching (B₀.steps.map VStep.pair)) at h
  rw [h]; exact mAgree_compose_left _ _

/-- Consecutive blocks on a root trace: previous term falsified at next entry. -/
theorem consecutive_prev_term_falsified {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho)
    (B₀ B₁ : VBlock p h) (pre suf : List (VBlock p h))
    (hblocks :
      blocksOf (vtrace rho D feed) = pre ++ B₀ :: B₁ :: suf) :
    termFalsifiedB B₁.entry B₀.term = true := by
  have hB₀mem : B₀ ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]
    exact List.mem_append_right _ (List.mem_cons_self _ _)
  have hB₁mem : B₁ ∈ blocksOf (vtrace rho D feed) := by
    rw [hblocks]
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
  have hspec₀ :=
    blocksOf_entry_spec (freePigeons rho).card rho [] D feed B₀ hB₀mem
  have hspec₁ :=
    blocksOf_entry_spec (freePigeons rho).card rho [] D feed B₁ hB₁mem
  have hmatch₁ : IsMatching B₁.entry :=
    blocksOf_entry_isMatching (freePigeons rho).card rho [] D feed hrho
      B₁.term B₁.entry (enter_mem_of_mem_blocksOf _ B₁ hB₁mem)
  have hchain := blocks_chain_path_compose rho D feed
  have hpath : pathComposeAdj B₀ B₁ := by
    have hchain' : List.Chain' pathComposeAdj (pre ++ B₀ :: B₁ :: suf) := by
      rwa [← hblocks]
    exact (List.chain'_append_cons_cons.mp hchain').2.1
  have hag := mAgree_of_pathComposeAdj hpath
  have hfrozen :=
    blocksOf_frozen_covered (freePigeons rho).card rho [] D feed
  have hcov :
      ∀ w ∈ termVertices B₀.entry B₀.term,
        vertexCoveredB
          (compose B₀.entry (pairsToMatching (B₀.steps.map VStep.pair)))
          w = true := by
    have hp : List.Pairwise
        (fun B _ => ∀ w ∈ termVertices B.entry B.term,
          vertexCoveredB
            (compose B.entry (pairsToMatching (B.steps.map VStep.pair)))
            w = true)
        (blocksOf (vtrace rho D feed)) := hfrozen
    have hdrop :
        List.drop pre.length (blocksOf (vtrace rho D feed)) =
          B₀ :: B₁ :: suf := by
      rw [hblocks, List.drop_left]
    have hp' : List.Pairwise
        (fun B _ => ∀ w ∈ termVertices B.entry B.term,
          vertexCoveredB
            (compose B.entry (pairsToMatching (B.steps.map VStep.pair)))
            w = true)
        (B₀ :: B₁ :: suf) := by
      have := List.Pairwise.drop (n := pre.length) hp
      rwa [hdrop] at this
    exact (List.pairwise_cons.mp hp').1 B₁ (List.mem_cons_self _ _)
  have hpath' :
      B₁.entry =
        compose B₀.entry (pairsToMatching (B₀.steps.map VStep.pair)) :=
    hpath
  have hdet :
      termSatisfiedB B₁.entry B₀.term = true ∨
        termFalsifiedB B₁.entry B₀.term = true :=
    term_determined_of_frozen_covered (mu := B₀.entry) (nu := B₁.entry)
      B₀.term hag hmatch₁ (by intro w hw; simpa [hpath'] using hcov w hw)
  rcases hdet with hsat | hfals
  · have hnf :=
      termFalsifiedB_eq_false_of_termSatisfiedB B₁.entry B₀.term hsat
    rcases blocksOf_entered_first (freePigeons rho).card rho [] D feed hrho
        B₀ hB₀mem with ⟨preT, sufT, hD, hpre⟩
    have hpre' :
        ∀ t' ∈ preT,
          termMatchingLegalB t' = false ∨
            termFalsifiedB B₁.entry t' = true := by
      intro t' ht'
      rcases hpre t' ht' with hileg | hf
      · exact Or.inl hileg
      · exact Or.inr (termFalsifiedB_mono hag hmatch₁ t' hf)
    have hfnf₀ :
        firstNotFalsifiedTerm B₁.entry D = some B₀.term :=
      firstNotFalsifiedTerm_eq_of_factor B₁.entry D preT B₀.term sufT hD
        hpre' hspec₀.2.1 hnf
    have hfnf₁ :
        firstNotFalsifiedTerm B₁.entry D = some B₁.term :=
      block_term_eq_firstNotFalsified_entry rho D feed hrho B₁ hB₁mem
    have hterms : B₀.term = B₁.term :=
      Option.some.inj (hfnf₀.symm.trans hfnf₁)
    have hnsat : termSatisfiedB B₁.entry B₁.term = false := hspec₁.2.2.2
    rw [← hterms, hsat] at hnsat
    exact Bool.noConfusion hnsat
  · exact hfals

/-! ## Two-term DNF length ≤ 2 -/

private theorem firstNotFalsified_eq_none_of_forall_fals
    {p h : Nat} (mu : MatchingMap p h) :
    ∀ (D : MDNF p h),
      (∀ t ∈ D, termMatchingLegalB t = false ∨ termFalsifiedB mu t = true) →
        firstNotFalsifiedTerm mu D = none
  | [], _ => rfl
  | t :: rest, h => by
      change
        (if termMatchingLegalB t = false then firstNotFalsifiedTerm mu rest
         else if termFalsifiedB mu t = true then firstNotFalsifiedTerm mu rest
         else some t) =
          none
      have ht := h t (List.mem_cons_self _ _)
      have hrest :
          ∀ t' ∈ rest,
            termMatchingLegalB t' = false ∨
              termFalsifiedB mu t' = true :=
        fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      rcases ht with hileg | hfals
      · simp only [hileg, ↓reduceIte]
        exact firstNotFalsified_eq_none_of_forall_fals mu rest hrest
      · by_cases hileg' : termMatchingLegalB t = false
        · simp only [hileg', ↓reduceIte]
          exact firstNotFalsified_eq_none_of_forall_fals mu rest hrest
        · have hleg' : termMatchingLegalB t = true :=
            Bool.eq_true_of_not_eq_false hileg'
          simp only [hleg', Bool.true_eq_false, ↓reduceIte, hfals]
          exact firstNotFalsified_eq_none_of_forall_fals mu rest hrest

private theorem blocksOf_term_mem_D_root {p h : Nat}
    (rho : MatchingMap p h) (D : MDNF p h) (feed : List (Vertex p h))
    (hrho : IsMatching rho) (B : VBlock p h)
    (hB : B ∈ blocksOf (vtrace rho D feed)) : B.term ∈ D := by
  rcases blocksOf_entered_first (freePigeons rho).card rho [] D feed hrho B
      hB with ⟨pre, suf, hD, _⟩
  rw [hD]
  exact List.mem_append_right _ (List.mem_cons_self _ _)

/-- On a two-term DNF, entered-term length is at most 2: a third block would
require a live term after both distinct entered terms have been falsified. -/
theorem enteredTermsOf_length_le_two_of_two_term_dnf {p h : Nat}
    (rho : MatchingMap p h) (tA tB : MTerm p h)
    (hrho : IsMatching rho) (t : Nat) :
    (enteredTermsOf rho [tA, tB] t).length ≤ 2 := by
  let D : MDNF p h := [tA, tB]
  let feed := leftmostLiveDeepFeed rho D t
  by_contra hgt
  have hge : 3 ≤ (blocksOf (vtrace rho D feed)).length := by
    have : ¬ (enteredTermsOf rho D t).length ≤ 2 := by
      simpa [enteredTermsOf, feed, List.length_map, D] using hgt
    have : ¬ (blocksOf (vtrace rho D feed)).length ≤ 2 := by
      simpa [enteredTermsOf, feed, List.length_map] using this
    omega
  match hblocks : blocksOf (vtrace rho D feed) with
  | [] => simp [hblocks] at hge
  | [_] => simp [hblocks] at hge
  | [_, _] => simp [hblocks] at hge
  | B₀ :: B₁ :: B₂ :: rest =>
      have h01 :
          blocksOf (vtrace rho D feed) =
            ([] : List (VBlock p h)) ++ B₀ :: B₁ :: B₂ :: rest := by
        simpa using hblocks
      have h12 :
          blocksOf (vtrace rho D feed) = [B₀] ++ B₁ :: B₂ :: rest := by
        simpa [List.singleton_append] using hblocks
      have hf01 :=
        consecutive_prev_term_falsified rho D feed hrho B₀ B₁ [] (B₂ :: rest)
          h01
      have hf12 :=
        consecutive_prev_term_falsified rho D feed hrho B₁ B₂ [B₀] rest h12
      have hB₀mem : B₀ ∈ blocksOf (vtrace rho D feed) := by
        rw [hblocks]; exact List.mem_cons_self _ _
      have hB₁mem : B₁ ∈ blocksOf (vtrace rho D feed) := by
        rw [hblocks]
        exact List.mem_cons_of_mem _ (List.mem_cons_self _ _)
      have hB₂mem : B₂ ∈ blocksOf (vtrace rho D feed) := by
        rw [hblocks]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
      have hfnf :
          firstNotFalsifiedTerm B₂.entry D = some B₂.term :=
        block_term_eq_firstNotFalsified_entry rho D feed hrho B₂ hB₂mem
      have hchain := blocks_chain_path_compose rho D feed
      have hchain' :
          List.Chain' pathComposeAdj (B₀ :: B₁ :: B₂ :: rest) := by
        rwa [hblocks] at hchain
      have hpath12 : pathComposeAdj B₁ B₂ :=
        (List.chain'_cons.mp (List.chain'_cons.mp hchain').2).1
      have hag12 := mAgree_of_pathComposeAdj hpath12
      have hmatch₂ : IsMatching B₂.entry :=
        blocksOf_entry_isMatching (freePigeons rho).card rho [] D feed hrho
          B₂.term B₂.entry (enter_mem_of_mem_blocksOf _ B₂ hB₂mem)
      -- hf01 : falsified at B₁.entry; mono along B₁ → B₂
      have hf02 : termFalsifiedB B₂.entry B₀.term = true :=
        termFalsifiedB_mono hag12 hmatch₂ B₀.term hf01
      have h0mem : B₀.term ∈ D :=
        blocksOf_term_mem_D_root rho D feed hrho B₀ hB₀mem
      have h1mem : B₁.term ∈ D :=
        blocksOf_term_mem_D_root rho D feed hrho B₁ hB₁mem
      have hspec₁ :=
        blocksOf_entry_spec (freePigeons rho).card rho [] D feed B₁ hB₁mem
      have hne : B₀.term ≠ B₁.term := by
        intro heq
        have : termFalsifiedB B₁.entry B₁.term = true := by
          simpa [heq] using hf01
        exact Bool.noConfusion (this.symm.trans hspec₁.2.2.1)
      have hcover :
          ∀ u ∈ D,
            termMatchingLegalB u = false ∨
              termFalsifiedB B₂.entry u = true := by
        intro u hu
        have hu' : u = tA ∨ u = tB := by simpa [D] using hu
        have h01' : B₀.term = tA ∨ B₀.term = tB := by simpa [D] using h0mem
        have h11' : B₁.term = tA ∨ B₁.term = tB := by simpa [D] using h1mem
        have : u = B₀.term ∨ u = B₁.term := by
          rcases hu' with rfl | rfl <;> rcases h01' with h0 | h0 <;>
            rcases h11' with h1 | h1
          · left; exact h0.symm
          · left; exact h0.symm
          · right; exact h1.symm
          · exact absurd (h0.trans h1.symm) hne
          · exact absurd (h0.trans h1.symm) hne
          · right; exact h1.symm
          · left; exact h0.symm
          · exact absurd (h0.trans h1.symm) hne
        rcases this with rfl | rfl
        · exact Or.inr hf02
        · exact Or.inr hf12
      have hnone : firstNotFalsifiedTerm B₂.entry D = none :=
        firstNotFalsified_eq_none_of_forall_fals B₂.entry D hcover
      rw [hnone] at hfnf
      exact Option.noConfusion hfnf

/-- **S2207:** every `searchD4mp` / `t = 3` encode image has entered-term
length ≤ 2 (two-term DNF, no re-entry). -/
theorem enteredTermsOf_length_le_two_searchD4mp_t_three
    {ell : Nat} (rho : MatchingMap 4 4) (hrho : IsMatching rho)
    (_hell : (freePigeons rho).card = ell)
    (_ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho)) :
    (enteredTermsOf rho searchD4mp 3).length ≤ 2 := by
  simpa [searchD4mp_eq] using
    enteredTermsOf_length_le_two_of_two_term_dnf rho termA termB hrho 3

/-! ## Entered-term residual + subtype injectivity package -/

/-- **S2207:** entered-term residual on Fin 4 / `searchD4mp` / `t = 3`
(length-≤2 bound + S2206 length-2 path-exit residual). -/
theorem encodeMatchEnteredTermsEqResidual_searchD4mp_t_three {ell : Nat} :
    EncodeMatchEnteredTermsEqResidual (p := 4) (h := 4) (w := 2) (t := 3)
      (ell := ell) rfl searchD4mp searchD4mp_width :=
  encodeMatchEnteredTermsEqResidual_of_length_le_two_of_exit
    rfl searchD4mp searchD4mp_width
    (fun rho hrho hell ht =>
      enteredTermsOf_length_le_two_searchD4mp_t_three (ell := ell) rho hrho
        hell ht)
    encodeMatchLengthTwoExitEqResidual_searchD4mp_t_three

/-- **S2207:** `encodeMatch` is injective on the graded bad-set subtype
`vbadMatchings searchD4mp (3 - 1) ell` (package residual). -/
theorem encodeMatch_subtype_injective_searchD4mp_t_three {ell : Nat} :
    Function.Injective
      (fun rho :
          {rho : MatchingMap 4 4 //
            rho ∈ vbadMatchings searchD4mp (3 - 1) ell} =>
        let hmem :=
          (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
        let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
          Nat.le_of_pred_lt hmem.2
        encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := ell) rfl
          rho.1 searchD4mp hmem.1.1 hmem.1.2 ht searchD4mp_width) :=
  encodeMatch_subtype_injective_of_enteredTermsEqResidual
    rfl searchD4mp searchD4mp_width
    encodeMatchEnteredTermsEqResidual_searchD4mp_t_three

/-! ## Summary -/

/-- **S2207 package summary** (Fin 4 / `searchD4mp` / `t = 3` only). -/
theorem package_inj_searchD4mp_t_three_summary :
    (∀ (ell : Nat) (rho : MatchingMap 4 4),
      IsMatching rho →
        (freePigeons rho).card = ell →
          3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho) →
            (enteredTermsOf rho searchD4mp 3).length ≤ 2) ∧
      (∀ (ell : Nat),
        EncodeMatchEnteredTermsEqResidual (p := 4) (h := 4) (w := 2)
          (t := 3) (ell := ell) rfl searchD4mp searchD4mp_width) ∧
      (∀ (ell : Nat),
        Function.Injective
          (fun rho :
              {rho : MatchingMap 4 4 //
                rho ∈ vbadMatchings searchD4mp (3 - 1) ell} =>
            let hmem :=
              (mem_vbadMatchings searchD4mp (3 - 1) ell rho.1).mp rho.2
            let ht : 3 ≤ vmdtDepth (canonicalVMDT searchD4mp rho.1) :=
              Nat.le_of_pred_lt hmem.2
            encodeMatch (p := 4) (h := 4) (w := 2) (t := 3) (ell := ell) rfl
              rho.1 searchD4mp hmem.1.1 hmem.1.2 ht searchD4mp_width)) :=
  ⟨fun ell rho hrho hell ht =>
      enteredTermsOf_length_le_two_searchD4mp_t_three (ell := ell) rho hrho
        hell ht,
    fun _ell => encodeMatchEnteredTermsEqResidual_searchD4mp_t_three,
    fun _ell => encodeMatch_subtype_injective_searchD4mp_t_three⟩

end PHPMatchingEncodePackageInj
end PvNP
