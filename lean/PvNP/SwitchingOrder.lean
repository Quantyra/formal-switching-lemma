/-
# Order reconciliation for the D-ORIGINAL switching-lemma decode (HONEST attempt)

This file attacks the GENUINE remaining content named in the task: the ORDER-RECONCILIATION
lemma (A) for the D-ORIGINAL scan `SwitchingDOrig.firstNonFalsified`, and the
ORIGINAL-POSITION column lemma (B).

## What is attempted (and the discipline)

The D-original scan `firstNonFalsified D (state_j)` is ρ-INDEPENDENT (it scans the fixed
DNF `D` under the ρ-independent evolving state `state_j = stateAt σ_loc prev`).  Unlike the
`D|σ_loc` scan refuted in `SwitchingStepData.not_stateStepData`, the recovered term `C` is
the ORIGINAL term (literals intact, no collapse).

We build the bridge linking `prefixRestr (deepPathV (D|ρ))`'s recorded deep directions to
the deep-direction restriction `dirRestrBlock` collected along the deep walk, and use it to
classify the D-original terms before the j-th deep term.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed axioms
⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.  Imported files
are untouched.  We report EXACTLY what closes and the exact obstruction if any.
-/
import PvNP.SwitchingDOrig

namespace PvNP
namespace SwitchingOrder

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingCardLemma
open SwitchingEncodeConstruct
open SwitchingEncodeLocal
open SwitchingDeepAux
open SwitchingClose
open SwitchingFactB
open SwitchingStateDecode
open SwitchingRazborovCode
open SwitchingDOrig
open SwitchingDecodeRef
open Classical

/-! ## 1. Bridge: `prefixRestr` of the head block records `dirRestrBlock`'s directions

`dirRestrQ`/`dirRestrBlock` collect, along the deep walk, the SAME `(var, dir)` pairs that
`deepPathVQ`/`deepPathV` emit (both follow the identical depth-comparison recursion).  We
prove that the restriction `prefixRestr (deepPathVQ vars D)` AGREES with
`dirRestrQ vars D` on every variable of `vars` — i.e. the recorded prefix directions ARE
the deep-direction restriction on the block's variables.  Proved by the shared recursion. -/

/-- `prefixRestr (p :: ps) v` is `some p.2` if `v = p.1`, else `prefixRestr ps v`. -/
theorem prefixRestr_cons {n : Nat} (p : Fin n × Bool) (ps : List (Fin n × Bool))
    (v : Fin n) :
    prefixRestr (p :: ps) v = if v = p.1 then some p.2 else prefixRestr ps v := by
  unfold prefixRestr
  rw [List.find?_cons]
  by_cases h : p.1 = v
  · subst h; simp
  · have : (decide (p.1 = v)) = false := by simp [h]
    rw [this]
    simp only [Bool.false_eq_true, if_false]
    by_cases h2 : v = p.1
    · exact absurd h2.symm h
    · rw [if_neg h2]

/-- **Bridge (helper, PROVED): `prefixRestr (deepPathVQ vars D)` agrees with
`dirRestrQ vars D` on every variable of `vars`.**  Both follow the IDENTICAL
depth-comparison recursion: `deepPathVQ` emits `(l.var, dir)` and `dirRestrQ` overlays
`single l.var dir`; on the head variable both yield `some dir`, and on a tail variable both
recurse into the same residual.  Under `SimpleTerm vars` the head variable does not recur,
so the prefix's FIRST occurrence is the head fixing.  This is the precise identification of
the recorded prefix directions with the deep-direction restriction, the bridge the
`SwitchingFactB.factB_iter` note flagged as "a separate induction not carried out". -/
theorem prefixRestr_deepPathVQ_eq_dirRestrQ {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), SimpleTerm vars → ∀ x ∈ vars.map (·.var),
      prefixRestr (deepPathVQ vars D) x = dirRestrQ vars D x
  | [], _, _, x, hx => by simp at hx
  | l :: vs, D, hs, x, hx => by
      have hnd : l.var ∉ vs.map (·.var) := by
        unfold SimpleTerm at hs
        simp only [List.map_cons, List.nodup_cons] at hs; exact hs.1
      have hsvs : SimpleTerm vs := by
        unfold SimpleTerm at hs ⊢
        simp only [List.map_cons, List.nodup_cons] at hs; exact hs.2
      simp only [List.map_cons, List.mem_cons] at hx
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · rw [show deepPathVQ (l :: vs) D
              = (l.var, true) :: deepPathVQ vs (assignVar l.var true D) from by
            rw [deepPathVQ]; simp only [if_pos h]]
        rw [show dirRestrQ (l :: vs) D
              = overlay (single l.var true) (dirRestrQ vs (assignVar l.var true D)) from by
            rw [dirRestrQ]; simp only [if_pos h]]
        rw [prefixRestr_cons]
        rcases hx with hxl | hxvs
        · subst hxl
          have hτnone : dirRestrQ vs (assignVar l.var true D) l.var = none :=
            dirRestrQ_apply_eq_none vs (assignVar l.var true D) l.var hnd
          have hov : overlay (single l.var true) (dirRestrQ vs (assignVar l.var true D)) l.var
              = single l.var true l.var :=
            overlay_eq_ρ_of_τ_none _ _ _ hτnone
          rw [hov]; unfold single; simp
        · have hxne : x ≠ l.var := by intro he; subst he; exact hnd hxvs
          have hsne : single l.var true x = none := single_apply_ne l.var true x hxne
          have hov : overlay (single l.var true) (dirRestrQ vs (assignVar l.var true D)) x
              = dirRestrQ vs (assignVar l.var true D) x := by
            unfold overlay
            cases hd : dirRestrQ vs (assignVar l.var true D) x with
            | none => rw [hsne]
            | some b => rfl
          rw [if_neg hxne, hov]
          exact prefixRestr_deepPathVQ_eq_dirRestrQ vs (assignVar l.var true D) hsvs x hxvs
      · rw [show deepPathVQ (l :: vs) D
              = (l.var, false) :: deepPathVQ vs (assignVar l.var false D) from by
            rw [deepPathVQ]; simp only [if_neg h]]
        rw [show dirRestrQ (l :: vs) D
              = overlay (single l.var false) (dirRestrQ vs (assignVar l.var false D)) from by
            rw [dirRestrQ]; simp only [if_neg h]]
        rw [prefixRestr_cons]
        rcases hx with hxl | hxvs
        · subst hxl
          have hτnone : dirRestrQ vs (assignVar l.var false D) l.var = none :=
            dirRestrQ_apply_eq_none vs (assignVar l.var false D) l.var hnd
          have hov : overlay (single l.var false) (dirRestrQ vs (assignVar l.var false D)) l.var
              = single l.var false l.var :=
            overlay_eq_ρ_of_τ_none _ _ _ hτnone
          rw [hov]; unfold single; simp
        · have hxne : x ≠ l.var := by intro he; subst he; exact hnd hxvs
          have hsne : single l.var false x = none := single_apply_ne l.var false x hxne
          have hov : overlay (single l.var false) (dirRestrQ vs (assignVar l.var false D)) x
              = dirRestrQ vs (assignVar l.var false D) x := by
            unfold overlay
            cases hd : dirRestrQ vs (assignVar l.var false D) x with
            | none => rw [hsne]
            | some b => rfl
          rw [if_neg hxne, hov]
          exact prefixRestr_deepPathVQ_eq_dirRestrQ vs (assignVar l.var false D) hsvs x hxvs
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-- **Block bridge (PROVED): `prefixRestr (deepPathV E)` agrees with `dirRestrBlock E` on
every variable of `E`'s HEAD term.**  Specializes the helper bridge to the top-level deep
walk: for `E = (l :: t) :: D` simple, on every variable `x` of the head term `l :: t`,
`prefixRestr (deepPathV E) x = dirRestrBlock E x`.  Combined with `factB`'s
`residualBlock_eq_dnfRestrict`, this lets the evolving state read the head block's deep
directions ρ-independently. -/
theorem prefixRestr_deepPathV_eq_dirRestrBlock {n : Nat} (l : Literal n) (t : Term n)
    (D : DNF n) (hD : SimpleDNF ((l :: t) :: D)) (x : Fin n)
    (hx : x ∈ (l :: t).map (·.var)) :
    prefixRestr (deepPathV ((l :: t) :: D)) x = dirRestrBlock ((l :: t) :: D) x := by
  have hst : SimpleTerm (l :: t) := hD (l :: t) (List.mem_cons_self _ _)
  have hnd : l.var ∉ t.map (·.var) := by
    unfold SimpleTerm at hst
    simp only [List.map_cons, List.nodup_cons] at hst; exact hst.1
  have hstt : SimpleTerm t := by
    unfold SimpleTerm at hst ⊢
    simp only [List.map_cons, List.nodup_cons] at hst; exact hst.2
  simp only [List.map_cons, List.mem_cons] at hx
  by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
      ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
  · rw [show deepPathV ((l :: t) :: D)
          = (l.var, true) :: deepPathVQ t (assignVar l.var true ((l :: t) :: D)) from by
        rw [deepPathV]; simp only [if_pos h]]
    rw [show dirRestrBlock ((l :: t) :: D)
          = overlay (single l.var true) (dirRestrQ t (assignVar l.var true ((l :: t) :: D)))
          from by rw [dirRestrBlock]; simp only [if_pos h]]
    rw [prefixRestr_cons]
    rcases hx with hxl | hxt
    · subst hxl
      have hτnone : dirRestrQ t (assignVar l.var true ((l :: t) :: D)) l.var = none :=
        dirRestrQ_apply_eq_none t (assignVar l.var true ((l :: t) :: D)) l.var hnd
      have hov : overlay (single l.var true)
          (dirRestrQ t (assignVar l.var true ((l :: t) :: D))) l.var
          = single l.var true l.var := overlay_eq_ρ_of_τ_none _ _ _ hτnone
      rw [hov]; unfold single; simp
    · have hxne : x ≠ l.var := by intro he; subst he; exact hnd hxt
      have hsne : single l.var true x = none := single_apply_ne l.var true x hxne
      have hov : overlay (single l.var true)
          (dirRestrQ t (assignVar l.var true ((l :: t) :: D))) x
          = dirRestrQ t (assignVar l.var true ((l :: t) :: D)) x := by
        unfold overlay
        cases hd : dirRestrQ t (assignVar l.var true ((l :: t) :: D)) x with
        | none => rw [hsne]
        | some b => rfl
      rw [if_neg hxne, hov]
      exact prefixRestr_deepPathVQ_eq_dirRestrQ t (assignVar l.var true ((l :: t) :: D))
        hstt x hxt
  · rw [show deepPathV ((l :: t) :: D)
          = (l.var, false) :: deepPathVQ t (assignVar l.var false ((l :: t) :: D)) from by
        rw [deepPathV]; simp only [if_neg h]]
    rw [show dirRestrBlock ((l :: t) :: D)
          = overlay (single l.var false) (dirRestrQ t (assignVar l.var false ((l :: t) :: D)))
          from by rw [dirRestrBlock]; simp only [if_neg h]]
    rw [prefixRestr_cons]
    rcases hx with hxl | hxt
    · subst hxl
      have hτnone : dirRestrQ t (assignVar l.var false ((l :: t) :: D)) l.var = none :=
        dirRestrQ_apply_eq_none t (assignVar l.var false ((l :: t) :: D)) l.var hnd
      have hov : overlay (single l.var false)
          (dirRestrQ t (assignVar l.var false ((l :: t) :: D))) l.var
          = single l.var false l.var := overlay_eq_ρ_of_τ_none _ _ _ hτnone
      rw [hov]; unfold single; simp
    · have hxne : x ≠ l.var := by intro he; subst he; exact hnd hxt
      have hsne : single l.var false x = none := single_apply_ne l.var false x hxne
      have hov : overlay (single l.var false)
          (dirRestrQ t (assignVar l.var false ((l :: t) :: D))) x
          = dirRestrQ t (assignVar l.var false ((l :: t) :: D)) x := by
        unfold overlay
        cases hd : dirRestrQ t (assignVar l.var false ((l :: t) :: D)) x with
        | none => rw [hsne]
        | some b => rfl
      rw [if_neg hxne, hov]
      exact prefixRestr_deepPathVQ_eq_dirRestrQ t (assignVar l.var false ((l :: t) :: D))
        hstt x hxt

/-! ## 2. Accumulated deep-direction restriction and the residual identity

`accumDir E j` overlays the deep-direction restrictions `dirRestrBlock` of the first `j`
term blocks, each computed on its own residual `residualIter E k`.  We prove
`residualIter E j = dnfRestrict (accumDir E j) E` for simple `E` (the deep walk after `j`
blocks is `E` restricted by the accumulated deep directions), by iterating
`residualBlock_eq_dnfRestrict`. -/

/-- **Support of `dirRestrQ`** (the converse of `dirRestrQ_apply_eq_none`): if
`dirRestrQ vars D x ≠ none` then `x` is a variable of `vars`. -/
theorem dirRestrQ_mem_of_some {n : Nat} (vars : Term n) (D : DNF n) (x : Fin n)
    (h : dirRestrQ vars D x ≠ none) : x ∈ vars.map (·.var) := by
  by_contra hx
  exact h (dirRestrQ_apply_eq_none vars D x hx)

/-- **Support of `dirRestrBlock`:** if `dirRestrBlock E x ≠ none` then `x` is a variable of
`E`'s head term, hence there is a term `t ∈ E` and literal `l ∈ t` with `l.var = x`. -/
theorem dirRestrBlock_some_mem {n : Nat} (E : DNF n) (x : Fin n)
    (h : dirRestrBlock E x ≠ none) : ∃ t ∈ E, ∃ l ∈ t, l.var = x := by
  cases E with
  | nil => rw [show dirRestrBlock ([] : DNF n) = (fun _ => none) from by rw [dirRestrBlock]] at h; exact absurd rfl h
  | cons term Ds =>
      cases term with
      | nil =>
          rw [show dirRestrBlock (([] : Term n) :: Ds) = (fun _ => none) from by rw [dirRestrBlock]] at h
          exact absurd rfl h
      | cons l t =>
          -- x is a variable of l :: t
          have hx : x ∈ (l :: t).map (·.var) := by
            by_contra hx
            -- dirRestrBlock ((l::t)::Ds) x = overlay (single l.var dir) (dirRestrQ t ...) x
            -- on x ∉ (l::t) vars, both single and dirRestrQ are none
            simp only [List.map_cons, List.mem_cons, not_or] at hx
            obtain ⟨hxl, hxt⟩ := hx
            apply h
            rw [dirRestrBlock]
            by_cases hd : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: Ds)))
                ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: Ds)))
            · simp only [if_pos hd]
              unfold overlay
              rw [dirRestrQ_apply_eq_none t (assignVar l.var true ((l :: t) :: Ds)) x hxt]
              exact single_apply_ne l.var true x hxl
            · simp only [if_neg hd]
              unfold overlay
              rw [dirRestrQ_apply_eq_none t (assignVar l.var false ((l :: t) :: Ds)) x hxt]
              exact single_apply_ne l.var false x hxl
          rw [List.mem_map] at hx
          obtain ⟨l', hl', hl'v⟩ := hx
          exact ⟨l :: t, List.mem_cons_self _ _, l', hl', hl'v⟩

/-- The accumulated deep-direction restriction of the first `j` term blocks of `E`. -/
noncomputable def accumDir {n : Nat} (E : DNF n) : Nat → Restriction n
  | 0 => (fun _ => none)
  | (j + 1) => overlay (accumDir E j) (dirRestrBlock (residualIter E j))

/-- `dnfRestrict (overlay ρ τ)` composes as `dnfRestrict τ ∘ dnfRestrict ρ` when `τ` is
disjoint from `ρ`'s domain.  (Re-export of `dnfRestrict_overlay` for local use.) -/
theorem dnfRestrict_overlay' {n : Nat} (ρ τ : Restriction n) (E : DNF n)
    (hdisj : ∀ v, ρ v ≠ none → τ v = none) :
    dnfRestrict (overlay ρ τ) E = dnfRestrict τ (dnfRestrict ρ E) :=
  dnfRestrict_overlay ρ τ E hdisj

/-- The accumulated restriction `accumDir E j` is DISJOINT from `dirRestrBlock (residualIter
E j)`: the new block's deep variables are FREE in the accumulated restriction, because
`residualIter E j = dnfRestrict (accumDir E j) E`'s literals are on `accumDir`-free
variables (`dnfRestrict_var_free`), and `dirRestrBlock (residualIter E j)` only fixes
variables of that residual's head term.  PROVED below as part of the residual identity. -/
theorem residualIter_eq_dnfRestrict_accumDir {n : Nat} :
    ∀ (j : Nat) {E : DNF n}, SimpleDNF E →
      residualIter E j = dnfRestrict (accumDir E j) E
  | 0, E, _ => by
      rw [residualIter, accumDir, dnfRestrict_none_id]

  | (j + 1), E, hE => by
      have hsimp : SimpleDNF (residualIter E j) := simpleDNF_residualIter j hE
      have hReq : residualIter E j = dnfRestrict (accumDir E j) E :=
        residualIter_eq_dnfRestrict_accumDir j hE
      -- disjointness: dirRestrBlock (residualIter E j) fixes only head-term variables, accumDir-free
      have hdisj : ∀ v, (accumDir E j) v ≠ none → dirRestrBlock (residualIter E j) v = none := by
        intro v hv
        by_contra hne
        obtain ⟨t, ht, l, hl, hlv⟩ := dirRestrBlock_some_mem (residualIter E j) v hne
        have hfree : (accumDir E j) l.var = none := by
          rw [hReq] at ht
          exact dnfRestrict_var_free (accumDir E j) E t ht l hl
        rw [hlv] at hfree
        exact hv hfree
      calc residualIter E (j + 1)
          = residualBlock (residualIter E j) := residualIter_succ j E
        _ = dnfRestrict (dirRestrBlock (residualIter E j)) (residualIter E j) :=
              residualBlock_eq_dnfRestrict (residualIter E j) hsimp
        _ = dnfRestrict (dirRestrBlock (residualIter E j))
              (dnfRestrict (accumDir E j) E) := by rw [hReq]
        _ = dnfRestrict (overlay (accumDir E j) (dirRestrBlock (residualIter E j))) E :=
              (dnfRestrict_overlay' (accumDir E j) (dirRestrBlock (residualIter E j)) E hdisj).symm
        _ = dnfRestrict (accumDir E (j + 1)) E := by rw [accumDir]

/-! ## 3. Multi-block bridge: `prefixRestr (deepPathV E)` records `accumDir E j`

The deep walk `deepPathV E` emits the deep `(var, dir)` pairs block by block; the first `j`
blocks' fixings are exactly `accumDir E j`.  We prove that on every variable FIXED by
`accumDir E j`, `prefixRestr (deepPathV E)` returns the same value.  Proof by induction on
`j`, peeling the `(j)`-th block via the drop law `deepPathV_residualIter` (so the j-th block
of `deepPathV E` is the head block of `deepPathV (residualIter E j)`) and the head-block
bridge `prefixRestr_deepPathV_eq_dirRestrBlock`, using that the prefix's FIRST occurrence of
a variable is its earliest (deep-path-distinct) fixing. -/

/-- A variable fixed by `dirRestrBlock (residualIter E j)` is a variable of the j-th deep
block (= head term of the j-th residual), hence appears in `deepPathV E` (within the j-th
block segment).  We package the membership needed for the bridge. -/
theorem accumDir_some_mem_deepPathV {n : Nat} (E : DNF n) (hE : SimpleDNF E) :
    ∀ (j : Nat) (x : Fin n), accumDir E j x ≠ none →
      x ∈ (deepPathV E).map Prod.fst := by
  intro j
  induction j with
  | zero => intro x hx; rw [accumDir] at hx; exact absurd rfl hx
  | succ j ih =>
      intro x hx
      rw [accumDir] at hx
      -- overlay (accumDir E j) (dirRestrBlock (residualIter E j)) x ≠ none
      by_cases hd : dirRestrBlock (residualIter E j) x = none
      · -- then accumDir E j x ≠ none (overlay falls through to accumDir)
        have : accumDir E j x ≠ none := by
          rw [overlay_eq_ρ_of_τ_none _ _ _ hd] at hx; exact hx
        exact ih x this
      · -- x is a variable of the j-th residual's head term; appears in deepPathV E
        -- abstract the residual so `cases` does not disturb the outer membership goal
        have key : ∀ (R : DNF n), dirRestrBlock R x ≠ none →
            x ∈ (deepPathV R).map Prod.fst := by
          intro R hdR
          cases R with
          | nil =>
              rw [show dirRestrBlock ([] : DNF n) = (fun _ => none) from by rw [dirRestrBlock]] at hdR
              exact absurd rfl hdR
          | cons term Ds =>
              cases term with
              | nil =>
                  rw [show dirRestrBlock (([] : Term n) :: Ds) = (fun _ => none) from by
                    rw [dirRestrBlock]] at hdR
                  exact absurd rfl hdR
              | cons l0 t0 =>
                  have hxhead : x ∈ (l0 :: t0).map (·.var) := by
                    by_contra hxn
                    apply hdR
                    rw [dirRestrBlock]
                    simp only [List.map_cons, List.mem_cons, not_or] at hxn
                    obtain ⟨hxl0, hxt0⟩ := hxn
                    by_cases hcmp : dtDepth (queryTerm t0 (assignVar l0.var false ((l0 :: t0) :: Ds)))
                        ≤ dtDepth (queryTerm t0 (assignVar l0.var true ((l0 :: t0) :: Ds)))
                    · simp only [if_pos hcmp]
                      unfold overlay
                      rw [dirRestrQ_apply_eq_none t0 (assignVar l0.var true ((l0 :: t0) :: Ds)) x hxt0]
                      exact single_apply_ne l0.var true x hxl0
                    · simp only [if_neg hcmp]
                      unfold overlay
                      rw [dirRestrQ_apply_eq_none t0 (assignVar l0.var false ((l0 :: t0) :: Ds)) x hxt0]
                      exact single_apply_ne l0.var false x hxl0
                  have htake : ((deepPathV ((l0 :: t0) :: Ds)).map Prod.fst).take (1 + t0.length)
                      = (l0 :: t0).map (·.var) := deepPathV_cons_cons_take l0 t0 Ds
                  have hmt : x ∈ ((deepPathV ((l0 :: t0) :: Ds)).map Prod.fst).take (1 + t0.length) := by
                    rw [htake]; exact hxhead
                  exact List.mem_of_mem_take hmt
        have hxR : x ∈ (deepPathV (residualIter E j)).map Prod.fst := key (residualIter E j) hd
        rw [deepPathV_residualIter, List.map_drop] at hxR
        exact List.mem_of_mem_drop hxR

/-- `prefixRestr` is unchanged by dropping a prefix that does not contain `x`: if `x` is
not among the variables of `L.take k`, then `prefixRestr L x = prefixRestr (L.drop k) x`
(the first occurrence of `x` lies in the dropped tail). -/
theorem prefixRestr_drop_eq_of_not_mem_take {n : Nat} (L : List (Fin n × Bool)) (k : Nat)
    (x : Fin n) (hx : x ∉ (L.take k).map Prod.fst) :
    prefixRestr L x = prefixRestr (L.drop k) x := by
  unfold prefixRestr
  congr 1
  conv_lhs => rw [← List.take_append_drop k L]
  rw [List.find?_append]
  have hnone : (L.take k).find? (fun vd => vd.1 = x) = none := by
    rw [List.find?_eq_none]
    intro vd hvd
    simp only [decide_eq_true_eq]
    intro hcon
    exact hx (by rw [List.mem_map]; exact ⟨vd, hvd, hcon⟩)
  rw [hnone]
  simp

/-- If `(L.map fst)` is `Nodup` and `x ∈ (L.drop k).map fst`, then `x ∉ (L.take k).map fst`
(else `x` would appear twice in `L.map fst`). -/
theorem not_mem_take_of_mem_drop_nodup {n : Nat} (L : List (Fin n × Bool)) (k : Nat)
    (x : Fin n) (hnd : (L.map Prod.fst).Nodup) (hx : x ∈ (L.drop k).map Prod.fst) :
    x ∉ (L.take k).map Prod.fst := by
  intro hxt
  -- L.map fst = (take k).map fst ++ (drop k).map fst, and x is in both
  have hsplit : (L.map Prod.fst) = (L.take k).map Prod.fst ++ (L.drop k).map Prod.fst := by
    rw [← List.map_append, List.take_append_drop]
  rw [hsplit] at hnd
  exact (List.disjoint_of_nodup_append hnd) hxt hx

/-- **Multi-block bridge (PROVED): `prefixRestr (deepPathV E)` records `accumDir E j`.**
On every variable FIXED by the accumulated deep-direction restriction of the first `j`
blocks, `prefixRestr (deepPathV E)` returns the same value.  Induction on `j`: the new
block's directions are read off the head block of `deepPathV (residualIter E j)` (the block
bridge), which is a `drop` of `deepPathV E` (drop law); the deep-path NODUP (distinct
variables) lets the prefix's first occurrence ignore the already-processed prefix. -/
theorem prefixRestr_deepPathV_eq_accumDir {n : Nat} (E : DNF n) (hE : SimpleDNF E) :
    ∀ (j : Nat) (x : Fin n), accumDir E j x ≠ none →
      prefixRestr (deepPathV E) x = accumDir E j x := by
  have hnd : ((deepPathV E).map Prod.fst).Nodup := by
    -- deepPathV E = deepestPath (termCanonicalDT E), nodup under SimpleDNF
    rw [deepPathV_eq]
    exact deepestPath_nodup _ (distinctPaths_termCanonicalDT _ hE)
  intro j
  induction j with
  | zero => intro x hx; rw [accumDir] at hx; exact absurd rfl hx
  | succ j ih =>
      intro x hx
      rw [accumDir] at hx ⊢
      by_cases hd : dirRestrBlock (residualIter E j) x = none
      · -- overlay falls through to accumDir E j
        rw [overlay_eq_ρ_of_τ_none _ _ _ hd] at hx ⊢
        exact ih x hx
      · -- overlay = dirRestrBlock (residualIter E j) x = some b; read from the j-th block
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hd
        rw [overlay_eq_some_of_τ _ _ _ b hb]
        have hsimp : SimpleDNF (residualIter E j) := simpleDNF_residualIter j hE
        -- block bridge on the residual: prefixRestr (deepPathV R) x = dirRestrBlock R x
        have hbridge : prefixRestr (deepPathV (residualIter E j)) x
            = dirRestrBlock (residualIter E j) x := by
          cases hR : residualIter E j with
          | nil =>
              rw [hR] at hd
              rw [show dirRestrBlock ([] : DNF n) = (fun _ => none) from by rw [dirRestrBlock]] at hd
              exact absurd rfl hd
          | cons term Ds =>
              cases term with
              | nil =>
                  rw [hR] at hd
                  rw [show dirRestrBlock (([] : Term n) :: Ds) = (fun _ => none) from by
                    rw [dirRestrBlock]] at hd
                  exact absurd rfl hd
              | cons l0 t0 =>
                  have hdR : dirRestrBlock ((l0 :: t0) :: Ds) x ≠ none := by rw [← hR]; exact hd
                  have hxhead : x ∈ (l0 :: t0).map (·.var) := by
                    by_contra hxn
                    apply hdR
                    rw [dirRestrBlock]
                    simp only [List.map_cons, List.mem_cons, not_or] at hxn
                    obtain ⟨hxl0, hxt0⟩ := hxn
                    by_cases hcmp : dtDepth (queryTerm t0 (assignVar l0.var false ((l0 :: t0) :: Ds)))
                        ≤ dtDepth (queryTerm t0 (assignVar l0.var true ((l0 :: t0) :: Ds)))
                    · simp only [if_pos hcmp]
                      unfold overlay
                      rw [dirRestrQ_apply_eq_none t0 (assignVar l0.var true ((l0 :: t0) :: Ds)) x hxt0]
                      exact single_apply_ne l0.var true x hxl0
                    · simp only [if_neg hcmp]
                      unfold overlay
                      rw [dirRestrQ_apply_eq_none t0 (assignVar l0.var false ((l0 :: t0) :: Ds)) x hxt0]
                      exact single_apply_ne l0.var false x hxl0
                  have hsimp' : SimpleDNF ((l0 :: t0) :: Ds) := by rw [← hR]; exact hsimp
                  exact prefixRestr_deepPathV_eq_dirRestrBlock l0 t0 Ds hsimp' x hxhead
        -- relate deepPathV (residualIter E j) to a drop of deepPathV E
        have hdrop : deepPathV (residualIter E j)
            = (deepPathV E).drop (startLen (deepBlockLens E) j) := deepPathV_residualIter j E
        rw [hdrop] at hbridge
        -- x ∈ drop (since prefixRestr returns some) ⇒ x ∉ take ⇒ prefixRestr unaffected by drop
        have hxdrop : x ∈ ((deepPathV E).drop (startLen (deepBlockLens E) j)).map Prod.fst := by
          by_contra hxn
          rw [prefixRestr_eq_none _ x hxn] at hbridge
          rw [hb] at hbridge; exact absurd hbridge.symm (by simp)
        have hnottake : x ∉ ((deepPathV E).take (startLen (deepBlockLens E) j)).map Prod.fst :=
          not_mem_take_of_mem_drop_nodup (deepPathV E) _ x hnd hxdrop
        rw [prefixRestr_drop_eq_of_not_mem_take (deepPathV E) _ x hnottake, hbridge, hb]

/-- `startLen` is monotone in its block count: `startLen bs j ≤ startLen bs (j+1)`. -/
theorem startLen_le_succ {n : Nat} (E : DNF n) (j : Nat) :
    startLen (deepBlockLens E) j ≤ startLen (deepBlockLens E) (j + 1) := by
  -- startLen bs (j+1) = (drop-style sum); use the residual peel identity
  -- startLen bs (j+1) = startLen bs j + (j-th block length); monotone.
  -- We prove the generic list fact by induction on the list and j.
  have gen : ∀ (bs : List Nat) (j : Nat), startLen bs j ≤ startLen bs (j + 1) := by
    intro bs
    induction bs with
    | nil => intro j; cases j <;> simp [startLen]
    | cons b bs ih =>
        intro j
        cases j with
        | zero => simp [startLen]
        | succ j => simp only [startLen]; exact Nat.add_le_add_left (ih j) b
  exact gen (deepBlockLens E) j

/-- `startLen bs (j+1) = startLen bs j + (bs.drop j).headI`: the start of block `j+1` is the
start of block `j` plus the `j`-th block's length. -/
theorem startLen_succ_eq : ∀ (bs : List Nat) (j : Nat),
    startLen bs (j + 1) = startLen bs j + (bs.drop j).headI
  | [], j => by cases j <;> simp [startLen]
  | b :: bs, 0 => by simp [startLen]
  | b :: bs, (j + 1) => by
      simp only [startLen, List.drop_succ_cons]
      rw [startLen_succ_eq bs j]; omega

/-- A variable fixed by `accumDir E j` lies among the FIRST `startLen (deepBlockLens E) j`
entries of `deepPathV E` (it is a variable of one of the first `j` blocks).  Induction on
`j`: the new block's variables are the head block of `deepPathV (residualIter E j)` =
`drop (startLen … j)` of `deepPathV E`, within its own block length, hence within
`take (startLen … (j+1))`. -/
theorem accumDir_mem_take_startLen {n : Nat} (E : DNF n) (hE : SimpleDNF E) :
    ∀ (j : Nat) (x : Fin n), accumDir E j x ≠ none →
      x ∈ ((deepPathV E).take (startLen (deepBlockLens E) j)).map Prod.fst := by
  intro j
  induction j with
  | zero => intro x hx; rw [accumDir] at hx; exact absurd rfl hx
  | succ j ih =>
      intro x hx
      rw [accumDir] at hx
      by_cases hd : dirRestrBlock (residualIter E j) x = none
      · -- fixed by accumDir E j: in first j blocks ⊆ first j+1 blocks (take monotone)
        have haj : accumDir E j x ≠ none := by
          rw [overlay_eq_ρ_of_τ_none _ _ _ hd] at hx; exact hx
        have hmem := ih x haj
        have hle : startLen (deepBlockLens E) j ≤ startLen (deepBlockLens E) (j + 1) :=
          startLen_le_succ E j
        rw [List.mem_map] at hmem ⊢
        obtain ⟨vd, hvd, hvdx⟩ := hmem
        exact ⟨vd, List.mem_of_mem_take (by
          rw [List.take_take, Nat.min_eq_left hle]; exact hvd), hvdx⟩
      · -- fixed by the j-th block: in deepPathV (residualIter E j) head block
        have hdrop : deepPathV (residualIter E j)
            = (deepPathV E).drop (startLen (deepBlockLens E) j) := deepPathV_residualIter j E
        -- x is within the HEAD block of the residual: take (headLen) of its deep path
        have hhead : x ∈ ((deepPathV (residualIter E j)).take
            (deepBlockLens (residualIter E j)).headI).map Prod.fst := by
          -- dirRestrBlock fixes only the head term's vars; head block = those vars in order
          cases hR : residualIter E j with
          | nil =>
              rw [hR] at hd
              rw [show dirRestrBlock ([] : DNF n) = (fun _ => none) from by rw [dirRestrBlock]] at hd
              exact absurd rfl hd
          | cons term Ds =>
              cases term with
              | nil =>
                  rw [hR] at hd
                  rw [show dirRestrBlock (([] : Term n) :: Ds) = (fun _ => none) from by
                    rw [dirRestrBlock]] at hd
                  exact absurd rfl hd
              | cons l0 t0 =>
                  have hdR : dirRestrBlock ((l0 :: t0) :: Ds) x ≠ none := by rw [← hR]; exact hd
                  have hxhead : x ∈ (l0 :: t0).map (·.var) := by
                    by_contra hxn
                    apply hdR
                    rw [dirRestrBlock]
                    simp only [List.map_cons, List.mem_cons, not_or] at hxn
                    obtain ⟨hxl0, hxt0⟩ := hxn
                    by_cases hcmp : dtDepth (queryTerm t0 (assignVar l0.var false ((l0 :: t0) :: Ds)))
                        ≤ dtDepth (queryTerm t0 (assignVar l0.var true ((l0 :: t0) :: Ds)))
                    · simp only [if_pos hcmp]
                      unfold overlay
                      rw [dirRestrQ_apply_eq_none t0 (assignVar l0.var true ((l0 :: t0) :: Ds)) x hxt0]
                      exact single_apply_ne l0.var true x hxl0
                    · simp only [if_neg hcmp]
                      unfold overlay
                      rw [dirRestrQ_apply_eq_none t0 (assignVar l0.var false ((l0 :: t0) :: Ds)) x hxt0]
                      exact single_apply_ne l0.var false x hxl0
                  -- head block: take (headI of deepBlockLens) = first term's vars
                  have hbl : (deepBlockLens ((l0 :: t0) :: Ds)).headI = 1 + t0.length := by
                    rw [deepBlockLens_cons_cons_eq]; rfl
                  have htake : ((deepPathV ((l0 :: t0) :: Ds)).map Prod.fst).take (1 + t0.length)
                      = (l0 :: t0).map (·.var) := deepPathV_cons_cons_take l0 t0 Ds
                  rw [List.map_take, hbl, htake]
                  exact hxhead
        -- combine: take headLen of (drop (start j)) ⊆ take (start j + headLen) = take (start (j+1))
        rw [hdrop] at hhead
        have hsl : startLen (deepBlockLens E) (j + 1)
            = startLen (deepBlockLens E) j + (deepBlockLens (residualIter E j)).headI := by
          rw [startLen_succ_eq, deepBlockLens_residualIter]
        rw [hsl]
        -- hhead : x ∈ map fst (take headLen (drop (start j) L)); extract vd
        rw [List.mem_map] at hhead ⊢
        obtain ⟨vd, hvd, hvdx⟩ := hhead
        refine ⟨vd, ?_, hvdx⟩
        -- vd ∈ take headLen (drop (start j) L); take_drop ⇒ vd ∈ drop (start j) (take (start j + headLen) L)
        rw [List.take_drop] at hvd
        exact List.mem_of_mem_drop hvd

/-! ## 4. Prefix-restriction form on the actual decoder prefix

The decoder uses `prev = (deepPathV (D|ρ)).take (start j)` where `start j = startLen
(deepBlockLens (D|ρ)) j` is the global start index of block `j`.  On a variable fixed by
`accumDir (D|ρ) j` (a variable of the first `j` blocks, hence at a deep-path position
`< start j`), `prefixRestr` of the TAKEN prefix agrees with `prefixRestr` of the full path,
hence with `accumDir`. -/

/-- A variable fixed by `accumDir E j` has its first deep-path occurrence within the first
`startLen (deepBlockLens E) j` entries — so `prefixRestr (take (startLen …)) ` agrees with
`prefixRestr (full path)` on it.  We prove the `prefixRestr`-agreement directly: the j-th
block variables all lie in the first `start j` entries (they ARE the first `j` blocks), so
restricting `prefixRestr` to the prefix does not change their first occurrence. -/
theorem prefixRestr_take_eq_accumDir {n : Nat} (E : DNF n) (hE : SimpleDNF E)
    (j : Nat) (x : Fin n) (hx : accumDir E j x ≠ none) :
    prefixRestr ((deepPathV E).take (startLen (deepBlockLens E) j)) x = accumDir E j x := by
  -- It suffices to show prefixRestr (take k) x = prefixRestr (full) x, then apply the bridge.
  set k := startLen (deepBlockLens E) j with hk
  have hbridge := prefixRestr_deepPathV_eq_accumDir E hE j x hx
  -- x is a variable of the first j blocks; show x ∈ take k.  We get this from the bridge:
  -- prefixRestr (full) x = accumDir E j x ≠ none, so x is on the path; and its position is
  -- in block < j, i.e. < k.  Rather than locate the position, use: the value `accumDir E j x`
  -- is recorded by the j-th-or-earlier block, all within take k.  We prove via the recursive
  -- structure that x ∈ (take k).map fst.
  have hmem : x ∈ ((deepPathV E).take k).map Prod.fst := accumDir_mem_take_startLen E hE j x hx
  -- prefixRestr (full) = prefixRestr (take k) on x, since x's first occurrence is in take k
  have heq : prefixRestr (deepPathV E) x = prefixRestr ((deepPathV E).take k) x := by
    have hsplit : prefixRestr (deepPathV E) x
        = prefixRestr ((deepPathV E).take k ++ (deepPathV E).drop k) x := by
      rw [List.take_append_drop]
    rw [hsplit]
    unfold prefixRestr
    congr 1
    rw [List.find?_append]
    -- find? in take k is `some` (x is there), so the append is just that
    cases hf : ((deepPathV E).take k).find? (fun vd => vd.1 = x) with
    | some p => rfl
    | none =>
        exfalso
        rw [List.find?_eq_none] at hf
        rw [List.mem_map] at hmem
        obtain ⟨vd, hvd, hvdx⟩ := hmem
        have := hf vd hvd
        simp only [decide_eq_true_eq] at this
        exact this hvdx
  rw [← heq, hbridge]

/-- A literal of the ρ-RESTRICTED term `Cr = termRestrict ρ C₀` is a literal of the original
term `C₀` (restriction keeps free literals and drops/falsifies fixed ones). -/
theorem termRestrict_mem_of_mem {n : Nat} (ρ : Restriction n) :
    ∀ (C₀ Cr : Term n), termRestrict ρ C₀ = some Cr → ∀ l ∈ Cr, l ∈ C₀
  | [], Cr, h, l, hl => by
      simp only [termRestrict, Option.some.injEq] at h; subst h; exact absurd hl (List.not_mem_nil l)
  | m :: t, Cr, h, l, hl => by
      simp only [termRestrict] at h
      cases hρ : ρ m.var with
      | none =>
          rw [hρ] at h
          cases hr : termRestrict ρ t with
          | none => rw [hr] at h; simp at h
          | some t' =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hl with hlm | hlt
              · subst hlm; exact List.mem_cons_self _ _
              · exact List.mem_cons_of_mem m (termRestrict_mem_of_mem ρ t t' hr l hlt)
      | some b =>
          rw [hρ] at h
          by_cases hb : b = m.sign
          · simp only [if_pos hb] at h
            exact List.mem_cons_of_mem m (termRestrict_mem_of_mem ρ t Cr h l hl)
          · simp only [if_neg hb] at h; simp at h

/-! ## 5. The genuine (A) prefix-falsification content (PROVED)

Using the bridge, we close the genuinely-NEW order content: a D-original term whose
ρ-restriction is FALSIFIED by the first-`j`-block deep directions (`accumDir (D|ρ) j`) —
i.e. a term filtered out of the residual before block `j` (the task's "killed by an earlier
block's π-fixings" case) — is FALSIFIED under the evolving decoder state
`state = stateAt σ_loc ((deepPathV (D|ρ)).take (start j))`.  This is the order-argument
class that FACT (b) / `processedDeepTerm_falsified_stateAt` needed the prefix↔deep-direction
bridge to supply, now PROVED. -/

/-- **(A) prefix-falsification — accumDir-killed terms (PROVED).**  Let `E = D|ρ` be simple
and `C₀` a D-original term whose ρ-restriction `C := termRestrict ρ C₀` is defined
(`= some Cr`) and is FALSIFIED by the accumulated first-`j`-block deep directions
(`termRestrict (accumDir E j) Cr = none`).  Then `C₀` is FALSIFIED under the evolving state
`stateAt σ_loc ((deepPathV E).take (start j))` (`start j = startLen (deepBlockLens E) j`).
The offending literal of `Cr` (on an `accumDir`-fixed variable, which is in the recorded
prefix by `prefixRestr_take_eq_accumDir`) sits on a deep variable; it lies in `C₀` too (the
restricted literal list is a sub-list of `C₀`), and the prefix fixes it against its sign. -/
theorem accumDir_killed_falsified_stateAt {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (hD : SimpleDNF D) (j : Nat)
    (C₀ Cr : Term n) (hres : termRestrict ρ C₀ = some Cr)
    (hkill : termRestrict (accumDir (dnfRestrict ρ D) j) Cr = none) :
    termRestrict (stateAt (encodeLoc₁ D s ρ)
        ((deepPathV (dnfRestrict ρ D)).take
          (startLen (deepBlockLens (dnfRestrict ρ D)) j)) ) C₀ = none := by
  set E := dnfRestrict ρ D
  have hEsimp : SimpleDNF E := simpleDNF_dnfRestrict hD ρ
  -- offending literal of Cr fixed against its sign by accumDir E j
  obtain ⟨l, hlCr, c, hc, hcs⟩ :=
    SwitchingStepData.termRestrict_none_witness (accumDir E j) Cr hkill
  -- l lies in C₀ as well: termRestrict ρ C₀ = some Cr means Cr is C₀ filtered; l ∈ Cr ⇒ l ∈ C₀
  have hlC0 : l ∈ C₀ := termRestrict_mem_of_mem ρ C₀ Cr hres l hlCr
  -- l.var is fixed by accumDir E j (to c ≠ l.sign); hence recorded in the prefix
  have hacc_ne : accumDir E j l.var ≠ none := by rw [hc]; simp
  have hpref : prefixRestr ((deepPathV E).take (startLen (deepBlockLens E) j)) l.var = some c := by
    rw [prefixRestr_take_eq_accumDir E hEsimp j l.var hacc_ne]; exact hc
  -- under stateAt = overlay σ_loc prefix, the prefix fixes l.var to c ≠ l.sign ⇒ C₀ falsified
  rw [stateAt]
  exact termRestrict_overlay_none_of_lit (encodeLoc₁ D s ρ)
    ((deepPathV E).take (startLen (deepBlockLens E) j)) C₀ l hlC0 c hpref hcs

end SwitchingOrder
end PvNP
