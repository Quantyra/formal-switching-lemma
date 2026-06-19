/-
# FACT (b): the deep walk falsifies every term it processes and continues past

This file proves the concrete structural lemma the sibling files
(`SwitchingDecodeRef.obstruction_note` point (b), `SwitchingClose` honesty note)
isolate as the open Razborov "π-advance FALSIFICATION linchpin":

  *Along the deep walk of `termCanonicalDT (D|ρ)`, each term the walk PROCESSES AND
  CONTINUES PAST is FALSIFIED by the deep-path directions on that term's queried
  variables.*

The mechanism (proved here, not assumed): the term-canonical tree only CONTINUES
past a term whose own deep directions KILLED it.  A term SATISFIED by its own
directions collapses to the constant-true `[]` under residualization, making the
residual DNF headed by `[]`, so `termCanonicalDT ([] :: _) = leaf true` (depth 0)
and the deep walk STOPS.  Contrapositive: if the walk continues, the term was
falsified.

## What is PROVED here (HONEST scope)

* `residualBlock_eq_dnfRestrict_dirRestr` — the residual after a deep term block is
  EXACTLY `dnfRestrict` by the block's deep-direction restriction (bridging the
  `assignVar`-based deep walk to the restriction algebra, via the proved
  `assignVar_eq_single` / `dnfRestrict_single_comp`), under `SimpleDNF`
  distinctness.
* `factB_block_dichotomy` — for a simple DNF whose first term is `l :: t`: EITHER
  the first term is FALSIFIED by its block's deep directions
  (`termRestrict (dirRestr …) (l :: t) = none`), OR the deep walk on the residual is
  EMPTY (`deepPathV (residualBlock …) = []`, i.e. the walk stopped).
* `factB_processed_falsified` — the contrapositive packaging (FACT (b)): if the deep
  walk CONTINUES past the first term block (`deepPathV (residualBlock …) ≠ []`), then
  the first term is FALSIFIED by its block's deep directions.
* `factB_iter` — the iterated/per-step form along `residualIter`: each block the deep
  walk processes and continues past has its term falsified, expressed via
  `deepResidual_head` so it speaks about the j-th deep block of `D|ρ`.

## What is NOT closed (the remaining obstruction, unchanged)

FACT (b) supplies the "earlier deep terms are ρ-falsified" hypothesis that
`SwitchingDeepAux.firstSat_eq_of_ρ_falsified_prefix` needs.  But the ASSEMBLY to
`RCodeBlockStepVar` / `SwitchingLemmaTermSimple` additionally needs the decode to be
ρ-INDEPENDENT, and the residual `residualIter (D|ρ) j` is built from `D|ρ` (needs ρ);
the `σ_loc` available to the decoder fixes the not-yet-decoded touched variables to
their SATISFYING values, which collapse the current deep term and ERASE the variable
to be recovered.  That ρ-elimination is the convention-independent Razborov content
isolated (unchanged) as `ResidualHeadDecode` / `DeepBlockRecoverableW`.  We do NOT
fake it; see the honesty note at the end.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed axioms
⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.  The
imported files are untouched.
-/
import PvNP.SwitchingDecodeRef

namespace PvNP
namespace SwitchingFactB

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct
open SwitchingEncodeLocal
open SwitchingDeepAux
open SwitchingClose
open SwitchingDecodeRef
open Classical

/-! ## 1. The deep-direction restriction of a block, built along the recursion

`dirRestrQ vars D` collects the single fixings `v ↦ deepDir` for every variable of
`vars` along the deep walk (the SAME branch `residualQ`/`deepPathVQ` descend into),
overlaid into one `Restriction`.  `dirRestrBlock` does the same for the first whole
term block (mirroring `deepPathV`/`residualBlock`).  These mirror
`residualQ`/`residualBlock` exactly, so we can prove `residualQ vars D =
dnfRestrict (dirRestrQ vars D) D` by the same recursion. -/

/-- The single fixing `v ↦ b`. -/
def single {n : Nat} (v : Fin n) (b : Bool) : Restriction n :=
  fun x => if x = v then some b else none

/-- The deep-direction restriction collected along the block helper.  Built so that
`overlay (single l.var d) (dirRestrQ …)` matches `dnfRestrict_single_comp`. -/
def dirRestrQ {n : Nat} : Term n → DNF n → Restriction n
  | [], _ => (fun _ => none)
  | l :: vs, D =>
      if dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
        then overlay (single l.var true) (dirRestrQ vs (assignVar l.var true D))
        else overlay (single l.var false) (dirRestrQ vs (assignVar l.var false D))
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

/-- The deep-direction restriction of the first whole term block. -/
def dirRestrBlock {n : Nat} : DNF n → Restriction n
  | [] => (fun _ => none)
  | [] :: _ => (fun _ => none)
  | (l :: t) :: D =>
      if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
        then overlay (single l.var true) (dirRestrQ t (assignVar l.var true ((l :: t) :: D)))
        else overlay (single l.var false) (dirRestrQ t (assignVar l.var false ((l :: t) :: D)))

/-! ## 2. Support of `dirRestrQ`: it only fixes variables of `vars`

`dirRestrQ vars D` overlays single fixings `v ↦ deepDir` only for variables `v` of
`vars`.  Hence a variable NOT among `vars`' variables is left free.  This is the
disjointness side-condition `dnfRestrict_single_comp` requires, supplied for the
head literal via `SimpleTerm` distinctness. -/

/-- `single v b x = none` for `x ≠ v`. -/
theorem single_apply_ne {n : Nat} (v : Fin n) (b : Bool) (x : Fin n) (h : x ≠ v) :
    single v b x = none := by unfold single; rw [if_neg h]

/-- **Support of `dirRestrQ`.**  If `x` is not a variable of `vars`, then
`dirRestrQ vars D x = none`. -/
theorem dirRestrQ_apply_eq_none {n : Nat} :
    ∀ (vars : Term n) (D : DNF n) (x : Fin n),
      x ∉ vars.map (·.var) → dirRestrQ vars D x = none
  | [], _, x, _ => by rw [dirRestrQ]
  | l :: vs, D, x, hx => by
      simp only [List.map_cons, List.mem_cons, not_or] at hx
      obtain ⟨hxl, hxvs⟩ := hx
      rw [dirRestrQ]
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · simp only [if_pos h]
        unfold overlay
        rw [dirRestrQ_apply_eq_none vs (assignVar l.var true D) x hxvs]
        exact single_apply_ne l.var true x hxl
      · simp only [if_neg h]
        unfold overlay
        rw [dirRestrQ_apply_eq_none vs (assignVar l.var false D) x hxvs]
        exact single_apply_ne l.var false x hxl
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-! ## 3. The residual = `dnfRestrict` by the deep-direction restriction (bridge)

`residualQ vars D` applies `assignVar v dir` (= single-fixing `dnfRestrict`, by
`assignVar_eq_single`) once per variable of `vars` along the deep walk, then returns
the DNF.  Collapsing the iterate into ONE `dnfRestrict (dirRestrQ vars D)` requires
the per-step disjointness `P l.var = none` (so `dnfRestrict_single_comp` applies),
which holds under `SimpleTerm vars` (distinct variables) via
`dirRestrQ_apply_eq_none`.  This is the bridge from the `assignVar`-based deep walk to
the restriction algebra. -/

/-- **The block residual is `dnfRestrict` by its deep-direction restriction (PROVED,
helper).**  For a SIMPLE literal list `vars`, `residualQ vars D = dnfRestrict
(dirRestrQ vars D) D`. -/
theorem residualQ_eq_dnfRestrict {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), SimpleTerm vars →
      residualQ vars D = dnfRestrict (dirRestrQ vars D) D
  | [], D, _ => by
      rw [show residualQ ([] : Term n) D = D from by rw [residualQ]]
      rw [show dirRestrQ ([] : Term n) D = (fun _ => none) from by rw [dirRestrQ]]
      rw [dnfRestrict_none_id]
  | l :: vs, D, hs => by
      -- l.var ∉ vs.map var, vs simple
      have hnd : l.var ∉ vs.map (·.var) := by
        unfold SimpleTerm at hs
        simp only [List.map_cons, List.nodup_cons] at hs
        exact hs.1
      have hsvs : SimpleTerm vs := by
        unfold SimpleTerm at hs ⊢
        simp only [List.map_cons, List.nodup_cons] at hs
        exact hs.2
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · rw [show residualQ (l :: vs) D = residualQ vs (assignVar l.var true D) from by
              rw [residualQ]; simp only [if_pos h]]
        rw [show dirRestrQ (l :: vs) D
              = overlay (single l.var true) (dirRestrQ vs (assignVar l.var true D)) from by
              rw [dirRestrQ]; simp only [if_pos h]]
        rw [residualQ_eq_dnfRestrict vs (assignVar l.var true D) hsvs]
        -- the disjointness side-condition for the single-then-rest composition
        have hP : (dirRestrQ vs (assignVar l.var true D)) l.var = none :=
          dirRestrQ_apply_eq_none vs (assignVar l.var true D) l.var hnd
        -- compose: rewrite only the OUTER (second) D-restriction layer
        conv_lhs => arg 2; rw [assignVar_eq_single l.var true D]
        exact dnfRestrict_single_comp l.var true
          (dirRestrQ vs (assignVar l.var true D)) D hP
      · rw [show residualQ (l :: vs) D = residualQ vs (assignVar l.var false D) from by
              rw [residualQ]; simp only [if_neg h]]
        rw [show dirRestrQ (l :: vs) D
              = overlay (single l.var false) (dirRestrQ vs (assignVar l.var false D)) from by
              rw [dirRestrQ]; simp only [if_neg h]]
        rw [residualQ_eq_dnfRestrict vs (assignVar l.var false D) hsvs]
        have hP : (dirRestrQ vs (assignVar l.var false D)) l.var = none :=
          dirRestrQ_apply_eq_none vs (assignVar l.var false D) l.var hnd
        conv_lhs => arg 2; rw [assignVar_eq_single l.var false D]
        exact dnfRestrict_single_comp l.var false
          (dirRestrQ vs (assignVar l.var false D)) D hP
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-- **The block residual is `dnfRestrict` by its deep-direction restriction (PROVED).**
For a simple DNF `D` (so its first term is a proper conjunction), `residualBlock D =
dnfRestrict (dirRestrBlock D) D`.  Directly from the helper and `assignVar_eq_single`
+ `dnfRestrict_single_comp`. -/
theorem residualBlock_eq_dnfRestrict {n : Nat} :
    ∀ (D : DNF n), SimpleDNF D → residualBlock D = dnfRestrict (dirRestrBlock D) D
  | [], _ => by
      rw [show residualBlock ([] : DNF n) = [] from by rw [residualBlock]]
      rw [show dirRestrBlock ([] : DNF n) = (fun _ => none) from by rw [dirRestrBlock]]
      rw [dnfRestrict_none_id]
  | [] :: D, _ => by
      rw [show residualBlock (([] : Term n) :: D) = ([] : Term n) :: D from by rw [residualBlock]]
      rw [show dirRestrBlock (([] : Term n) :: D) = (fun _ => none) from by rw [dirRestrBlock]]
      rw [dnfRestrict_none_id]
  | (l :: t) :: D, hD => by
      have hst : SimpleTerm (l :: t) := hD (l :: t) (List.mem_cons_self _ _)
      have hnd : l.var ∉ t.map (·.var) := by
        unfold SimpleTerm at hst
        simp only [List.map_cons, List.nodup_cons] at hst
        exact hst.1
      have hstt : SimpleTerm t := by
        unfold SimpleTerm at hst ⊢
        simp only [List.map_cons, List.nodup_cons] at hst
        exact hst.2
      by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
      · rw [show residualBlock ((l :: t) :: D)
              = residualQ t (assignVar l.var true ((l :: t) :: D)) from by
              rw [residualBlock]; simp only [if_pos h]]
        rw [show dirRestrBlock ((l :: t) :: D)
              = overlay (single l.var true)
                  (dirRestrQ t (assignVar l.var true ((l :: t) :: D))) from by
              rw [dirRestrBlock]; simp only [if_pos h]]
        rw [residualQ_eq_dnfRestrict t (assignVar l.var true ((l :: t) :: D)) hstt]
        have hP : (dirRestrQ t (assignVar l.var true ((l :: t) :: D))) l.var = none :=
          dirRestrQ_apply_eq_none t (assignVar l.var true ((l :: t) :: D)) l.var hnd
        conv_lhs => arg 2; rw [assignVar_eq_single l.var true ((l :: t) :: D)]
        exact dnfRestrict_single_comp l.var true
          (dirRestrQ t (assignVar l.var true ((l :: t) :: D))) ((l :: t) :: D) hP
      · rw [show residualBlock ((l :: t) :: D)
              = residualQ t (assignVar l.var false ((l :: t) :: D)) from by
              rw [residualBlock]; simp only [if_neg h]]
        rw [show dirRestrBlock ((l :: t) :: D)
              = overlay (single l.var false)
                  (dirRestrQ t (assignVar l.var false ((l :: t) :: D))) from by
              rw [dirRestrBlock]; simp only [if_neg h]]
        rw [residualQ_eq_dnfRestrict t (assignVar l.var false ((l :: t) :: D)) hstt]
        have hP : (dirRestrQ t (assignVar l.var false ((l :: t) :: D))) l.var = none :=
          dirRestrQ_apply_eq_none t (assignVar l.var false ((l :: t) :: D)) l.var hnd
        conv_lhs => arg 2; rw [assignVar_eq_single l.var false ((l :: t) :: D)]
        exact dnfRestrict_single_comp l.var false
          (dirRestrQ t (assignVar l.var false ((l :: t) :: D))) ((l :: t) :: D) hP

/-! ## 4. Coverage: the deep-direction restriction FIXES every block variable

The deep walk through a term block queries — hence fixes the deep direction of —
EVERY variable of the block.  So `dirRestrQ vars D` fixes every variable of `vars`,
and `dirRestrBlock ((l :: t) :: D)` fixes every variable of `l :: t`. -/

/-- `overlay ρ τ x` is some whenever `ρ x` is some. -/
theorem overlay_isSome_of_left {n : Nat} (ρ τ : Restriction n) (x : Fin n)
    (h : (ρ x).isSome) : (overlay ρ τ x).isSome := by
  unfold overlay; cases τ x with
  | some b => simp
  | none => exact h

/-- `overlay ρ τ x` is some whenever `τ x` is some. -/
theorem overlay_isSome_of_right {n : Nat} (ρ τ : Restriction n) (x : Fin n)
    (h : (τ x).isSome) : (overlay ρ τ x).isSome := by
  unfold overlay; cases hτ : τ x with
  | some b => simp
  | none => rw [hτ] at h; simp at h

/-- **`dirRestrQ` fixes every variable of `vars`.** -/
theorem dirRestrQ_apply_isSome {n : Nat} :
    ∀ (vars : Term n) (D : DNF n) (x : Fin n),
      x ∈ vars.map (·.var) → (dirRestrQ vars D x).isSome
  | [], _, x, hx => by simp at hx
  | l :: vs, D, x, hx => by
      simp only [List.map_cons, List.mem_cons] at hx
      rw [dirRestrQ]
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · simp only [if_pos h]
        rcases hx with hxl | hxvs
        · subst hxl
          exact overlay_isSome_of_left _ _ _ (by unfold single; simp)
        · exact overlay_isSome_of_right _ _ _
            (dirRestrQ_apply_isSome vs (assignVar l.var true D) x hxvs)
      · simp only [if_neg h]
        rcases hx with hxl | hxvs
        · subst hxl
          exact overlay_isSome_of_left _ _ _ (by unfold single; simp)
        · exact overlay_isSome_of_right _ _ _
            (dirRestrQ_apply_isSome vs (assignVar l.var false D) x hxvs)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-- **`dirRestrBlock` fixes every variable of the first term `l :: t`.** -/
theorem dirRestrBlock_cons_cons_isSome {n : Nat} (l : Literal n) (t : Term n)
    (D : DNF n) (x : Fin n) (hx : x ∈ (l :: t).map (·.var)) :
    (dirRestrBlock ((l :: t) :: D) x).isSome := by
  rw [dirRestrBlock]
  simp only [List.map_cons, List.mem_cons] at hx
  by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
      ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
  · simp only [if_pos h]
    rcases hx with hxl | hxt
    · subst hxl
      exact overlay_isSome_of_left _ _ _ (by unfold single; simp)
    · exact overlay_isSome_of_right _ _ _
        (dirRestrQ_apply_isSome t (assignVar l.var true ((l :: t) :: D)) x hxt)
  · simp only [if_neg h]
    rcases hx with hxl | hxt
    · subst hxl
      exact overlay_isSome_of_left _ _ _ (by unfold single; simp)
    · exact overlay_isSome_of_right _ _ _
        (dirRestrQ_apply_isSome t (assignVar l.var false ((l :: t) :: D)) x hxt)

/-! ## 5. A fully-fixed term restricts to `none` or `some []`

If a restriction `σ` fixes EVERY variable of a term `t`, then `termRestrict σ t` is
either `none` (some literal disagrees ⇒ FALSIFIED) or `some []` (all literals agree ⇒
SATISFIED).  No literal can survive, since survival requires a free variable. -/

/-- **A fully-fixed term is falsified or collapses to `[]`.** -/
theorem termRestrict_fully_fixed {n : Nat} (σ : Restriction n) :
    ∀ (t : Term n), (∀ l ∈ t, (σ l.var).isSome) →
      termRestrict σ t = none ∨ termRestrict σ t = some []
  | [], _ => Or.inr rfl
  | l :: t, hfix => by
      have hl : (σ l.var).isSome := hfix l (List.mem_cons_self l t)
      have ht : ∀ m ∈ t, (σ m.var).isSome := fun m hm => hfix m (List.mem_cons_of_mem l hm)
      cases hσ : σ l.var with
      | none => rw [hσ] at hl; simp at hl
      | some b =>
          rw [termRestrict, hσ]
          dsimp only
          by_cases hbs : b = l.sign
          · rw [if_pos hbs]
            exact termRestrict_fully_fixed σ t ht
          · rw [if_neg hbs]; exact Or.inl rfl

/-! ## 6. FACT (b): the deep walk falsifies every processed-and-continued term

We assemble the pieces.  The first term `l :: t` is fully fixed by `dirRestrBlock`
(coverage), so its restriction is `none` (falsified) or `some []` (satisfied,
collapses).  If satisfied, `residualBlock = dnfRestrict (dirRestrBlock) …` is headed
by `[]`, so `deepPathV (residualBlock) = []` and the deep walk STOPS.  Hence if the
walk CONTINUES (`deepPathV (residualBlock) ≠ []`), the term was FALSIFIED. -/

/-- If `termRestrict σ (l :: t) = some []` then `dnfRestrict σ ((l :: t) :: D)` is
headed by the constant-true `[]`, so its deep walk is empty. -/
theorem deepPathV_dnfRestrict_eq_nil_of_head_sat {n : Nat} (σ : Restriction n)
    (l : Literal n) (t : Term n) (D : DNF n)
    (hsat : termRestrict σ (l :: t) = some []) :
    deepPathV (dnfRestrict σ ((l :: t) :: D)) = [] := by
  have hhead : dnfRestrict σ ((l :: t) :: D) = [] :: dnfRestrict σ D := by
    unfold dnfRestrict
    rw [List.filterMap_cons, hsat]
  rw [hhead, deepPathV]

/-- **FACT (b) — block dichotomy (PROVED).**  For a SIMPLE DNF whose first term is
`l :: t`: EITHER the first term is FALSIFIED by its block's deep directions
(`termRestrict (dirRestrBlock …) (l :: t) = none`), OR the deep walk on the residual
after the block is EMPTY (`deepPathV (residualBlock …) = []`, i.e. the walk stopped).
This is the structural dichotomy underlying the π-advance falsification linchpin: the
canonical tree continues past a term ONLY when its own deep directions killed it. -/
theorem factB_block_dichotomy {n : Nat} (l : Literal n) (t : Term n) (D : DNF n)
    (hD : SimpleDNF ((l :: t) :: D)) :
    termRestrict (dirRestrBlock ((l :: t) :: D)) (l :: t) = none
      ∨ deepPathV (residualBlock ((l :: t) :: D)) = [] := by
  -- the first term is fully fixed by dirRestrBlock
  have hfix : ∀ m ∈ (l :: t), (dirRestrBlock ((l :: t) :: D) m.var).isSome := by
    intro m hm
    exact dirRestrBlock_cons_cons_isSome l t D m.var (List.mem_map_of_mem (·.var) hm)
  rcases termRestrict_fully_fixed (dirRestrBlock ((l :: t) :: D)) (l :: t) hfix with
    hnone | hsat
  · exact Or.inl hnone
  · -- satisfied: residual headed by [], walk stops
    right
    rw [residualBlock_eq_dnfRestrict ((l :: t) :: D) hD]
    exact deepPathV_dnfRestrict_eq_nil_of_head_sat _ l t D hsat

/-- **FACT (b) — processed-and-continued term is falsified (PROVED).**  The
contrapositive packaging: for a SIMPLE DNF whose first term is `l :: t`, if the deep
walk CONTINUES past the first term block (`deepPathV (residualBlock …) ≠ []`), then the
first term is FALSIFIED by its block's deep directions:
`termRestrict (dirRestrBlock …) (l :: t) = none`.  This is exactly the linchpin
isolated as point (b) of `SwitchingDecodeRef.obstruction_note`. -/
theorem factB_processed_falsified {n : Nat} (l : Literal n) (t : Term n) (D : DNF n)
    (hD : SimpleDNF ((l :: t) :: D))
    (hcont : deepPathV (residualBlock ((l :: t) :: D)) ≠ []) :
    termRestrict (dirRestrBlock ((l :: t) :: D)) (l :: t) = none := by
  rcases factB_block_dichotomy l t D hD with h | h
  · exact h
  · exact absurd h hcont

/-! ## 7. The iterated / per-step form along the deep walk of `D|ρ`

We lift FACT (b) to the j-th term ENTERED by the deep walk of `D|ρ`, expressed via
the residual `residualIter (D|ρ) j` (whose HEAD term is the j-th deep term, by the
proved `deepResidual_head` drop laws).  `SimpleDNF` is preserved through
`residualBlock`/`residualIter` (each is a `dnfRestrict`/`assignVar` of the previous),
supplying the hypothesis FACT (b) needs. -/

/-- `residualBlock` preserves `SimpleDNF` (it is a `dnfRestrict` of the input under
its deep-direction restriction). -/
theorem simpleDNF_residualBlock {n : Nat} {D : DNF n} (hD : SimpleDNF D) :
    SimpleDNF (residualBlock D) := by
  cases D with
  | nil => rw [show residualBlock ([] : DNF n) = [] from by rw [residualBlock]]; intro t ht; simp at ht
  | cons term Ds =>
      cases term with
      | nil =>
          rw [show residualBlock (([] : Term n) :: Ds) = ([] : Term n) :: Ds from by rw [residualBlock]]
          exact hD
      | cons l t =>
          rw [residualBlock_eq_dnfRestrict ((l :: t) :: Ds) hD]
          exact simpleDNF_dnfRestrict hD _

/-- `residualIter` preserves `SimpleDNF`. -/
theorem simpleDNF_residualIter {n : Nat} :
    ∀ (i : Nat) {D : DNF n}, SimpleDNF D → SimpleDNF (residualIter D i)
  | 0, D, hD => by rw [residualIter]; exact hD
  | (i + 1), D, hD => by
      rw [residualIter]
      exact simpleDNF_residualIter i (simpleDNF_residualBlock hD)

/-- `residualIter D (i+1) = residualBlock (residualIter D i)` (the deep walk after
`i+1` blocks is one more block applied to the residual after `i` blocks). -/
theorem residualIter_succ {n : Nat} :
    ∀ (i : Nat) (D : DNF n), residualIter D (i + 1) = residualBlock (residualIter D i)
  | 0, D => by rw [residualIter, residualIter, residualIter]
  | (i + 1), D => by
      rw [show residualIter D (i + 1 + 1) = residualIter (residualBlock D) (i + 1) from by
            rw [residualIter]]
      rw [residualIter_succ i (residualBlock D)]
      rw [show residualIter D (i + 1) = residualIter (residualBlock D) i from by rw [residualIter]]

/-- **FACT (b) — iterated/per-step form (PROVED).**  Let `E := D|ρ` be a simple DNF and
suppose the j-th term entered by the deep walk is a genuine (non-empty) term, i.e.
`residualIter E j = (l :: t) :: rest`.  If the deep walk CONTINUES past block `j`
(`deepPathV (residualIter E (j + 1)) ≠ []`), then that j-th deep term `l :: t` is
FALSIFIED by its own block's deep directions:
`termRestrict (dirRestrBlock (residualIter E j)) (l :: t) = none`.

Combined with `deepResidual_head` (the j-th deep block of `D|ρ` is the HEAD block of
`residualIter (D|ρ) j`), this is the precise statement that each term the deep walk
processes and continues past is falsified by the deep-path directions on its block —
FACT (b) as stated in the task. -/
theorem factB_iter {n : Nat} {E : DNF n} (hE : SimpleDNF E) (j : Nat)
    (l : Literal n) (t : Term n) (rest : DNF n)
    (hres : residualIter E j = (l :: t) :: rest)
    (hcont : deepPathV (residualIter E (j + 1)) ≠ []) :
    termRestrict (dirRestrBlock (residualIter E j)) (l :: t) = none := by
  have hsimp : SimpleDNF (residualIter E j) := simpleDNF_residualIter j hE
  rw [hres] at hsimp ⊢
  -- residualIter E (j+1) = residualBlock (residualIter E j) = residualBlock ((l::t)::rest)
  have hcont' : deepPathV (residualBlock ((l :: t) :: rest)) ≠ [] := by
    rw [← hres, ← residualIter_succ]; exact hcont
  exact factB_processed_falsified l t rest hsimp hcont'

/-! ## 8. HONESTY NOTE — what FACT (b) closes, and exactly where the assembly stops

PROVED OUTRIGHT in this file (all green, axioms ⊆ `[propext, Quot.sound]`, no
`sorryAx`):

* `residualQ_eq_dnfRestrict` / `residualBlock_eq_dnfRestrict` — the deep-walk residual
  IS `dnfRestrict` by the block's deep-direction restriction (bridging the
  `assignVar`-based deep walk to the restriction algebra, via the proved
  `assignVar_eq_single` + `dnfRestrict_single_comp` + `SimpleTerm` distinctness).
* `dirRestrQ_apply_isSome` / `dirRestrBlock_cons_cons_isSome` — the deep walk FIXES
  every variable of a term block.
* `termRestrict_fully_fixed` — a fully-fixed term is `none` (falsified) or `some []`
  (satisfied/collapses).
* **`factB_block_dichotomy`** — for a simple DNF headed by `l :: t`: EITHER the term is
  FALSIFIED by its block's deep directions, OR the deep walk on the residual is EMPTY
  (the walk stopped, because a satisfied head term gives `termCanonicalDT ([] :: _) =
  leaf true`, depth 0).
* **`factB_processed_falsified`** — FACT (b): if the walk CONTINUES past the first term
  block, the first term is FALSIFIED by its block's deep directions.
* **`factB_iter`** — the iterated/per-step form: the j-th term ENTERED by the deep walk
  of `D|ρ` (the head term of `residualIter (D|ρ) j`, identified by the proved
  `SwitchingClose.deepResidual_head`) is FALSIFIED by its own block's deep directions
  whenever the walk continues past block `j`.

This is exactly point (b) of `SwitchingDecodeRef.obstruction_note` — the "π-advance
FALSIFICATION linchpin" — proved as a standalone structural fact.

NOT closed by FACT (b) (the assembly to `RCodeBlockStepVar` / `SwitchingLemmaTermSimple`
genuinely does NOT follow, and we do NOT fake it):

The general decode step `RCodeBlockStepVar` (= `SwitchingClose.ResidualHeadDecode`) needs
a **ρ-INDEPENDENT** recovery of the i-th deep variable from `σ_loc = encodeLoc₁ D s ρ`,
the per-term code, and `prev = (deepPathV (D|ρ)).take i`.  FACT (b) falsifies the earlier
deep terms by the **deep directions** `prefixRestr prev` (ρ-independent, available to the
decoder).  But the residual whose HEAD is the i-th deep term is
`residualIter (D|ρ) i = dnfRestrict (overlay ρ (prefixRestr prev)) D`, which needs `ρ`.
The only ρ-independent restriction available is `σ_loc = overlay ρ (satRestrLoc …)`, and
`satRestrLoc` ADDITIONALLY fixes the NOT-YET-DECODED touched variables (deep indices
`≥ i`) to their SATISFYING values — which COLLAPSE the i-th deep term to the
constant-true `[]` (proved: `SwitchingDeepAux.termRestrict_encodeLoc₁_satisfied`),
ERASING exactly the variable to be recovered.  Concretely the two falsifications point
OPPOSITE ways: FACT (b) needs the FALSIFYING (deep) directions on a block, whereas `σ_loc`
carries the SATISFYING directions on that same block.  A term falsified by its deep
directions is therefore NOT falsified under `σ_loc`; FACT (b) does not transport across
`σ_loc`.  Subtracting `σ_loc`'s future-touched satisfying fixings to rebuild
`residualIter (D|ρ) i` ρ-independently is the convention-independent Razborov content
that stays isolated (unchanged) as `ResidualHeadDecode` / `RCodeRecoverable` /
`DeepBlockRecoverableW`.

In short: FACT (b) supplies ONE of the two ingredients the obstruction note lists
[its point (b)], proved; the OTHER ingredient — the ρ-elimination — is the genuine wall,
and it is the reason the assembly does NOT reach `RCodeBlockStepVar`.  This file does NOT
fake that step: no `sorry`, no `admit`, no new `axiom`, no `native_decide`. -/

/-- **FACT (b) for an interior block (PROVED, corollary).**  If the deep walk of a simple
DNF `E` enters at least `j + 2` term blocks — equivalently the residual after `j + 1`
blocks still has a non-empty deep walk — then the j-th deep term `l :: t` is FALSIFIED by
its own block's deep directions.  (Every block the walk enters except possibly the LAST is
"processed and continued past", so its term is falsified; the last term may be the one the
walk stops on, satisfied.) -/
theorem factB_interior {n : Nat} {E : DNF n} (hE : SimpleDNF E) (j : Nat)
    (l : Literal n) (t : Term n) (rest : DNF n)
    (hres : residualIter E j = (l :: t) :: rest)
    (hcont : deepPathV (residualIter E (j + 1)) ≠ []) :
    termRestrict (dirRestrBlock (residualIter E j)) (l :: t) = none :=
  factB_iter hE j l t rest hres hcont

end SwitchingFactB
end PvNP
