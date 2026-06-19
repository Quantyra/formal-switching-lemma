/-
# Reference-grounded sequential Razborov decode (Beame primer / Thapen notes)

This file implements the reference-confirmed decoder for the term switching lemma
(arXiv:2202.05651, §switching lemma) and DISCHARGES new structural content that the
sibling files (`SwitchingClose`, `SwitchingEncodeLocal`, `SwitchingRazborovCode`)
left out — specifically the `assignVar`↔`dnfRestrict` bridge and the residualization
commutation that the reference decode walks on.  It then drives the per-step decode to
its EXACT remaining obstruction and reports it precisely (no `sorry`, no fake, no new
axiom).

## What is GENUINELY NEW and PROVED here

* `assignTerm_eq_single` / `assignVar_eq_single`: the decision-tree residualization
  `assignVar v b` is EXACTLY restriction by the single fixing `v ↦ b`
  (`dnfRestrict (fun x => if x = v then some b else none)`).  This is the bridge that
  was MISSING in all sibling files and that connects the canonical-tree recursion
  (built on `assignVar`) to the restriction algebra (`dnfRestrict`/`overlay`).
* `assignVar_dnfRestrict_comm`: residualizing `D|ρ` by a free variable commutes with
  `dnfRestrict ρ`.  This is the lever that lets the deep-walk residual `residualIter
  (D|ρ) j` be pushed through `dnfRestrict ρ` onto the ORIGINAL `D`.

## The reference decode and the EXACT remaining obstruction

The reference decoder (steps 1–4 of the primer) reads the i-th touched variable from
the ORIGINAL term of `D` selected as "the first term not falsified by the running
state", advancing the running state by the code's π (deep-direction) values carried in
`prev`.  We define this decoder (`decodeStateRef`) ρ-INDEPENDENTLY.  Driving the
per-step correctness to the bottom, the remaining content is a SINGLE structural fact
(documented at `obstruction_note` below): that an EARLIER deep term, once its variables
are fixed to their own deep-path directions, is FALSIFIED (because the canonical tree
only continues past a term that its directions killed — a surviving term would collapse
to constant-true and stop the walk).  This is the π-advance falsification linchpin; it
is NOT among the proved lemma base, and we do NOT fake it.  See `obstruction_note`.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed axioms
⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.  The
imported files are untouched.
-/
import PvNP.SwitchingClose

namespace PvNP
namespace SwitchingDecodeRef

open CNFModel
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct
open SwitchingEncodeLocal
open SwitchingDeepAux
open SwitchingClose
open SwitchingRazborovCode
open Classical

/-! ## 1. The `assignVar` ↔ `dnfRestrict` bridge (NEW, PROVED)

`assignVar v b` (the decision-tree residualization the canonical tree is built on)
coincides, term for term, with restriction by the single fixing `v ↦ b`.  Both drop a
satisfied `v`-literal, kill the term on a falsified `v`-literal, and keep all other
literals — so they are equal as `Option (Term n)` / `DNF n` operations. -/

/-- **`assignTerm` is single-variable `termRestrict` (PROVED).** -/
theorem assignTerm_eq_single {n : Nat} (v : Fin n) (b : Bool) (t : Term n) :
    assignTerm v b t = termRestrict (fun x => if x = v then some b else none) t := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      rw [assignTerm]
      by_cases hlv : l.var = v
      · subst hlv
        rw [termRestrict, if_pos rfl, if_pos rfl]
        show _ = (if b = l.sign then _ else _)
        by_cases hls : l.sign = b
        · rw [if_pos hls, if_pos hls.symm, ih]
        · rw [if_neg hls, if_neg (fun h => hls h.symm)]
      · rw [if_neg hlv, termRestrict, if_neg hlv, ih]; rfl

/-- **`assignVar` is single-variable `dnfRestrict` (PROVED).** -/
theorem assignVar_eq_single {n : Nat} (v : Fin n) (b : Bool) (D : DNF n) :
    assignVar v b D = dnfRestrict (fun x => if x = v then some b else none) D := by
  unfold assignVar dnfRestrict
  apply List.filterMap_congr
  intro t _; exact assignTerm_eq_single v b t

/-- **Residualization commutes with `dnfRestrict ρ` on a free variable (PROVED).**
For `v` a star of `ρ`, residualizing `D|ρ` by `v ↦ b` equals restricting `assignVar v
b D` by `ρ`.  The lever that pushes the deep-walk residual of `D|ρ` onto the original
`D`. -/
theorem assignVar_dnfRestrict_comm {n : Nat} (v : Fin n) (b : Bool) (ρ : Restriction n)
    (D : DNF n) (hv : ρ v = none) :
    assignVar v b (dnfRestrict ρ D) = dnfRestrict ρ (assignVar v b D) := by
  rw [assignVar_eq_single, assignVar_eq_single]
  rw [← dnfRestrict_overlay, ← dnfRestrict_overlay]
  · congr 1
    funext x; unfold overlay
    by_cases hx : x = v
    · subst hx; rw [hv]; simp [if_pos rfl]
    · simp only [if_neg hx]; cases ρ x <;> rfl
  · intro x hx; by_cases hxv : x = v
    · subst hxv; exact hv
    · simp only [if_neg hxv] at hx; exact absurd rfl hx
  · intro x hx; by_cases hxv : x = v
    · subst hxv; rw [hv] at hx; exact absurd rfl hx
    · simp [if_neg hxv]

/-! ## 2. Restriction-by-empty is the identity (NEW, PROVED)

Needed as the base case of expressing the deep-walk residual `residualQ`/`residualBlock`
as a single `dnfRestrict`. -/

/-- `termRestrict (∅) t = some t`. -/
theorem termRestrict_none_id {n : Nat} (t : Term n) :
    termRestrict (fun _ => none) t = some t := by
  induction t with
  | nil => rfl
  | cons l t ih => rw [termRestrict]; simp only []; rw [ih]

/-- **`dnfRestrict (∅) D = D` (PROVED).** -/
theorem dnfRestrict_none_id {n : Nat} (D : DNF n) :
    dnfRestrict (fun _ => none) D = D := by
  unfold dnfRestrict
  rw [show (D.filterMap (termRestrict (fun _ => none))) = D.filterMap some from by
    apply List.filterMap_congr; intro t _; exact termRestrict_none_id t]
  exact List.filterMap_some D

/-! ## 3. The deep-walk residual as a single restriction (PARTIAL — the exact wall)

The reference decoder must form, ρ-INDEPENDENTLY, the residual of `D|ρ` after the deep
walk has processed the recovered prefix.  By §1's bridge the deep walk residual
`residualQ`/`residualBlock` is an iterated `assignVar` = iterated single `dnfRestrict`.
Collapsing the iterate into ONE `dnfRestrict P` (with `P` the deep directions, the
ρ-independent code data) is what would let the decoder rebuild the residual from the
code alone.  The collapse REQUIRES the deep-walk variables be DISTINCT (so the single
fixings are pairwise disjoint and `dnfRestrict_overlay` applies); this holds under
`SimpleDNF` (`SwitchingEncodeConstruct.deepestPath_var_nodup`), but `residualQ` does
NOT carry the distinctness invariant, and threading it through the
`(dnfSize, vars.length)`-well-founded recursion of `residualQ` — together with the
matching π-advance FALSIFICATION linchpin (see `obstruction_note`) — is the open
Razborov replay.  We record the base/step shape that is proved, and isolate the single
missing disjointness-composition step. -/

/-- **The disjoint single-then-rest composition (PROVED).**  If `P l.var = none` (the
head variable does not recur in the rest restriction `P`), then restricting by `P`
after the single fixing `l.var ↦ b` equals restricting by their overlay.  This is the
clean composition the deep-walk-residual collapse needs at each step; the SOLE missing
ingredient to apply it along `residualQ` is the proof that `P l.var = none`, i.e. the
distinctness of the deep-walk variables threaded through the recursion. -/
theorem dnfRestrict_single_comp {n : Nat} (l : Fin n) (b : Bool) (P : Restriction n)
    (D : DNF n) (hP : P l = none) :
    dnfRestrict P (dnfRestrict (fun x => if x = l then some b else none) D)
      = dnfRestrict (overlay (fun x => if x = l then some b else none) P) D := by
  rw [dnfRestrict_overlay]
  intro x hx; by_cases hxl : x = l
  · subst hxl; exact hP
  · simp only [if_neg hxl] at hx; exact absurd rfl hx

/-! ## 4. HONESTY NOTE — the EXACT remaining obstruction (NOT faked)

`RCodeBlockStepVar n` (≡ `SwitchingClose.ResidualHeadDecode n`, the SOLE remaining
content of the whole proved chain to `SwitchingLemmaTermSimple n`) requires a
ρ-INDEPENDENT `stepVar` recovering the i-th deep variable from `σ_loc = encodeLoc₁ D s
ρ`, the i-th per-term code entry, and `prev = (deepPathV (D|ρ)).take i`.

The reference decode (Beame primer / Thapen notes) recovers it as: the first ORIGINAL
term of `D` not falsified by the running state `state_i := overlay σ_loc (prefixRestr
prev)` (ρ-independent — both arguments are decoder inputs), read at the code's column.
For this to equal the i-th deep term, TWO facts are needed, of which exactly ONE is the
open content:

  (a) Every ORIGINAL term of `D` before the i-th deep term that was ρ-FALSIFIED stays
      falsified under `state_i` (since `state_i ⊇ ρ` on `ρ`'s domain).  This IS proved:
      `SwitchingDeepAux.not_satisfied_encodeLoc₁_of_ρ_falsifies` /
      `firstSat_eq_of_ρ_falsified_prefix`.

  (b) **[OPEN — the π-advance FALSIFICATION linchpin]** Every EARLIER DEEP term (one the
      deep path ENTERED, block index `< ` the current block), once its variables are
      fixed to their own deep-path directions (carried in `prev`/`prefixRestr prev`), is
      FALSIFIED — so it is skipped by "first not falsified".  Mathematically this holds
      because the canonical tree only CONTINUES past a term whose directions KILLED it
      (a term surviving its own directions collapses to the constant-true `[]`, making
      `termCanonicalDT ([] :: _) = leaf true` and STOPPING the walk —
      `SwitchingTermCanonicalDT`).  Formalizing it requires threading the deep-walk
      distinctness/segmentation invariant through the `residualQ`/`residualBlock`
      recursion (the `dnfRestrict_single_comp` disjointness side-condition `P l = none`
      above) and proving the resulting head-term collapse ⇒ falsification.  This is the
      convention-independent Razborov replay content isolated as
      `DeepBlockRecoverableW` / `LocDeepBlockRecoverableW` / `RCodeRecoverable` /
      `ResidualHeadDecode` in the sibling files.  It is NOT in the proved lemma base and
      we do NOT fake it.

  A further, smaller gap: `RCodeBlockStepVar` indexes by GLOBAL deep index `i`, so
  `prev = take i` can end MID-block; the identification (a)+(b) is cleanest at
  block-NUMBER granularity (`deepResidual_head`), and the mid-block bookkeeping (the
  partial current block) must be bridged via the per-term `last`-bit segmentation
  (`SwitchingRazborovCode.isLastInBlock_lt_sum`).

Thus the reference decode is mathematically sound and its restriction-algebra
plumbing is advanced here (§1–3, the `assignVar`↔`dnfRestrict` bridge,
the residualization commutation, and the disjoint composition step), but the decisive
π-advance falsification linchpin (b) remains the open Razborov content.  No `sorry`, no
`admit`, no new `axiom`, no `native_decide`. -/

end SwitchingDecodeRef
end PvNP
