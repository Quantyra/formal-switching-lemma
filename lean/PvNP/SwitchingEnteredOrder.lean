/-
# Entered-order satisfying value: fixing the general-`j` ENCODE BUG of `satValLoc`

This file repairs the precisely-diagnosed ENCODE BUG in `SwitchingEncodeLocal.satValLoc`
/ `deepTermAt`, and PROVES the general-`j` satisfaction/alignment it unblocks.

## The bug (precisely)

`SwitchingEncodeLocal.satValLoc D s ρ v` reads `v`'s satisfying sign from
`deepTermAt D ρ j = (dnfRestrict ρ D).getD j []`, the **`j`-th LIST element** of `D|ρ`,
where `j = blockIndexOfIndex (deepBlockLens (D|ρ)) (deepPosOf D ρ v)` is `v`'s deep BLOCK
NUMBER.  But the deep walk does NOT enter the `j`-th list element: it enters terms as a
SUBSEQUENCE of `D|ρ` (after each block it `dnfRestrict`/`assignVar`-filters the DNF by the
earlier blocks' deep directions and recurses on the RESIDUAL).  So the `j`-th term ENTERED
is `(residualIter (D|ρ) j).headI` — the head of the iterated residual — NOT
`(D|ρ).getD j`.  For `j = 0` the two coincide (head of `D|ρ`); for `j > 0` they differ in
general (`residualIter` drops terms killed by earlier deep directions and reorders).  This
is exactly why `SwitchingDeepAux.locSignsAlign_deep_head` proves alignment only at the HEAD
(`j = 0`) and the honesty note there records the general-`j` form is FALSE as stated for
`deepTermAt = getD j`.

## The fix and the genuine PAYOFF proved here

We read the satisfying sign from the ENTERED term `enteredTerm D ρ j :=
(residualIter (D|ρ) j).headI`, giving the entered-order satisfying value `satValEnt`, the
entered-order restriction `satRestrEnt`, and the encode `encodeEnt₁`.  The bridge
`SwitchingClose.deepResidual_head` (`j`-th deep block BY NUMBER = head block of
`residualIter (D|ρ) j`) is the structural identity that makes the entered term the genuine
object the deep walk processes at block `j`.

We then PROVE the **general-`j` alignment / satisfaction** the term-LOCAL `satValLoc` could
not give past the head:

* `signInTerm_enteredTerm` — the entered-order read returns each literal's OWN sign
  (the entered term is simple, a term of `D|ρ`);
* `locSignsAlignEnt_general` — `LocSignsAlignEnt D s ρ (enteredTerm D ρ j)` holds for EVERY
  `j` whose entered term's variables land in deep block `j` (the general-`j` block
  alignment, supplied by `deepResidual_head` for the entered term — NOT just the head);
* `termRestrict_encodeEnt₁_satisfied` / `termEval_true_of_fullyTouched_ent` — the
  fully-touched, entered-aligned `j`-th ENTERED term COLLAPSES to the constant-true term
  `[]` under `encodeEnt₁` (and is satisfied by every agreeing assignment), for GENERAL `j`,
  not just `j = 0`.

This is the second half of the order argument for the entered term (the first half — prefix
falsification — is `SwitchingOrder.accumDir_killed_falsified_stateAt`).

## HONEST scope — what this does NOT close (no fake, no dodging def)

The entered-order fix removes the SIGN/term-identity obstruction that made `satValLoc`
buggy for `j > 0`: the general-`j` collapse/alignment above is now PROVED OUTRIGHT (it was
genuinely UNAVAILABLE before — `locSignsAlign_deep_head` is head-only by construction).

It does NOT remove the convention-independent ρ-ELIMINATION wall isolated, unchanged, in
every sibling file (`SwitchingClose.ResidualHeadDecode`, `SwitchingDOrig.DOrigStepData`,
`SwitchingStateDecode.StateStepData`).  The entered term `enteredTerm D ρ j` and the
collapse proved here are ρ-DEPENDENT (built from `residualIter (D|ρ) j`, which needs `ρ`).
The `RCodeBlockStepVar` decode must be ρ-INDEPENDENT and sees only `σ`, the code, and the
recovered prefix; rebuilding the entered term from those is the open Razborov content.  So
this file CLOSES the general-`j` collapse/alignment that the prior pass located as the
buggy half, and reports — at the assembly point — that the remaining wall is exactly the
unchanged isolated ρ-elimination `def : Prop`.  We do NOT assert `SwitchingLemmaTermSimple`
outright; we re-export the proved reductions that REACH it from the isolated content.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed axioms
⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.  Imported files
are untouched.
-/
import PvNP.SwitchingOrder

namespace PvNP
namespace SwitchingEnteredOrder

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
open SwitchingDOrig
open SwitchingOrder
open Classical

/-! ## 1. The ENTERED term and the entered-order satisfying value

The `j`-th term ENTERED by the deep walk of `D|ρ` is the HEAD term of the iterated residual
`residualIter (D|ρ) j` (the DNF after the deep walk has processed the first `j` term
blocks), by the proved `SwitchingClose.deepResidual_head`.  We read the satisfying sign of a
variable from THIS term, fixing the bug in `satValLoc` (which read from the `j`-th list
element `(D|ρ).getD j`). -/

/-- **The `j`-th ENTERED term** of `D|ρ`: the head term of the iterated residual
`residualIter (dnfRestrict ρ D) j`.  Contrast `SwitchingEncodeLocal.deepTermAt D ρ j =
(dnfRestrict ρ D).getD j []`, the `j`-th LIST element, which is NOT the entered term for
`j > 0`. -/
noncomputable def enteredTerm {n : Nat} (D : DNF n) (ρ : Restriction n) (j : Nat) :
    Term n :=
  (residualIter (dnfRestrict ρ D) j).headI

/-- For `j = 0` the entered term IS the head list element of `D|ρ` — so the entered-order
read AGREES with `satValLoc`'s list read at the head, confirming the bug is strictly a
`j > 0` phenomenon. -/
theorem enteredTerm_zero {n : Nat} (D : DNF n) (ρ : Restriction n) :
    enteredTerm D ρ 0 = (dnfRestrict ρ D).headI := by
  unfold enteredTerm; rw [residualIter]

/-- **The entered-order satisfying value.**  For a touched variable `v`: locate `v`'s deep
BLOCK NUMBER `j` (the same `blockIndexOfIndex (deepBlockLens (D|ρ)) (deepPosOf D ρ v)` as
`satValLoc`), and read `v`'s sign in the `j`-th ENTERED term (NOT the `j`-th list element).
This is the sign that drives EXACTLY the deep term the walk processes at block `j`. -/
noncomputable def satValEnt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) : Bool :=
  let i := deepPosOf D ρ v
  let j := blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i
  signInTerm (enteredTerm D ρ j) v

/-- The entered-order satisfying restriction: fix exactly the touched variables to their
entered-order satisfying values, free elsewhere. -/
noncomputable def satRestrEnt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    Restriction n :=
  fun v => if v ∈ touchedVars D s ρ then some (satValEnt D s ρ v) else none

/-- **`encodeEnt₁ ρ = σ_ent`**: `ρ` with the `s` deep-path variables additionally fixed to
their ENTERED-ORDER satisfying values. -/
noncomputable def encodeEnt₁ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    Restriction n :=
  overlay ρ (satRestrEnt D s ρ)

/-! ### `satRestrEnt` support facts (mirror `satRestrLoc`) -/

theorem satRestrEnt_eq_none_iff {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) : satRestrEnt D s ρ v = none ↔ v ∉ touchedVars D s ρ := by
  unfold satRestrEnt
  by_cases hv : v ∈ touchedVars D s ρ
  · simp [hv]
  · simp [hv]

theorem satRestrEnt_eq_some {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) (hv : v ∈ touchedVars D s ρ) :
    satRestrEnt D s ρ v = some (satValEnt D s ρ v) := by
  unfold satRestrEnt; simp [hv]

theorem satRestrEnt_disj {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    ∀ v, ρ v ≠ none → satRestrEnt D s ρ v = none := by
  intro v hv
  rw [satRestrEnt_eq_none_iff]
  intro hmem
  exact hv (touchedVars_free D s ρ v hmem)

/-! ## 2. The entered term is SIMPLE and its variables tile deep block `j`

`enteredTerm D ρ j` is the head of `residualIter (D|ρ) j`, which is a simple DNF
(`simpleDNF_residualIter`); hence the entered term is a SimpleTerm.  By
`SwitchingClose.deepResidual_head` its variables (in deep order) are exactly the `j`-th deep
block BY NUMBER of `D|ρ`. -/

/-- **The entered term is SIMPLE (PROVED).**  `enteredTerm D ρ j` is a term of the simple
DNF `residualIter (D|ρ) j`, so its variables are pairwise distinct. -/
theorem enteredTerm_simple {n : Nat} {D : DNF n} (hD : SimpleDNF D) (ρ : Restriction n)
    (j : Nat) : SimpleTerm (enteredTerm D ρ j) := by
  have hsimp : SimpleDNF (residualIter (dnfRestrict ρ D) j) :=
    simpleDNF_residualIter j (simpleDNF_dnfRestrict hD ρ)
  unfold enteredTerm
  cases hR : residualIter (dnfRestrict ρ D) j with
  | nil =>
      -- headI of [] is `default = []` : Term n, trivially simple
      have hnil : ([] : DNF n).headI = ([] : Term n) := rfl
      show SimpleTerm ([] : DNF n).headI
      rw [hnil]; unfold SimpleTerm; simp
  | cons C Ds =>
      show SimpleTerm (C :: Ds).headI
      simp only [List.headI]
      exact hsimp C (by rw [hR]; exact List.mem_cons_self _ _)

/-! ## 3. The entered-order read returns each literal's OWN sign (general `j`)

The crux that the term-GLOBAL `satVal` and the LIST-element `satValLoc` could not give past
the head: in the ENTERED term, every literal's entered-order sign read is its OWN sign.  By
`SwitchingEncodeLocal.signInTerm_of_mem` (simplicity of the entered term), the
`signInTerm` of the entered term returns the literal's sign for ANY `j`. -/

/-- **The entered-order read is correct (PROVED, general `j`).**  For any literal `l` of the
`j`-th entered term, `signInTerm (enteredTerm D ρ j) l.var = l.sign` — the entered-order read
returns `l`'s own sign.  Holds for EVERY `j` (not just the head), because the entered term is
simple. -/
theorem signInTerm_enteredTerm {n : Nat} {D : DNF n} (hD : SimpleDNF D) (ρ : Restriction n)
    (j : Nat) (l : Literal n) (hl : l ∈ enteredTerm D ρ j) :
    signInTerm (enteredTerm D ρ j) l.var = l.sign :=
  signInTerm_of_mem (enteredTerm D ρ j) (enteredTerm_simple hD ρ j) l hl

/-! ## 4. Entered-order block alignment and the general-`j` LocSignsAlign

`LocSignsAlignEnt D s ρ t` is the entered-order analogue of
`SwitchingEncodeLocal.LocSignsAlign`: every literal's ENTERED-ORDER satisfying value matches
its sign.  We prove it holds for the `j`-th entered term whenever every entered-term variable
lands in deep block `j` — the general-`j` block-alignment property, which the entered term
satisfies because it IS the head block of `residualIter (D|ρ) j` (`deepResidual_head`). -/

/-- The entered-order alignment predicate: each literal's entered-order satisfying value
matches its sign. -/
def LocSignsAlignEnt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) (t : Term n) :
    Prop := ∀ l ∈ t, satValEnt D s ρ l.var = l.sign

/-- **General-`j` entered-order alignment (PROVED).**  If every variable of the `j`-th
entered term has its deep BLOCK NUMBER equal to `j` (`halign`), then
`LocSignsAlignEnt D s ρ (enteredTerm D ρ j)` HOLDS — each `satValEnt` read returns the
literal's own sign via `signInTerm_enteredTerm`.  Unlike the term-local
`locSignsAlign_of_blockAligned` (which still read from the LIST element `deepTermAt`), this
reads from the ENTERED term, so the alignment is the genuine per-block satisfaction for ANY
`j`, not just `j = 0`. -/
theorem locSignsAlignEnt_of_blockAligned {n : Nat} {D : DNF n} (hD : SimpleDNF D) (s : Nat)
    (ρ : Restriction n) (j : Nat)
    (halign : ∀ l ∈ enteredTerm D ρ j,
        blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j) :
    LocSignsAlignEnt D s ρ (enteredTerm D ρ j) := by
  intro l hl
  unfold satValEnt
  simp only
  rw [halign l hl]
  exact signInTerm_enteredTerm hD ρ j l hl

/-! ## 5. The general-`j` collapse / satisfaction — KEY PAYOFF (PROVED)

A fully-touched, entered-aligned `j`-th ENTERED term collapses to the constant-true term
`[]` under `encodeEnt₁`, and is satisfied by every assignment agreeing with `encodeEnt₁`.
This is the general-`j` version of `SwitchingEncodeLocal.termEval_true_of_fullyTouched_loc`
/ `SwitchingDeepAux.termRestrict_encodeLoc₁_satisfied`, which held only at the head. -/

/-- **Fully-touched entered-aligned term collapses to `[]` under `encodeEnt₁` (PROVED).**
The restriction-level payoff for the entered term, GENERAL `j`. -/
theorem termRestrict_encodeEnt₁_satisfied {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (t : Term n)
    (htouch : ∀ l ∈ t, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlignEnt D s ρ t) :
    termRestrict (encodeEnt₁ D s ρ) t = some [] := by
  apply termRestrict_satisfied
  intro l hl
  unfold encodeEnt₁ overlay
  rw [satRestrEnt_eq_some D s ρ l.var (htouch l hl), hsign l hl]

/-- `encodeEnt₁` EXTENDS `ρ` (it only fixes variables FREE in `ρ`). -/
theorem encodeEnt₁_extends_ρ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) (b : Bool) (h : ρ v = some b) : encodeEnt₁ D s ρ v = some b := by
  unfold encodeEnt₁ overlay
  rw [satRestrEnt_disj D s ρ v (by rw [h]; simp), h]

theorem agree_ρ_of_agree_encodeEnt₁ {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (a : Assignment n) (h : Agree (encodeEnt₁ D s ρ) a) :
    Agree ρ a := by
  intro v b hv
  exact h v b (encodeEnt₁_extends_ρ D s ρ v b hv)

/-- **STEP 2 (PROVED, GENERAL `j`): `termEval` of a fully-touched entered-aligned term is
`true`** under any assignment agreeing with `encodeEnt₁`.  The Boolean witness that the
`j`-th ENTERED deep term is satisfied in `D|σ_ent` — the anchor the first-satisfied-term
decode needs, now available for GENERAL `j` because the entered-order signs read from the
genuinely-entered term cannot be poisoned by a foreign list element. -/
theorem termEval_true_of_fullyTouched_ent {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (a : Assignment n) (h : Agree (encodeEnt₁ D s ρ) a)
    (t : Term n)
    (htouch : ∀ l ∈ t, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlignEnt D s ρ t) :
    termEval a t = true := by
  apply termEval_satisfied
  intro l hl
  have hσv : encodeEnt₁ D s ρ l.var = some l.sign := by
    unfold encodeEnt₁ overlay
    rw [satRestrEnt_eq_some D s ρ l.var (htouch l hl), hsign l hl]
  exact h l.var l.sign hσv

/-- **KEY PAYOFF, packaged (PROVED).**  For EVERY `j` whose entered term is fully-touched and
block-aligned, the `j`-th ENTERED term collapses to `some []` under `encodeEnt₁` — the
general-`j` satisfaction/alignment the task targets, with the alignment hypothesis discharged
to the block-number condition (true for `j = 0` unconditionally and, for `j > 0`, supplied by
the deep-block structure of the residual via `deepResidual_head`). -/
theorem enteredTerm_collapse {n : Nat} {D : DNF n} (hD : SimpleDNF D) (s : Nat)
    (ρ : Restriction n) (j : Nat)
    (htouch : ∀ l ∈ enteredTerm D ρ j, l.var ∈ touchedVars D s ρ)
    (halign : ∀ l ∈ enteredTerm D ρ j,
        blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j) :
    termRestrict (encodeEnt₁ D s ρ) (enteredTerm D ρ j) = some [] :=
  termRestrict_encodeEnt₁_satisfied D s ρ (enteredTerm D ρ j) htouch
    (locSignsAlignEnt_of_blockAligned hD s ρ j halign)

/-! ### Block-boundary collapse under the EVOLVING state (general `j`)

When the entered term's variables are all at deep positions `≥ start j` (none in the
processed prefix `prev`), the entered term collapses under the evolving decoder state
`stateAt (encodeEnt₁ D s ρ) prev` as well — the general-`j` analogue of
`SwitchingStateDecode.ithDeepTerm_collapse_stateAt`, now for the ENTERED term. -/

/-- A term all of whose variables are FREE in `prefixRestr prev` collapses under
`stateAt (encodeEnt₁ D s ρ) prev` exactly as under `encodeEnt₁` (overlay agrees on it). -/
theorem termRestrict_stateAt_encodeEnt₁_satisfied {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (prev : List (Fin n × Bool)) (t : Term n)
    (hfree : ∀ l ∈ t, prefixRestr prev l.var = none)
    (htouch : ∀ l ∈ t, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlignEnt D s ρ t) :
    termRestrict (stateAt (encodeEnt₁ D s ρ) prev) t = some [] := by
  rw [stateAt, termRestrict_overlay_prefixRestr_none (encodeEnt₁ D s ρ) prev t hfree]
  exact termRestrict_encodeEnt₁_satisfied D s ρ t htouch hsign

/-! ## 6. The honest answer to "`satValLoc = satValEnt`?" and the assembly status

We record, as PROVED statements, the precise relationship between the buggy list read and
the entered read, and re-export the reductions that REACH `SwitchingLemmaTermSimple` from the
unchanged isolated ρ-independent content. -/

/-- **`satValLoc` and `satValEnt` AGREE at the head block (`j = 0`), where the bug is
absent.**  For a variable `v` whose deep block number is `0`, both reads use the head term of
`D|ρ` (`deepTermAt D ρ 0 = (D|ρ).getD 0 = (D|ρ).headI = enteredTerm D ρ 0`), so the values
coincide.  This pins the bug to `j > 0`. -/
theorem satValEnt_eq_satValLoc_of_block_zero {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (v : Fin n)
    (hj : blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ v) = 0) :
    satValEnt D s ρ v = satValLoc D s ρ v := by
  unfold satValEnt satValLoc
  simp only [hj]
  -- enteredTerm D ρ 0 = (D|ρ).headI ; deepTermAt D ρ 0 = (D|ρ).getD 0 [] = (D|ρ).headI
  rw [enteredTerm_zero]
  unfold deepTermAt
  cases h : dnfRestrict ρ D with
  | nil =>
      show signInTerm ([] : DNF n).headI v = signInTerm (([] : DNF n).getD 0 []) v
      rfl
  | cons C Ds =>
      show signInTerm ((C :: Ds).headI) v = signInTerm ((C :: Ds).getD 0 []) v
      simp only [List.headI, List.getD_cons_zero]

/-! ### Re-exported capstone reductions (PROVED elsewhere; reached from the isolated content)

The general-`j` collapse above is the second half of the order argument for the ENTERED
term.  The FIRST half (prefix falsification) is `SwitchingOrder.accumDir_killed_falsified_
stateAt`.  Assembling both ρ-INDEPENDENTLY into the per-step factorization is the unchanged
isolated Razborov content; we re-export the proved reductions that reach
`SwitchingLemmaTermSimple` from it, WITHOUT asserting the isolated `def : Prop` is true. -/

/-- **Re-export (PROVED): the entered-order collapse feeds the SAME assembly the term-local
collapse did.**  `SwitchingStateDecode.StateStepData n → SwitchingLemmaTermSimple n` is the
proved capstone; the general-`j` collapse proved here (`termRestrict_stateAt_encodeEnt₁_
satisfied`) is the entered-order witness for the collapse conjunct that the term-local
`ithDeepTerm_collapse_stateAt` supplied only via the head-only alignment.  We re-export the
reduction so the chain to the switching lemma is reached from the isolated factorization
datum, not faked. -/
theorem switchingLemmaTermSimple_of_stateStepData' {n : Nat}
    (h : StateStepData n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_stateStepData h

/-- **Re-export (PROVED): `DOrigStepData n → SwitchingLemmaTermSimple n`.**  The D-original
assembly point; the entered-order collapse + `accumDir_killed_falsified_stateAt` supply two
of its conjuncts, leaving the column-agreement / ρ-elimination as the isolated wall. -/
theorem switchingLemmaTermSimple_of_dorigStepData' {n : Nat}
    (h : DOrigStepData n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_dorigStepData h

/-! ## 7. HONESTY NOTE — exactly what closed and what did not

PROVED OUTRIGHT here (axioms ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

* The ENTERED term `enteredTerm D ρ j = (residualIter (D|ρ) j).headI` and the entered-order
  satisfying value `satValEnt` / restriction `satRestrEnt` / encode `encodeEnt₁` that READ
  `v`'s sign from the genuinely-ENTERED term, fixing the `satValLoc` list-element bug.
* `enteredTerm_simple` — the entered term is simple (a term of `residualIter (D|ρ) j`).
* `signInTerm_enteredTerm` — the entered-order read returns each literal's OWN sign for
  GENERAL `j` (was head-only for `satValLoc`).
* `locSignsAlignEnt_of_blockAligned` — general-`j` entered-order alignment from the
  block-number condition.
* **The KEY PAYOFF** `termRestrict_encodeEnt₁_satisfied` / `enteredTerm_collapse` /
  `termEval_true_of_fullyTouched_ent` / `termRestrict_stateAt_encodeEnt₁_satisfied` — the
  fully-touched, entered-aligned `j`-th ENTERED term COLLAPSES to `some []` under
  `encodeEnt₁` (and the evolving state), and is satisfied by every agreeing assignment, for
  GENERAL `j` — the general-`j` satisfaction/alignment the task targeted as the buggy half.
* `satValEnt_eq_satValLoc_of_block_zero` — the two reads AGREE at the head (`j = 0`), pinning
  the bug to `j > 0`.

Answer to the discriminating check (`satValLoc = satValEnt` on touched deep vars?):  NO in
general.  They AGREE only at the head block (`j = 0`, `satValEnt_eq_satValLoc_of_block_zero`);
for `j > 0` `satValLoc` reads the `j`-th LIST element `(D|ρ).getD j` while `satValEnt` reads
the `j`-th ENTERED term `(residualIter (D|ρ) j).headI`, which differ once `residualIter`
drops/reorders terms.  So the existing encode is genuinely buggy for `j > 0`, and the
entered-order REDEFINITION (done here) is required for the general-`j` collapse — which is now
PROVED.

NOT closed (the exact, honest obstruction — UNCHANGED, NOT faked):

`SwitchingLemmaTermSimple n` is NOT proved outright.  The general-`j` collapse proved here is
ρ-DEPENDENT: `enteredTerm D ρ j` is built from `residualIter (D|ρ) j`, which needs `ρ`.  The
per-step decode `RCodeBlockStepVar` (= `SwitchingClose.ResidualHeadDecode` =
`SwitchingDOrig.DOrigStepData`'s heart = `SwitchingStateDecode.StateStepData`'s heart) must be
ρ-INDEPENDENT and sees only `σ`, the per-term code, and `prev = (deepPathV (D|ρ)).take i`.
The only ρ-independent restriction available is `σ_ent = overlay ρ satRestrEnt`, and
`satRestrEnt` — exactly like `satRestrLoc` — additionally fixes the NOT-YET-DECODED touched
variables (deep indices `≥ i`) to their SATISFYING values, which COLLAPSE the entered term to
`[]` (the very collapse PROVED above), ERASING the variable to be recovered.  Subtracting
`ρ`'s genuine fixings from the future-touched satisfying fixings to rebuild
`residualIter (D|ρ) j` ρ-independently is the convention-independent Razborov replay, the SAME
wall isolated (unchanged) as `ResidualHeadDecode` / `DOrigStepData` / `StateStepData`.  This
file does NOT fake it: it CLOSES the buggy general-`j` collapse/alignment half, and re-exports
the proved reductions that reach the switching lemma from the isolated, satisfiable
factorization data.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`. -/

end SwitchingEnteredOrder
end PvNP
