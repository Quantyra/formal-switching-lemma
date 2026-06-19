/-
# Two bounded deep-term auxiliary lemmas for the term-local switching encode

This file discharges TWO concrete lemmas that a prior audit found MISSING from the
switching-lemma development (`SwitchingEncodeLocal` / `SwitchingEncodeConstruct`).
It does NOT attempt to close the full switching lemma, `RCodeBlockStepVar`,
`DeepBlockRecoverableW`, or `LocDeepBlockRecoverableW`.

## LEMMA 1 — unconditional alignment for the HEAD deep term
`locSignsAlign_deep_head` discharges the `halign` hypothesis of
`SwitchingEncodeLocal.locSignsAlign_of_blockAligned` UNCONDITIONALLY for the FIRST
deep term `deepTermAt D ρ 0` (the head term of `D|ρ`, the first term ENTERED by the
deep path).  This is the genuinely-unconditional alignment case: the first deep
block is *exactly* the head term's variables in deep order
(`deepPathV_cons_cons_take` + `deepBlockLens_head`), so every head-term variable's
deep position lands in block `0`, and the alignment condition holds without any
hypothesis.

The general `j`-th-deep-term version is NOT provable in the stated form
`deepTermAt D ρ j = (D|ρ).getD j []`, because for `j > 0` the *list* index `j` of
`D|ρ` does NOT coincide with the `j`-th term *entered* by the deep path: after the
head block, control returns to `termCanonicalDT` of the RESIDUAL DNF, whose head
term is generally NOT `(D|ρ).getD j []`.  See the honesty note at the end.

## LEMMA 2 — first-σ-satisfied-term = the head deep term
`firstSat_eq_deepTerm_head` proves: when the head deep term `l :: t` of `D|ρ` is
fully-touched and aligned, it collapses to the constant-true term under
`σ_loc = encodeLoc₁ D s ρ`, hence it is the FIRST term of `D|ρ` satisfied by
`σ_loc`.  Combined with the prefix lemma `firstSat_eq_of_prefix_unsat` (a clean list
fact: a satisfied term preceded only by unsatisfied terms is the first satisfied
term) and the ρ-falsified-stay-unsatisfied half
(`termRestrict_encodeLoc₁_none_of_ρ`), this gives the general head/first-step form.

For a bad `ρ` the prefix `(deepPathV (D|ρ)).take 0 = []`, the residual `D₀ = D|ρ`,
and the head deep term IS the first ρ-surviving term; so this is the `i = 0` /
first-step instance of the audit's `firstSat_eq_deepTerm`.  The general `i`-th
version needs the canonical-DT replay that re-identifies the i-th *entered* term as
the head of the prefix-restricted residual AND that all earlier surviving terms are
unsatisfied — exactly the open content isolated as `LocDeepBlockRecoverableW`.  We
do NOT fake it; see the honesty note.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed
axioms ⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.
The existing green lemmas in the imported files are untouched.
-/
import PvNP.SwitchingEncodeLocal

namespace PvNP
namespace SwitchingDeepAux

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingCardLemma
open SwitchingEncodeConstruct
open SwitchingEncodeLocal
open Classical

/-! ## 0. Helper defs introduced by this file

* `prefixRestr pre` — the restriction fixing each `(v, b) ∈ pre` to `b`
  (used to form the prefix-restricted residual `Dᵢ` in Lemma 2's statement schema).
* `firstSatisfiedTerm E σ` — the first term of `E` collapsed to the constant-true
  term `[]` by `σ` (i.e. SATISFIED by `σ` in the term-local sense `termRestrict σ
  term = some []`). -/

/-- The restriction fixing each `(v, b)` in the prefix to `b`, free elsewhere.
This is the restriction by the first `i` deep decisions used to form the residual
`Dᵢ := dnfRestrict (prefixRestr prefix) D`. -/
noncomputable def prefixRestr {n : Nat} (pre : List (Fin n × Bool)) : Restriction n :=
  fun v => (pre.find? (fun vd => vd.1 = v)).map Prod.snd

/-- The first term of `E` that is SATISFIED by `σ` in the term-local sense, namely
collapsed to the constant-true term `[]` under `termRestrict σ` (every literal fixed
to its own sign).  `none` if no term is collapsed. -/
noncomputable def firstSatisfiedTerm {n : Nat} (E : DNF n) (σ : Restriction n) :
    Option (Term n) :=
  E.find? (fun term => decide (termRestrict σ term = some []))

/-! ## 1. Small list / restriction helpers -/

/-- If `v ∈ L.take b` then `v`'s first index in `L` is `< b` (the first occurrence
lies inside the length-`≤ b` prefix). -/
theorem indexOf_lt_of_mem_take {α : Type*} [DecidableEq α] (L : List α) (b : Nat)
    (v : α) (h : v ∈ L.take b) : L.indexOf v < b := by
  have happ : L = L.take b ++ L.drop b := (List.take_append_drop b L).symm
  have h1 : L.indexOf v = (L.take b).indexOf v := by
    conv_lhs => rw [happ]
    exact List.indexOf_append_of_mem h
  rw [h1]
  exact lt_of_lt_of_le (List.indexOf_lt_length.mpr h) (List.length_take_le b L)

/-- `encodeLoc₁ = overlay ρ (satRestrLoc …)` (definitional). -/
theorem encodeLoc₁_eq_overlay {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    encodeLoc₁ D s ρ = overlay ρ (satRestrLoc D s ρ) := rfl

/-- A ρ-FALSIFIED term stays falsified (`termRestrict = none`) under `σ_loc`, since
`σ_loc` only fixes variables FREE in `ρ`.  Term-level analogue of
`termEval_false_of_ρ_falsifies_loc`. -/
theorem termRestrict_encodeLoc₁_none_of_ρ {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (t : Term n) (h : termRestrict ρ t = none) :
    termRestrict (encodeLoc₁ D s ρ) t = none := by
  rw [encodeLoc₁_eq_overlay,
    termRestrict_overlay ρ (satRestrLoc D s ρ) t (satRestrLoc_disj D s ρ)]
  rw [h]; rfl

/-- Consequently a ρ-falsified term is NOT collapsed to the constant-true term by
`σ_loc` (so `firstSatisfiedTerm` skips it). -/
theorem not_satisfied_encodeLoc₁_of_ρ_falsifies {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (t : Term n) (h : termRestrict ρ t = none) :
    termRestrict (encodeLoc₁ D s ρ) t ≠ some [] := by
  rw [termRestrict_encodeLoc₁_none_of_ρ D s ρ t h]; simp

/-! ## 2. LEMMA 1 — unconditional alignment for the head deep term

We discharge the `halign` hypothesis of `locSignsAlign_of_blockAligned` for the head
deep term `deepTermAt D ρ 0` of any bad `ρ` whose `D|ρ` has a non-empty head term.
The head deep block is exactly the head term's variables in deep order
(`deepPathV_cons_cons_take` + `deepBlockLens_head`), so each head-term variable's
deep position is `< 1 + t.length` (the head block length) and therefore lies in
block `0`. -/

/-- **LEMMA 1 (PROVED — head deep term, UNCONDITIONAL alignment).**  For a simple
DNF `D` with `dnfRestrict ρ D = (l :: t) :: rest`, the alignment condition `halign`
holds for the head deep term and hence `LocSignsAlign D s ρ (deepTermAt D ρ 0)` holds
UNCONDITIONALLY (no `halign` hypothesis needed).  This is the cleanest provable form
of the audit's `locSignsAlign_deep` (the `j = 0` / head case; the general list-index
`j` case is not provable as stated — see the honesty note). -/
theorem locSignsAlign_deep_head {n : Nat} {D : DNF n} (hD : SimpleDNF D) (s : Nat)
    (ρ : Restriction n) (l : Literal n) (t : Term n) (rest : DNF n)
    (hcons : dnfRestrict ρ D = (l :: t) :: rest) :
    LocSignsAlign D s ρ (deepTermAt D ρ 0) := by
  have hterm0 : deepTermAt D ρ 0 = l :: t := by unfold deepTermAt; rw [hcons]; rfl
  -- the head term is simple (a term of the simple DNF `D|ρ`)
  have hsimple : SimpleTerm (deepTermAt D ρ 0) := by
    rw [hterm0]
    have hsr : SimpleDNF (dnfRestrict ρ D) := simpleDNF_dnfRestrict hD ρ
    rw [hcons] at hsr; exact hsr (l :: t) (List.mem_cons_self _ _)
  apply locSignsAlign_of_blockAligned D s ρ 0 hsimple
  intro l' hl'
  rw [hterm0] at hl'
  -- l'.var is among the first `1 + t.length` deep-path variables (the head block)
  have htake : ((deepPathV (dnfRestrict ρ D)).map Prod.fst).take (1 + t.length)
      = (l :: t).map (·.var) := by
    rw [hcons]; exact deepPathV_cons_cons_take l t rest
  have hmem : l'.var ∈ ((deepPathV (dnfRestrict ρ D)).map Prod.fst).take (1 + t.length) := by
    rw [htake]; exact List.mem_map_of_mem (·.var) hl'
  have hpos : deepPosOf D ρ l'.var < 1 + t.length := by
    unfold deepPosOf
    exact indexOf_lt_of_mem_take _ _ _ hmem
  -- `deepBlockLens (D|ρ)` has head exactly `1 + t.length`
  have hhead : (deepBlockLens (dnfRestrict ρ D)).head? = some (1 + t.length) := by
    rw [hcons]; exact deepBlockLens_head l t rest
  cases hbl : deepBlockLens (dnfRestrict ρ D) with
  | nil => rw [hbl] at hhead; simp at hhead
  | cons b bs =>
      rw [hbl] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      -- index in head block ⇒ block index 0
      rw [blockIndexOfIndex]; simp [hpos]

/-! ## 3. LEMMA 2 — first-σ-satisfied-term = the head deep term

A clean list lemma plus the term-local collapse give the head/first-step form of the
audit's `firstSat_eq_deepTerm`. -/

/-- **General first-satisfied list lemma (PROVED).**  If every term before `C` is NOT
satisfied by `σ` and `C` IS satisfied by `σ`, then `firstSatisfiedTerm` returns `C`.
A pure list fact about `find?`. -/
theorem firstSat_eq_of_prefix_unsat {n : Nat} (pre : List (Term n)) (C : Term n)
    (rest : DNF n) (σ : Restriction n)
    (hpre : ∀ p ∈ pre, termRestrict σ p ≠ some [])
    (hC : termRestrict σ C = some []) :
    firstSatisfiedTerm (pre ++ C :: rest) σ = some C := by
  unfold firstSatisfiedTerm
  induction pre with
  | nil => rw [List.nil_append, List.find?_cons]; simp [hC]
  | cons p ps ih =>
      rw [List.cons_append, List.find?_cons]
      have hp : ¬ (decide (termRestrict σ p = some []) = true) := by
        simp only [decide_eq_true_eq]; exact hpre p (List.mem_cons_self _ _)
      simp only [hp, if_neg]
      exact ih (fun q hq => hpre q (List.mem_cons_of_mem _ hq))

/-- **A fully-touched, locally-aligned term collapses to `[]` under `σ_loc` (PROVED).**
Restriction-level analogue of `termEval_true_of_fullyTouched_loc`: `σ_loc` fixes
every literal of the term to its own sign, so the term collapses to constant-true. -/
theorem termRestrict_encodeLoc₁_satisfied {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (t : Term n)
    (htouch : ∀ l ∈ t, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlign D s ρ t) :
    termRestrict (encodeLoc₁ D s ρ) t = some [] := by
  apply termRestrict_satisfied
  intro l hl
  unfold encodeLoc₁ overlay
  rw [satRestrLoc_eq_some D s ρ l.var (htouch l hl), hsign l hl]

/-- **LEMMA 2 (PROVED — head deep term is the first σ-satisfied term).**  For a simple
DNF `D` with `dnfRestrict ρ D = (l :: t) :: rest`, if the head deep term is
FULLY-TOUCHED (all its variables are touched — i.e. the head deep block lies within
the first `s` deep decisions), then it collapses to the constant-true term under
`σ_loc = encodeLoc₁ D s ρ`, and since it is the HEAD term of `D|ρ` it is the FIRST
term satisfied by `σ_loc`:
`firstSatisfiedTerm (dnfRestrict ρ D) (encodeLoc₁ D s ρ) = some (deepTermAt D ρ 0)`.

This is the `i = 0` / first-step instance of the audit's `firstSat_eq_deepTerm`
(prefix `= (deepPathV (D|ρ)).take 0 = []`, residual `D₀ = D|ρ`, head deep term =
first ρ-surviving term).  Alignment is supplied UNCONDITIONALLY by Lemma 1. -/
theorem firstSat_eq_deepTerm_head {n : Nat} {D : DNF n} (hD : SimpleDNF D) (s : Nat)
    (ρ : Restriction n) (l : Literal n) (t : Term n) (rest : DNF n)
    (hcons : dnfRestrict ρ D = (l :: t) :: rest)
    (htouch : ∀ l' ∈ (l :: t), l'.var ∈ touchedVars D s ρ) :
    firstSatisfiedTerm (dnfRestrict ρ D) (encodeLoc₁ D s ρ) = some (deepTermAt D ρ 0) := by
  have hterm0 : deepTermAt D ρ 0 = l :: t := by unfold deepTermAt; rw [hcons]; rfl
  -- alignment of the head deep term is unconditional (Lemma 1)
  have halign : LocSignsAlign D s ρ (l :: t) := by
    have := locSignsAlign_deep_head hD s ρ l t rest hcons
    rwa [hterm0] at this
  -- the head term collapses to [] under σ_loc
  have hcollapse : termRestrict (encodeLoc₁ D s ρ) (l :: t) = some [] :=
    termRestrict_encodeLoc₁_satisfied D s ρ (l :: t) htouch halign
  -- it is the head term of `D|ρ`, hence the first satisfied term
  rw [hcons, hterm0]
  have := firstSat_eq_of_prefix_unsat ([] : List (Term n)) (l :: t) rest
    (encodeLoc₁ D s ρ) (by intro p hp; exact absurd hp (List.not_mem_nil p)) hcollapse
  simpa using this

/-- **LEMMA 2 (general head/first-step form with ρ-falsified prefix, PROVED).**  A
self-contained restatement that does NOT require the deep term to be literally the
head of `D|ρ`: if `D|ρ` factors as `pre ++ C :: rest` where every term of `pre` is
ρ-FALSIFIED (hence stays unsatisfied under `σ_loc`, by
`termRestrict_encodeLoc₁_none_of_ρ`) and `C` is fully-touched and locally aligned
(hence collapsed by `σ_loc`), then `C` is the first σ_loc-satisfied term.  This is the
clean form usable per-step once the prefix-residual identification (the open
`LocDeepBlockRecoverableW` content) supplies that the i-th deep term is preceded only
by ρ-killed terms. -/
theorem firstSat_eq_of_ρ_falsified_prefix {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (pre : List (Term n)) (C : Term n) (rest : DNF n)
    (hfactor : dnfRestrict ρ D = pre ++ C :: rest)
    (hpre : ∀ p ∈ pre, termRestrict ρ p = none)
    (htouch : ∀ l ∈ C, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlign D s ρ C) :
    firstSatisfiedTerm (dnfRestrict ρ D) (encodeLoc₁ D s ρ) = some C := by
  rw [hfactor]
  apply firstSat_eq_of_prefix_unsat pre C rest (encodeLoc₁ D s ρ)
  · intro p hp
    exact not_satisfied_encodeLoc₁_of_ρ_falsifies D s ρ p (hpre p hp)
  · exact termRestrict_encodeLoc₁_satisfied D s ρ C htouch hsign

/-! ## 4. Honesty note — what is NOT closed here

LEMMA 1 general `j`: the audit's `locSignsAlign_deep` quantified over the `j`-th deep
term as `deepTermAt D ρ j = (dnfRestrict ρ D).getD j []`.  For `j > 0` this *list*
index of `D|ρ` does NOT equal the `j`-th term ENTERED by the deep path: after the
head block, `termCanonicalDT` returns control to the RESIDUAL DNF
`assignVar … ((l :: t) :: D)`, whose head term is generally a TRUNCATION/REORDER of
`(D|ρ).getD j []`, not that list element.  Hence the stated `halign` is *false in
general* for `deepTermAt = getD j`, and we prove only the `j = 0` head case
(`locSignsAlign_deep_head`), which is exactly what a per-step decode consumes (each
step operates on a residual whose head term is the relevant deep term).

LEMMA 2 general `i`: closing `firstSat_eq_deepTerm` for arbitrary `i` requires TWO
ingredients we do NOT have unconditionally: (a) the i-th deep term (the term entered
at deep step `i`) is the HEAD ρ-surviving term of the prefix-restricted residual
`Dᵢ = dnfRestrict (prefixRestr ((deepPathV (D|ρ)).take i)) D` — the canonical-DT
"process the first surviving term first" replay through the residualization; and
(b) every ρ-surviving term strictly before it in `Dᵢ` is NOT σ_loc-satisfied.  Both
are precisely the ρ-independent block-recovery content isolated as
`LocDeepBlockRecoverableW` (and its sibling `DeepBlockRecoverableW`).  We provide the
clean reusable list lemma (`firstSat_eq_of_prefix_unsat`), the term-local collapse
(`termRestrict_encodeLoc₁_satisfied`), the ρ-falsified-prefix form
(`firstSat_eq_of_ρ_falsified_prefix`), and the unconditional `i = 0` instance
(`firstSat_eq_deepTerm_head`); the residual-head identification for `i > 0` remains
the open Razborov replay and is NOT faked.
-/

end SwitchingDeepAux
end PvNP
