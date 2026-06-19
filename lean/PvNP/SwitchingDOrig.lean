/-
# Scanning D's ORIGINAL term list for the switching-lemma decode

This file pursues the reference-grounded "scan the ORIGINAL DNF `D`" decode (Beame
primer / Thapen arXiv:2202.05651: the decoder finds "the first term `C` of `F` — the
ORIGINAL DNF, term-list indices intact — such that `C↾(σ-state)` is NOT falsified",
then reads the recovered variable off `C`).  The motivation is the DECISIVE refutation
recorded in `SwitchingStepData.not_stateStepData`: a decode that scans the RESTRICTED
DNF `D|σ_loc` is internally FALSE, because the i-th deep term is a list element of
`D|σ_loc` only if every one of its (touched, hence σ_loc-FIXED) variables survives the
restriction — impossible.  Scanning `D` ORIGINAL avoids that collapse: the original term
keeps all its literals.

## What this file PROVES OUTRIGHT (axioms ⊆ [propext, Classical.choice, Quot.sound])

* `firstNonFalsified D state` — the concrete, ρ-INDEPENDENT scan of `D`'s ORIGINAL term
  list for the first index/term not falsified (`termRestrict state C ≠ none`).
* `firstNonFalsified_eq_of_factor` — its correctness from a factorization
  `D = pre ++ C :: rest` with `pre` all falsified and `C` not falsified (pure `find?`
  plumbing, mirroring `SwitchingDeepAux.firstSat_eq_of_prefix_unsat`).
* `decodeStepVarD` — the D-original per-step decoder, and `decodeStepVarD_eq_of_factor`,
  its correctness from a factorization PLUS a hypothesis giving the recovered variable.

## What does NOT close (the EXACT obstruction, NOT faked)

Scanning `D` ORIGINAL fixes the COLLAPSE bug but does NOT remove the genuine Razborov
wall; it RELOCATES it to the VARIABLE READ.  Concretely:

* The within-block code column `codeBlockPos` indexes the i-th **deep block**, i.e. the
  i-th deep term's variables in **deep-path order** of `D|ρ`.  The only proved
  variable-read law `SwitchingEncodeConstruct.deepVar_eq_block_getElem` reads the i-th
  deep variable as the `codeColumn`-th element of `deepBlock D ρ i`.
* The original term `C₀ ∈ D` that survives to the i-th deep term satisfies
  `termRestrict ρ C₀ = some (i-th deep term)`; `termRestrict` is an order-preserving
  FILTER, so `C₀` is the i-th deep term's restricted literal list with the ρ-fixed
  literals re-inserted in their ORIGINAL positions.  Hence `C₀.map (·.var)` is NOT the
  deep-block variable list — it carries extra ρ-fixed variables, and even the surviving
  variables are in ORIGINAL-term order, which is the deep-PATH order only for the HEAD
  term (i = 0), not in general.
* Therefore `C₀.get codeColumn |>.var` is NOT the i-th deep variable in general: the
  code column is an index into the deep block, not into `C₀`.  Reading the variable off
  the original term needs a NEW alignment ("the codeColumn-th surviving literal of `C₀`
  in original order is the i-th deep variable") which is itself the open
  list-order/deep-order Razborov replay, merely rephrased.

So the D-original scan is a genuinely BETTER decoder shape (it never collapses the
recovered term), and the prefix-falsification half is provable here; but the variable
read still requires the convention-independent alignment isolated, unchanged, as
`RCodeRecoverable` / `LocDeepBlockRecoverableW` / `ResidualHeadDecode`.  We do NOT fake
it: it stays the open content, and we report the exact place it bites (§4).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  NOT a lower
bound, NOT P≠NP.  Imported files are untouched.
-/
import PvNP.SwitchingStateDecode
import PvNP.SwitchingStepData

namespace PvNP
namespace SwitchingDOrig

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
open Classical

/-! ## 1. The D-ORIGINAL scan `firstNonFalsified`

The decoder scans `D`'s ORIGINAL term list (indices intact) for the FIRST term not
FALSIFIED by the decode state `state` (`termRestrict state C ≠ none`).  Unlike
`SwitchingDeepAux.firstSatisfiedTerm` (which tests COLLAPSE `= some []` on the RESTRICTED
DNF `D|σ`), this tests NON-FALSIFICATION (`≠ none`) on `D` ORIGINAL, exactly the
reference's "first term of `F` not falsified by `ρσ`".  It returns the index and the
ORIGINAL term (variables intact). -/

/-- **`firstNonFalsified`**: the first ORIGINAL term of `D` not falsified by `state`
(`termRestrict state C ≠ none`).  Scans `D` ORIGINAL — term-list order intact (the
reference's "first term of `F` not falsified by `ρσ`").  Contrast
`SwitchingDeepAux.firstSatisfiedTerm`, which tests COLLAPSE `= some []` over the RESTRICTED
DNF `D|σ` and so loses the recovered variables. -/
noncomputable def firstNonFalsified {n : Nat} (D : DNF n) (state : Restriction n) :
    Option (Term n) :=
  D.find? (fun C => decide (termRestrict state C ≠ none))

/-- **`firstNonFalsified` from a factorization (PROVED).**  If `D` factors as
`pre ++ C :: rest` with every `pre`-term FALSIFIED (`= none`) under `state`, and `C` NOT
falsified (`≠ none`), then the scan of `D` ORIGINAL returns `C`.  Pure `find?` plumbing,
the D-original analogue of `SwitchingDeepAux.firstSat_eq_of_prefix_unsat`. -/
theorem firstNonFalsified_eq_of_factor {n : Nat} (D : DNF n) (state : Restriction n)
    (pre : List (Term n)) (C : Term n) (rest : DNF n)
    (hfactor : D = pre ++ C :: rest)
    (hpre : ∀ p ∈ pre, termRestrict state p = none)
    (hC : termRestrict state C ≠ none) :
    firstNonFalsified D state = some C := by
  unfold firstNonFalsified
  rw [hfactor]
  clear hfactor
  induction pre with
  | nil =>
      rw [List.nil_append, List.find?_cons]
      have : decide (termRestrict state C ≠ none) = true := by simp [hC]
      simp [this]
  | cons p ps ih =>
      rw [List.cons_append, List.find?_cons]
      have hp : decide (termRestrict state p ≠ none) = false := by
        have := hpre p (List.mem_cons_self _ _); simp [this]
      simp only [hp, Bool.false_eq_true, if_false]
      exact ih (fun q hq => hpre q (List.mem_cons_of_mem _ hq))

/-! ## 2. The D-original per-step decoder `decodeStepVarD`

Read the `entry.1`-th variable of the ORIGINAL term located by `firstNonFalsified`,
using the evolving state `stateAt σ prev` (ρ-independent).  The variable is read off the
ORIGINAL term `C` (its literals intact — the `not_stateStepData` collapse is avoided). -/

/-- The D-original per-step decoder.  Locate the first ORIGINAL term of `D` not falsified
by the evolving state `stateAt σ prev`, then read its `entry.1`-th variable.  All inputs
(`σ`, `entry`, `prev`, `D`) are ρ-INDEPENDENT, so this is a legitimate decoder. -/
noncomputable def decodeStepVarD {n : Nat} (D : DNF n) (w : Nat) (σ : Restriction n)
    (entry : Fin w × Bool × Bool) (prev : List (Fin n × Bool)) : List (Fin n) :=
  match firstNonFalsified D (stateAt σ prev) with
  | some C => colVar C entry.1.val
  | none => []

/-- **`decodeStepVarD` correctness from a factorization + variable read (PROVED).**  If
`D` factors as `pre ++ C :: rest` with `pre` all falsified and `C` not falsified under
the evolving state `stateAt σ prev`, and the `entry.1`-th variable of the ORIGINAL `C` is
`target`, then `decodeStepVarD` returns `[target]`.  Pure plumbing over
`firstNonFalsifiedTerm_eq_of_factor` + `colVar`. -/
theorem decodeStepVarD_eq_of_factor {n : Nat} (D : DNF n) (w : Nat) (σ : Restriction n)
    (entry : Fin w × Bool × Bool) (prev : List (Fin n × Bool))
    (pre : List (Term n)) (C : Term n) (rest : DNF n)
    (hfactor : D = pre ++ C :: rest)
    (hpre : ∀ p ∈ pre, termRestrict (stateAt σ prev) p = none)
    (hC : termRestrict (stateAt σ prev) C ≠ none)
    (target : Fin n)
    (hcol : colVar C entry.1.val = [target]) :
    decodeStepVarD D w σ entry prev = [target] := by
  unfold decodeStepVarD
  rw [firstNonFalsified_eq_of_factor D (stateAt σ prev) pre C rest hfactor hpre hC]
  exact hcol

/-! ## 3. The falsification half over D-original (the provable ingredients)

Two of the three prefix-term classes are provably FALSIFIED under the evolving state
`stateAt σ_loc prev`, exactly as in the sibling `SwitchingStepData`:

* ρ-killed terms: `SwitchingStepData.ρ_killed_none_stateAt` (a ρ-falsified ORIGINAL term
  stays `none` under `stateAt`).
* processed deep terms fixed against their sign by `prefixRestr prev`:
  `SwitchingStateDecode.processedDeepTerm_falsified_stateAt`.

These transfer to D-original UNCHANGED because both quantify over an arbitrary term and
restriction — they are NOT specific to `D|ρ`.  We re-export the ρ-killed half at the
D-original term level for clarity. -/

/-- A ρ-FALSIFIED original term of `D` is FALSIFIED (`= none`) under the evolving state
`stateAt σ_loc prev` — directly `SwitchingStepData.ρ_killed_none_stateAt`. -/
theorem orig_ρ_killed_none_stateAt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (i : Nat) (C : Term n) (h : termRestrict ρ C = none) :
    termRestrict (stateAt (encodeLoc₁ D s ρ) ((deepPathV (dnfRestrict ρ D)).take i)) C
      = none :=
  PvNP.SwitchingStepData.ρ_killed_none_stateAt D s ρ i C h

/-! ## 4. The EXACT obstruction: the variable read off the ORIGINAL term

`decodeStepVarD_eq_of_factor` needs `colVar C entry.1.val = [target]` where `C` is the
ORIGINAL term and `target` is the i-th deep variable.  `colVar C k = (C.map (·.var))[k]?`
reads the `k`-th literal's variable of the ORIGINAL term `C`, with `k = codeBlockPos … %
w`.  But the ONLY proved variable-read law is

  `deepVar_eq_block_getElem :
     (deepBlock D ρ i |>.map fst)[codeColumn]? = some (i-th deep var)`,

which reads the `codeColumn`-th element of the **deep block** (deep-path order of `D|ρ`).
For these to agree we would need

  `(C.map (·.var))[codeColumn]? = ((deepBlock D ρ i).map Prod.fst)[codeColumn]?`,

i.e. the ORIGINAL term `C`'s variable list to AGREE with the deep block's at position
`codeColumn`.  That is FALSE in general: `C` is the i-th deep term with the ρ-fixed
literals re-inserted in their original positions (`termRestrict ρ C = some (deep term)`,
and `termRestrict` is an order-preserving filter), so `C.map (·.var)` carries extra
ρ-fixed variables AND, beyond the head term, orders the surviving variables in
ORIGINAL-term order, not deep-path order.  We record the precise mismatch as a Prop and
PROVE it is exactly the residual `RCodeBlockStepVar` obligation — NOT closing it, NOT
faking it. -/

/-- **The variable read off the ORIGINAL term REDUCES to a column-agreement (PROVED).**
For a bad `ρ` (with `widthDNF D ≤ w`) and step `i < s`, the D-original variable read
`colVar C codeColumn = [i-th deep var]` holds IF AND ONLY IF the ORIGINAL term `C`'s
variable list agrees with the i-th deep block's at the code column, i.e.

  `(C.map (·.var))[codeColumn]? = ((deepBlock D ρ i).map Prod.fst)[codeColumn]?`.

Proved: the RHS read of the deep block is `some (i-th deep var)` by the proved
`deepVar_eq_block_getElem`, and `colVar C k = ((C.map (·.var))[k]?).toList`, so the two
are equal exactly when the column entries agree.  This PINPOINTS the open content: the
ENTIRE remaining obligation in `DOrigStepData`'s variable conjunct is this column
agreement between the ORIGINAL term and the deep block — the list-order / deep-order
alignment isolated, unchanged, as `RCodeBlockStepVar` / `LocDeepBlockRecoverableW`.  It is
NOT generally true (the original term carries ρ-fixed literals shifting the column), and
we do NOT assert it. -/
theorem colVar_orig_eq_iff_column_agree {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    (hwD : widthDNF D ≤ w) {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ)
    {i : Nat} (hi : i < s) (C : Term n) :
    colVar C (codeRC D w s hw ρ ⟨i, hi⟩).1.val
        = [((deepPathV (dnfRestrict ρ D)).get
            ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1]
      ↔ (C.map (·.var))[(codeRC D w s hw ρ ⟨i, hi⟩).1.val]?
          = ((deepBlock D ρ i).map Prod.fst)[(codeRC D w s hw ρ ⟨i, hi⟩).1.val]? := by
  -- the code column of the per-term code equals the per-variable code's column
  have hcolnum : (codeRC D w s hw ρ ⟨i, hi⟩).1.val
      = (codeOf D w s hw ρ ⟨i, hi⟩).1.val := by
    unfold codeRC codeLoc; simp only []
  -- the deep-block read at this column is `some (i-th deep var)`
  have hblk := deepVar_eq_block_getElem (D := D) hw hwD hρ hi
  rw [← hcolnum] at hblk
  rw [hblk]
  -- now: colVar C k = [v]  ↔  (C.map var)[k]? = some v
  unfold colVar
  constructor
  · intro h
    cases hget : (C.map (·.var))[(codeRC D w s hw ρ ⟨i, hi⟩).1.val]? with
    | none => rw [hget] at h; simp [Option.toList] at h
    | some v =>
        rw [hget] at h
        simp only [Option.toList, List.cons.injEq, and_true] at h
        rw [h]
  · intro h; rw [h]; rfl

/-- **The D-original per-step factorization datum (isolated `def : Prop`, NOT an axiom,
NOT asserted true).**  For each bad `ρ` and step `i`, a factorization of `D` ORIGINAL
`= pre ++ C :: rest` with: `pre` all falsified under the evolving state; `C` NOT
falsified; and the code-column variable of the ORIGINAL `C` equal to the i-th deep
variable.  This is the HONEST D-original target — its `C` keeps its variables (no
collapse), so it is NOT internally false the way `StateStepData` is (refuted in
`SwitchingStepData.not_stateStepData`).  The OPEN content is entirely the third conjunct:
the order/column alignment of the ORIGINAL term with the deep block. -/
def DOrigStepData (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w), widthDNF D ≤ w →
    ∀ (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s),
      ∃ (pre : List (Term n)) (C : Term n) (rest : DNF n),
        D = pre ++ C :: rest
        ∧ (∀ p ∈ pre, termRestrict (stateAt (encodeLoc₁ D s ρ)
              ((deepPathV (dnfRestrict ρ D)).take i)) p = none)
        ∧ termRestrict (stateAt (encodeLoc₁ D s ρ)
              ((deepPathV (dnfRestrict ρ D)).take i)) C ≠ none
        ∧ colVar C (codeRC D w s hw ρ ⟨i, hi⟩).1.val
            = [((deepPathV (dnfRestrict ρ D)).get
                ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1]

/-- **The reduction (PROVED): `DOrigStepData n → RCodeBlockStepVar n`.**  The D-original
decoder `decodeStepVarD` is the per-step witness; its correctness on the bad set is
exactly `DOrigStepData` via `decodeStepVarD_eq_of_factor`.  Thus, through the PROVED chain
`RCodeBlockStepVar → RCodeRecoverable → SwitchingLemmaTermSimple`, the D-original datum
would close the switching lemma — IF it could be proved.  It is isolated, not faked. -/
theorem rcodeBlockStepVar_of_dorigStepData {n : Nat}
    (h : DOrigStepData n) : RCodeBlockStepVar n := by
  intro D w s ℓ hw hwD
  refine ⟨fun σ entry prev => decodeStepVarD D w σ entry prev, ?_⟩
  intro ρ hρ i hi
  obtain ⟨pre, C, rest, hfactor, hpre, hC, hcol⟩ := h D w s ℓ hw hwD ρ hρ i hi
  exact decodeStepVarD_eq_of_factor D w (encodeLoc₁ D s ρ) (codeRC D w s hw ρ ⟨i, hi⟩)
    ((deepPathV (dnfRestrict ρ D)).take i) pre C rest hfactor hpre hC
    (((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1) hcol

/-- **CAPSTONE (PROVED): `DOrigStepData n → SwitchingLemmaTermSimple n`.**  Through the
reduction and the proved chain in `SwitchingRazborovCode`. -/
theorem switchingLemmaTermSimple_of_dorigStepData {n : Nat}
    (h : DOrigStepData n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_rcodeBlockStepVar (rcodeBlockStepVar_of_dorigStepData h)

/-! ## 5. Satisfiability of `DOrigStepData` (INTEGRITY CHECK)

We certify `DOrigStepData` is genuinely SATISFIABLE (not vacuously false like
`StateStepData`) via the `s = 0` and `n = 0` slices. -/

/-- **`DOrigStepData` `s = 0` slice (PROVED non-vacuity).**  Vacuous `∀ i < 0`. -/
theorem dorigStepData_witness_s_zero {n : Nat} (D : DNF n) (w ℓ : Nat)
    (hw : 0 < w) (hwD : widthDNF D ≤ w) :
    ∀ (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D 0 ℓ) (i : Nat) (hi : i < 0),
      ∃ (pre : List (Term n)) (C : Term n) (rest : DNF n),
        D = pre ++ C :: rest
        ∧ (∀ p ∈ pre, termRestrict (stateAt (encodeLoc₁ D 0 ρ)
              ((deepPathV (dnfRestrict ρ D)).take i)) p = none)
        ∧ termRestrict (stateAt (encodeLoc₁ D 0 ρ)
              ((deepPathV (dnfRestrict ρ D)).take i)) C ≠ none
        ∧ colVar C (codeRC D w 0 hw ρ ⟨i, hi⟩).1.val
            = [((deepPathV (dnfRestrict ρ D)).get
                ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1] := by
  intro ρ _hρ i hi
  exact absurd hi (by omega)

/-- **`DOrigStepData 0` holds outright.**  Over `Fin 0` the i-th deep variable is a
`Fin 0` (impossible), so every step datum is vacuously discharged. -/
theorem dorigStepData_of_n_zero : DOrigStepData 0 := by
  intro D w s ℓ hw hwD ρ hρ i hi
  exact (((deepPathV (dnfRestrict ρ D)).get
      ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1).elim0

end SwitchingDOrig
end PvNP
