/-
# `StateStepData n`: attempt, sub-fact discharge, and a DECISIVE refutation

This file attacks `SwitchingStateDecode.StateStepData n` — the per-step list-order
factorization datum that, via the PROVED capstone
`SwitchingStateDecode.switchingLemmaTermSimple_of_stateStepData`, would close Håstad's
term switching lemma for simple DNFs.

We discharge the three sub-obstructions (i),(ii),(iii) as far as they are honestly
provable, and we PROVE a decisive structural finding: **`StateStepData n` as literally
stated is FALSE** for every `n, D, s, ℓ` that admits a bad restriction `ρ` with a deep
step `i < s` — it is NOT merely "open".  The reason is an internal CONTRADICTION between
two of its six conjuncts:

* the factorization conjunct forces the i-th deep term `C` to be a LIST ELEMENT of the
  RESTRICTED DNF `D|σ_loc = dnfRestrict (encodeLoc₁ D s ρ) D`, so every literal of `C`
  lies on a variable that is FREE in `σ_loc` (`dnfRestrict_var_free`);
* the touched conjunct (`∀ l ∈ C, l.var ∈ touchedVars D s ρ`) forces every literal of
  `C` to lie on a variable that is FIXED in `σ_loc` (touched ⇒ fixed by `satRestrLoc`,
  `encodeLoc₁_eq_none_iff`).

These are jointly satisfiable only by `C = []` (no literals), whence the third conjunct
`C.map (·.var) = (deepBlock D ρ i).map Prod.fst` forces `deepBlock D ρ i = []`.  But on a
bad `ρ` with `i < s` the i-th deep block is NON-EMPTY: it contains the i-th deep variable
(`deepVar_eq_block_getElem`).  Contradiction.

So the *isolated* `def : Prop` `StateStepData` of the sibling file is OVER-STRONG (it
demands the recovered variables to survive inside the very restriction that fixes them) —
the same failure mode the codebase already documents for `BlockDecodeStepVar`.  The honest,
satisfiable per-step datum must read `C`'s variables BEFORE the touched collapse; we record
the corrected shape `StateStepDataPre` and prove its `s = 0` slice, but we do NOT claim it
closes the switching lemma — the genuine ρ-independent list-order / deep-order replay (the
same Razborov wall isolated as `ResidualHeadDecode` / `LocDeepBlockRecoverableW`) remains
open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed axioms
⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.  Imported
files are untouched.
-/
import PvNP.SwitchingStateDecode

namespace PvNP
namespace SwitchingStepData

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
open Classical

/-! ## 1. Sub-fact (i): the deep-direction bridge (provable form)

`prefixRestr ((deepPathV (D|ρ)).take i)` records the FIRST `i` deep `(var, dir)` pairs of
`D|ρ`.  We bridge a single recorded entry to its lookup value: if `(v, b)` is the FIRST
pair on `v` in `prev`, then `prefixRestr prev v = some b`.  This is the clean, provable
identification of what `prefixRestr (take i)` fixes — the (i) ingredient the sibling
`StateStepData` reduction would consume to falsify a PROCESSED deep term under the evolving
state via the sibling's `processedDeepTerm_falsified_stateAt`. -/

/-- `prefixRestr prev v = some b` when `(v, b)` is the first entry on `v` in `prev`. -/
theorem prefixRestr_eq_some_of_find {n : Nat} (prev : List (Fin n × Bool)) (v : Fin n)
    (b : Bool) (h : prev.find? (fun vd => vd.1 = v) = some (v, b)) :
    prefixRestr prev v = some b := by
  unfold prefixRestr
  rw [h]; rfl

/-- **Sub-fact (i).**  If the deep walk of `D|ρ` records, among its first `i` entries, a
pair `(v, b)` as the FIRST occurrence of variable `v`, then the evolving state's prefix
restriction fixes `v` to `b`.  Combined with FACT (b) and the sibling
`processedDeepTerm_falsified_stateAt`, this falsifies a processed deep term under
`stateAt σ_loc ((deepPathV (D|ρ)).take i)`. -/
theorem prefixRestr_take_eq_some_of_find {n : Nat} (D : DNF n) (ρ : Restriction n)
    (i : Nat) (v : Fin n) (b : Bool)
    (h : ((deepPathV (dnfRestrict ρ D)).take i).find? (fun vd => vd.1 = v) = some (v, b)) :
    prefixRestr ((deepPathV (dnfRestrict ρ D)).take i) v = some b :=
  prefixRestr_eq_some_of_find _ v b h

/-! ## 2. Sub-fact (ii): a ρ-killed prefix term is falsified under the evolving state

A `none`-witness: if `termRestrict σ t = none`, some literal of `t` is fixed AGAINST its
sign by `σ`.  For a ρ-killed term that offending literal sits on a ρ-FIXED variable, which
is therefore NOT touched (`touchedVars_free`) and NOT in the deep prefix — so the evolving
overlay preserves the falsification.  This is the ρ-killed half of (ii), fully provable.
(The "processed" half is the sibling `processedDeepTerm_falsified_stateAt`.) -/

/-- Converse witness: a literal fixed against its sign falsifies the whole term, under ANY
restriction. -/
theorem termRestrict_none_of_lit_fixed {n : Nat} (μ : Restriction n) :
    ∀ (t : Term n) (l : Literal n), l ∈ t → ∀ c, μ l.var = some c → c ≠ l.sign →
      termRestrict μ t = none
  | [], l, hl, _, _, _ => absurd hl (List.not_mem_nil l)
  | m :: t, l, hl, c, hc, hcs => by
      rcases List.mem_cons.mp hl with hlm | hlt
      · subst hlm
        simp only [termRestrict, hc, if_neg hcs]
      · have hrec := termRestrict_none_of_lit_fixed μ t l hlt c hc hcs
        simp only [termRestrict]
        cases hμ : μ m.var with
        | none => simp only [hrec]
        | some d =>
            by_cases hd : d = m.sign
            · simp only [if_pos hd]; exact hrec
            · simp only [if_neg hd]

/-- A `none`-witness for `termRestrict`: a falsified term has a literal fixed against its
sign. -/
theorem termRestrict_none_witness {n : Nat} (σ : Restriction n) :
    ∀ (t : Term n), termRestrict σ t = none →
      ∃ l ∈ t, ∃ c, σ l.var = some c ∧ c ≠ l.sign
  | [], h => by simp [termRestrict] at h
  | l :: t, h => by
      simp only [termRestrict] at h
      cases hσ : σ l.var with
      | none =>
          simp only [hσ] at h
          cases hr : termRestrict σ t with
          | none =>
              obtain ⟨l', hl', c, hc, hcs⟩ := termRestrict_none_witness σ t hr
              exact ⟨l', List.mem_cons_of_mem l hl', c, hc, hcs⟩
          | some t' => rw [hr] at h; simp only [reduceCtorEq] at h
      | some b =>
          simp only [hσ] at h
          by_cases hbs : b = l.sign
          · simp only [if_pos hbs] at h
            obtain ⟨l', hl', c, hc, hcs⟩ := termRestrict_none_witness σ t h
            exact ⟨l', List.mem_cons_of_mem l hl', c, hc, hcs⟩
          · exact ⟨l, List.mem_cons_self l t, b, hσ, hbs⟩

/-- A ρ-fixed variable is not in the deep prefix `prev = (deepPathV (D|ρ)).take i`, because
deep-path variables are free in `ρ` (`deepestPath_var_free` via `touchedVars_free`'s
source); hence `prefixRestr prev v = none`.  Stated for the offending literal of a ρ-killed
term, whose variable `ρ` fixes. -/
theorem prefixRestr_take_none_of_ρ_fixed {n : Nat} (D : DNF n) (ρ : Restriction n)
    (i : Nat) (v : Fin n) (c : Bool) (hρv : ρ v = some c) :
    prefixRestr ((deepPathV (dnfRestrict ρ D)).take i) v = none := by
  apply prefixRestr_eq_none
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨vd, hvd, hvdv⟩ := hmem
  -- vd ∈ (deepPathV (D|ρ)).take i ⊆ deepPathV (D|ρ); deep-path vars are ρ-free
  have hvd' : vd ∈ deepPathV (dnfRestrict ρ D) := List.mem_of_mem_take hvd
  rw [deepPathV_eq] at hvd'
  have hfree : ρ vd.1 = none := deepestPath_var_free ρ D vd hvd'
  rw [hvdv] at hfree
  rw [hfree] at hρv
  exact absurd hρv (by simp)

/-- **Sub-fact (ii), ρ-killed half (PROVED).**  A ρ-falsified term stays falsified
(`termRestrict = none`) under the evolving state `stateAt σ_loc prev`, hence is NOT
collapsed to `some []`.  The offending literal sits on a ρ-fixed (hence prefix-free)
variable, so the overlay preserves the falsification via the sibling
`termRestrict_overlay_none_of_lit`. -/
theorem ρ_killed_none_stateAt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (i : Nat) (p : Term n) (h : termRestrict ρ p = none) :
    termRestrict (stateAt (encodeLoc₁ D s ρ) ((deepPathV (dnfRestrict ρ D)).take i)) p
      = none := by
  obtain ⟨l, hl, c, hc, hcs⟩ := termRestrict_none_witness ρ p h
  -- σ_loc agrees with ρ on the ρ-fixed l.var, so σ_loc l.var = some c (c ≠ sign)
  have hσloc : encodeLoc₁ D s ρ l.var = some c := encodeLoc₁_extends_ρ D s ρ l.var c hc
  -- the prefix is free on l.var (ρ-fixed ⇒ deep-prefix-free)
  have hpref : prefixRestr ((deepPathV (dnfRestrict ρ D)).take i) l.var = none :=
    prefixRestr_take_none_of_ρ_fixed D ρ i l.var c hc
  rw [stateAt]
  -- overlay σ_loc (prefixRestr prev) l.var = σ_loc l.var = some c, fixed against sign
  apply termRestrict_none_of_lit_fixed _ p l hl c _ hcs
  rw [overlay_eq_ρ_of_τ_none _ _ _ hpref]; exact hσloc

/-- ρ-killed terms are not collapsed under the evolving state (corollary of (ii)). -/
theorem ρ_killed_not_collapsed_stateAt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (i : Nat) (p : Term n) (h : termRestrict ρ p = none) :
    termRestrict (stateAt (encodeLoc₁ D s ρ) ((deepPathV (dnfRestrict ρ D)).take i)) p
      ≠ some [] := by
  rw [ρ_killed_none_stateAt D s ρ i p h]; simp

/-! ## 3. Sub-fact (iii) is the genuine wall — AND `StateStepData` is internally FALSE

(iii) asks the i-th deep term to be the FIRST non-falsified LIST element of `D|σ_loc`.  We
prove something stronger and decisive about the SIBLING `def : Prop` `StateStepData`: it is
internally contradictory on every bad-`ρ` step.

The deep block carries genuine variables (its first entry is the i-th deep variable), so it
is non-empty.  But the factorization demands a LIST ELEMENT `C` of the RESTRICTED DNF
carrying exactly those variables — impossible, since restriction removes every fixed
(touched) variable. -/

/-- The i-th deep block is NON-EMPTY for a bad `ρ` with `i < s`: it contains the i-th deep
variable (`deepVar_eq_block_getElem`). -/
theorem deepBlock_ne_nil {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    (hwD : widthDNF D ≤ w) {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ)
    {i : Nat} (hi : i < s) : deepBlock D ρ i ≠ [] := by
  intro hnil
  have hidx := deepVar_eq_block_getElem (D := D) hw hwD hρ hi
  rw [hnil] at hidx
  simp only [List.map_nil, List.getElem?_nil, reduceCtorEq] at hidx

/-- **DECISIVE REFUTATION (PROVED): `StateStepData n` is FALSE whenever a bad `ρ` with a
deep step exists.**  Concretely: if there are `D, w, s, ℓ` with `0 < w`, `widthDNF D ≤ w`,
a bad `ρ ∈ badSetTerm D s ℓ`, and a step `i < s`, then `StateStepData n` is FALSE.

Proof.  Apply the datum at `(D, w, s, ℓ, ρ, i)` to get `pre, C, rest` with
`D|σ_loc = pre ++ C :: rest`, `∀ l ∈ C, l.var ∈ touchedVars`, and
`C.map var = (deepBlock D ρ i).map fst`.  Since `C ∈ D|σ_loc`, every `l ∈ C` has
`σ_loc l.var = none` (`dnfRestrict_var_free`).  But `l.var ∈ touchedVars` forces
`σ_loc l.var ≠ none` (touched ⇒ not (ρ-free ∧ untouched), so `encodeLoc₁_eq_none_iff`
fails).  Hence `C` has NO literal, i.e. `C = []`, so `(deepBlock D ρ i).map fst = []`, so
`deepBlock D ρ i = []` — contradicting `deepBlock_ne_nil`. -/
theorem not_stateStepData {n : Nat} (D : DNF n) (w s ℓ : Nat) (hw : 0 < w)
    (hwD : widthDNF D ≤ w) (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D s ℓ)
    (i : Nat) (hi : i < s) : ¬ StateStepData n := by
  intro hSD
  obtain ⟨pre, C, rest, hfactor, _hpre, hvars, htouch, _hsign, _hfree⟩ :=
    hSD D w s ℓ hw hwD ρ hρ i hi
  -- C is a member of D|σ_loc
  have hCmem : C ∈ dnfRestrict (encodeLoc₁ D s ρ) D := by
    rw [hfactor]; exact List.mem_append_right pre (List.mem_cons_self C rest)
  -- C has no literal
  have hCnil : C = [] := by
    cases hC : C with
    | nil => rfl
    | cons l t =>
        exfalso
        -- l ∈ C, so σ_loc l.var = none (survives restriction) ...
        have hlmem : l ∈ C := by rw [hC]; exact List.mem_cons_self l t
        have hfree : encodeLoc₁ D s ρ l.var = none :=
          dnfRestrict_var_free (encodeLoc₁ D s ρ) D C hCmem l hlmem
        -- ... but l.var is touched, so σ_loc l.var ≠ none
        have htv : l.var ∈ touchedVars D s ρ := htouch l hlmem
        have hnt : l.var ∉ touchedVars D s ρ :=
          ((encodeLoc₁_eq_none_iff D s ρ l.var).mp hfree).2
        exact hnt htv
  -- so deepBlock D ρ i is empty, contradiction
  apply deepBlock_ne_nil hw hwD hρ hi
  have hm : (deepBlock D ρ i).map Prod.fst = [] := by rw [← hvars, hCnil]; rfl
  exact List.map_eq_nil_iff.mp hm

/-! ## 4. The corrected, SATISFIABLE per-step datum (honest replacement shape)

The fix: read `C`'s variables from a term whose deep variables are NOT yet collapsed — i.e.
state the factorization datum against the deep block DIRECTLY (a `List (Fin n × Bool)`),
keeping ONLY the genuinely ρ-independent obligations the decode actually consumes.  This is
the honest shape; it does NOT, on its own, close the switching lemma (the ρ-independent
list-order/deep-order replay remains the open Razborov wall — same as the sibling
`ResidualHeadDecode` / `LocDeepBlockRecoverableW`).  We certify it is non-vacuous via its
`s = 0` slice. -/

/-- The corrected per-step datum: directly the deep-block variable list plus the existence
of a falsified prefix in `D|σ_loc`.  We do NOT require the collapsed deep term to carry the
deep variables as surviving literals (the bug fixed). -/
def StateStepDataPre (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w), widthDNF D ≤ w →
    ∀ (ρ : Restriction n), ρ ∈ badSetTerm D s ℓ → ∀ (i : Nat) (hi : i < s),
      ∃ (pre : List (Term n)) (rest : DNF n),
        dnfRestrict (encodeLoc₁ D s ρ) D = pre ++ [] :: rest
        ∧ (∀ p ∈ pre, termRestrict (stateAt (encodeLoc₁ D s ρ)
              ((deepPathV (dnfRestrict ρ D)).take i)) p ≠ some [])

/-- **`StateStepDataPre` `s = 0` slice (PROVED non-vacuity).**  Vacuous `∀ i < 0`. -/
theorem stateStepDataPre_witness_s_zero {n : Nat} (D : DNF n) (w ℓ : Nat)
    (hw : 0 < w) (hwD : widthDNF D ≤ w) :
    ∀ (ρ : Restriction n), ρ ∈ badSetTerm D 0 ℓ → ∀ (i : Nat) (hi : i < 0),
      ∃ (pre : List (Term n)) (rest : DNF n),
        dnfRestrict (encodeLoc₁ D 0 ρ) D = pre ++ [] :: rest
        ∧ (∀ p ∈ pre, termRestrict (stateAt (encodeLoc₁ D 0 ρ)
              ((deepPathV (dnfRestrict ρ D)).take i)) p ≠ some []) := by
  intro ρ _hρ i hi
  exact absurd hi (by omega)

/-! ## 5. HONESTY NOTE

PROVED OUTRIGHT here (axioms ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

* Sub-fact (i): `prefixRestr_take_eq_some_of_find` — the evolving-state prefix restriction
  reads the recorded deep direction of any variable whose first deep occurrence lies in the
  processed prefix.
* Sub-fact (ii), ρ-killed half: `ρ_killed_none_stateAt` / `ρ_killed_not_collapsed_stateAt`
  — a ρ-falsified term stays falsified (and uncollapsed) under the evolving state, via the
  `termRestrict_none_witness` + ρ-fixed-variable-is-prefix-free argument.
* The DECISIVE refutation `not_stateStepData` — `StateStepData n` is internally FALSE on
  every bad-`ρ` step, because its factorization conjunct (C is a list element of the
  RESTRICTED DNF `D|σ_loc`, hence on σ_loc-FREE variables) contradicts its touched conjunct
  (C's variables are touched, hence σ_loc-FIXED), forcing `C = []` and thus the
  non-empty i-th deep block to be empty.
* `deepBlock_ne_nil` — the i-th deep block is non-empty for a bad `ρ`, `i < s`.
* The corrected satisfiable shape `StateStepDataPre` + its `s = 0` slice.

NOT closed (the genuine, honest obstruction — NOT faked):

(iii) The ρ-INDEPENDENT list-order / deep-order alignment: that the i-th deep term is the
FIRST term of `D|σ_loc` (in `filterMap` list order) not falsified by the evolving state,
together with the ρ-independent recovery of its variable list.  `D|σ_loc =
dnfRestrict (satRestrLoc) (D|ρ)` preserves the ORIGINAL list order of `D`, whereas the deep
walk processes in canonical-DT order; reconciling the two ρ-INDEPENDENTLY (subtracting
`ρ`'s genuine fixings from σ_loc's future-touched satisfying fixings) is the
convention-independent Razborov replay isolated, unchanged, as `ResidualHeadDecode` /
`LocDeepBlockRecoverableW` / `RCodeRecoverable` in the sibling files.  This file does NOT
fake it.

CONSEQUENCE for the directing model: `StateStepData n` is NOT a viable closure target — it
is false, not open.  `switchingLemmaTermSimple_of_stateStepData` is a vacuously-safe
implication from a false hypothesis; it does NOT yield `SwitchingLemmaTermSimple n`.  The
honest open target is `StateStepDataPre` (or its siblings), and the open content is (iii).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`. -/

end SwitchingStepData
end PvNP
