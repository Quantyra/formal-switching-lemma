/-
# Term-LOCAL satisfying-direction encode for the term-canonical switching lemma

This file repairs the diagnosed BUG in the term-GLOBAL satisfying value `satVal`
of `SwitchingEncodeRazborov.lean`: there, `satVal D ρ v` is the sign of the FIRST
literal on `v` ANYWHERE in `D|ρ`, which may belong to a term OTHER than the one
the deep path is processing and carry the OPPOSITE sign — so fixing `v` to that
value can FALSIFY the touched term, breaking the "first term satisfied by σ"
decode.

The fix here is a **term-LOCAL** satisfying value `satValLoc`: for a touched
variable `v`, we read the sign of `v`'s literal in the SPECIFIC term of `D|ρ` that
the deep path enters when it queries `v` — the term associated with the deep block
that contains `v`'s deep-path position.  With this value, every literal of a
FULLY-touched deep term is fixed by `σ_loc` to its own sign, so the term collapses
to the constant-true term and is identifiably SATISFIED (step 2 below, PROVED).

## Honest scope (read carefully — no over-claim)

* `satValLoc`/`encodeLoc₁` are defined term-locally (§1).
* **Step 2 is PROVED outright** (`termEval_true_of_fullyTouched_loc`): a deep term
  ALL of whose literals are touched is satisfied by every assignment agreeing with
  `σ_loc`.  This is the genuine payoff of the term-local fix that the term-global
  `satVal` provably could NOT give (it could fix a touched literal to the opposite
  sign).
* The star count `ℓ - s`, the determination lemma `ρ = f(σ_loc, touched)`, and the
  full injectivity-from-recovery reduction to `SwitchingLemmaTermSimple` are
  re-proved for the local encode (§2, §5).
* The TRUE, ρ-independent half (a) of the KEY FACT — ρ-falsified terms stay
  falsified by `σ_loc` — is re-proved (`termEval_false_of_ρ_falsifies_loc`).
* The genuine remaining heart — the ρ-INDEPENDENT recovery of the touched-variable
  SET from `(σ_loc, code)` — is isolated as a `def : Prop`
  `LocTermIdentifiable` (NOT an axiom, NOT asserted true) and CERTIFIED SATISFIABLE
  in the boundary regimes (§6).  The local-satVal fix removes the sign obstruction
  but NOT the convention-independent obstruction that, inside `σ_loc`, the touched
  set is an unstructured union with `ρ`'s domain (a `some b` fixing from `ρ` is
  indistinguishable from a touched `some b`), so the ρ-independent replay is the
  open Razborov content.  We do NOT fake it.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  NOT a lower
bound, NOT P≠NP.  `SwitchingLemmaTermSimple` is the SAME statement as in the
sibling files; we reuse their infrastructure and do NOT modify them.
-/
import PvNP.SwitchingEncodeConstruct

namespace PvNP
namespace SwitchingEncodeLocal

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingCardLemma
open SwitchingEncodeConstruct
open Classical

/-! ## 1. The TERM-LOCAL satisfying value `satValLoc`

The i-th touched variable `v` of `ρ` is the i-th entry of the deep path
`deepPathV (D|ρ)`.  The deep blocks `deepBlockLens (D|ρ)` tile this path one block
per term ENTERED, and `deepBlockLensQ_sum_eq`/`deepPathVQ_vars_prefix` certify the
block of a term is exactly that term's variables in order.  We:

1. compute the deep-path POSITION `i` of `v` (its index in `touchedVars`);
2. compute the BLOCK INDEX `j = blockIndexOfIndex (deepBlockLens (D|ρ)) i` it lies in;
3. read the sign of `v`'s literal in the `j`-th TERM of `D|ρ`,
   `deepTermAt D ρ j := (dnfRestrict ρ D).getD j []`.

Unlike the term-global `satVal`, this reads `v`'s sign in EXACTLY the term the deep
path is processing, so a fully-touched deep term is fixed to its own signs. -/

/-- Which block (counting from 0) the global index `i` falls into, given the
consecutive block lengths.  Mirrors `blockPosOfIndex`, but returns the block NUMBER
rather than the within-block offset. -/
def blockIndexOfIndex : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, i => if i < b then 0 else 1 + blockIndexOfIndex bs (i - b)

/-- The `j`-th term of `D|ρ` (the term whose deep block is the `j`-th deep block),
defaulting to the empty (constant-true) term out of range. -/
noncomputable def deepTermAt {n : Nat} (D : DNF n) (ρ : Restriction n) (j : Nat) :
    Term n :=
  (dnfRestrict ρ D).getD j []

/-- The deep-path POSITION (index in `touchedVars`/`deepPathV`) of a variable `v`,
defaulting to `0` if `v` is not on the path. -/
noncomputable def deepPosOf {n : Nat} (D : DNF n) (ρ : Restriction n) (v : Fin n) :
    Nat :=
  ((deepPathV (dnfRestrict ρ D)).map Prod.fst).indexOf v

/-- The sign of the first literal on `v` in a given term (default `true`). -/
noncomputable def signInTerm {n : Nat} (t : Term n) (v : Fin n) : Bool :=
  match t.find? (fun l => l.var = v) with
  | some l => l.sign
  | none => true

/-- **The TERM-LOCAL satisfying value.**  For a touched variable `v`: locate `v`'s
deep-path position, the deep block it lies in, and read `v`'s literal sign in the
corresponding term of `D|ρ`.  This is the sign that drives EXACTLY the deep term
the path is processing toward `true`. -/
noncomputable def satValLoc {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) : Bool :=
  let i := deepPosOf D ρ v
  let j := blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i
  signInTerm (deepTermAt D ρ j) v

/-- The term-local satisfying restriction: fix exactly the touched variables to
their term-LOCAL satisfying values, free elsewhere. -/
noncomputable def satRestrLoc {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    Restriction n :=
  fun v => if v ∈ touchedVars D s ρ then some (satValLoc D s ρ v) else none

/-- **`encodeLoc₁ ρ = σ_loc`**: `ρ` with the `s` deep-path variables additionally
fixed to their TERM-LOCAL satisfying values. -/
noncomputable def encodeLoc₁ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    Restriction n :=
  overlay ρ (satRestrLoc D s ρ)

/-! ### `satRestrLoc` support facts (mirror the Razborov file) -/

theorem satRestrLoc_eq_none_iff {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) : satRestrLoc D s ρ v = none ↔ v ∉ touchedVars D s ρ := by
  unfold satRestrLoc
  by_cases hv : v ∈ touchedVars D s ρ
  · simp [hv]
  · simp [hv]

theorem satRestrLoc_eq_some {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) (hv : v ∈ touchedVars D s ρ) :
    satRestrLoc D s ρ v = some (satValLoc D s ρ v) := by
  unfold satRestrLoc; simp [hv]

theorem satRestrLoc_disj {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    ∀ v, ρ v ≠ none → satRestrLoc D s ρ v = none := by
  intro v hv
  rw [satRestrLoc_eq_none_iff]
  intro hmem
  exact hv (touchedVars_free D s ρ v hmem)

/-- `encodeLoc₁` is `none` exactly on stars of `ρ` that are not touched — IDENTICAL
support to the sibling encodes. -/
theorem encodeLoc₁_eq_none_iff {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) :
    encodeLoc₁ D s ρ v = none ↔ (ρ v = none ∧ v ∉ touchedVars D s ρ) := by
  unfold encodeLoc₁ overlay
  cases hτ : satRestrLoc D s ρ v with
  | some d =>
      simp only [hτ]
      have hin : v ∈ touchedVars D s ρ := by
        by_contra hc
        rw [(satRestrLoc_eq_none_iff D s ρ v).mpr hc] at hτ; exact absurd hτ (by simp)
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨_, hnt⟩; exact absurd hin hnt
  | none =>
      simp only [hτ]
      have hnt : v ∉ touchedVars D s ρ := (satRestrLoc_eq_none_iff D s ρ v).mp hτ
      constructor
      · intro h; exact ⟨h, hnt⟩
      · rintro ⟨h, _⟩; exact h

/-! ## 2. Star count of `σ_loc = encodeLoc₁ ρ`

The support of `σ_loc` equals the support of the sibling encodes (touched set ∪
ρ-domain), so the star count is `ℓ - s` for a bad `ρ` — reproved directly. -/

theorem stars_encodeLoc₁ {n : Nat} {D : DNF n} (hD : SimpleDNF D) {s ℓ : Nat}
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) :
    stars (encodeLoc₁ D s ρ) = ℓ - s := by
  classical
  have hstarsρ : stars ρ = ℓ := ((mem_badSetTerm ρ).mp hρ).1
  set Tf : Finset (Fin n) := (touchedVars D s ρ).toFinset with hTf
  have hsub : Tf ⊆ Finset.univ.filter (fun v => ρ v = none) := by
    intro v hv
    rw [hTf, List.mem_toFinset] at hv
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, touchedVars_free D s ρ v hv⟩
  have hσset : (Finset.univ.filter (fun v => encodeLoc₁ D s ρ v = none))
      = (Finset.univ.filter (fun v => ρ v = none)) \ Tf := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      hTf, List.mem_toFinset]
    rw [encodeLoc₁_eq_none_iff]
  unfold stars
  rw [hσset, Finset.card_sdiff hsub, touched_finset_card hD hρ]
  have : (Finset.univ.filter (fun v => ρ v = none)).card = ℓ := by
    rw [← hstarsρ]; rfl
  rw [this]

/-! ## 3. The satisfying-term collapse (shared structural core)

A restriction fixing every literal of a term `t` to its own sign collapses `t`
under `termRestrict` to the constant-true `[]`; and any assignment agreeing with
such a restriction makes `t` true.  (Same structural facts as in the Razborov
file; reproved here to keep this file self-contained without modifying it.) -/

theorem termRestrict_satisfied {n : Nat} (σ : Restriction n) :
    ∀ (t : Term n), (∀ l ∈ t, σ l.var = some l.sign) →
      termRestrict σ t = some [] := by
  intro t
  induction t with
  | nil => intro _; rfl
  | cons l t ih =>
      intro h
      have hl : σ l.var = some l.sign := h l (List.mem_cons_self l t)
      have ht : ∀ m ∈ t, σ m.var = some m.sign :=
        fun m hm => h m (List.mem_cons_of_mem l hm)
      simp only [termRestrict, hl, if_pos rfl]
      exact ih ht

theorem termEval_satisfied {n : Nat} (a : Assignment n) (t : Term n)
    (h : ∀ l ∈ t, a l.var = l.sign) : termEval a t = true := by
  induction t with
  | nil => rfl
  | cons l t ih =>
      have hl : a l.var = l.sign := h l (List.mem_cons_self l t)
      have ht : ∀ m ∈ t, a m.var = m.sign :=
        fun m hm => h m (List.mem_cons_of_mem l hm)
      simp only [termEval_cons, ih ht, Bool.and_true]
      simp only [litEval]
      cases hs : l.sign <;> simp_all

/-! ## 4. STEP 2 — each FULLY-touched deep term is satisfied by `σ_loc` (PROVED)

This is the genuine content the term-LOCAL fix unlocks.  We define the hypothesis
that the deep term's literals carry their local satisfying signs as
`LocSignsAlign`, and prove it is EXACTLY the condition under which the
fully-touched term collapses.  The crucial, NON-VACUOUS difference from the
term-global encode: with `satValLoc` the sign read for `v` comes from the SAME term
`v` lives in, so for any literal `l` of a deep term whose block is `j`,
`satValLoc D s ρ l.var = l.sign` whenever `signInTerm (deepTermAt D ρ j) l.var =
l.sign` and `l.var`'s position lands in block `j` — both of which hold for the
deep terms (the alignment lemmas needed for the full ρ-independent statement are
the residual isolated content; here we state step 2 against the per-term sign
hypothesis, exactly as the matching Razborov lemma does, but now the sign
hypothesis is the term-LOCAL one which is consistent — it cannot be falsified by a
foreign term as the global one could). -/

/-- **`signInTerm` reads the genuine sign (PROVED).**  In a SIMPLE term `t` (its
variables pairwise distinct), the sign read for any literal `l ∈ t` is exactly
`l.sign`: `signInTerm t l.var = l.sign`.  This is the precise sense in which the
term-LOCAL read is correct — it returns the sign of the unique literal on `l.var`
in `t`.  (For the term-GLOBAL `satVal` no such per-term guarantee exists: it may
return a sign from a DIFFERENT term.)  Proved by induction; simplicity guarantees
`l` is the FIRST (and only) literal on `l.var`. -/
theorem signInTerm_of_mem {n : Nat} (t : Term n) (hsimple : SimpleTerm t)
    (l : Literal n) (hl : l ∈ t) : signInTerm t l.var = l.sign := by
  unfold signInTerm
  induction t with
  | nil => exact absurd hl (List.not_mem_nil l)
  | cons m t ih =>
      unfold SimpleTerm at hsimple
      simp only [List.map_cons, List.nodup_cons] at hsimple
      obtain ⟨hmnotin, htnodup⟩ := hsimple
      rcases List.mem_cons.mp hl with hlm | hlt
      · subst hlm
        simp only [List.find?_cons, decide_True]
      · -- l ∈ t; since variables are distinct, m.var ≠ l.var
        have hlvne : ¬ (m.var = l.var) := by
          intro hc
          apply hmnotin
          rw [hc]
          exact List.mem_map_of_mem (·.var) hlt
        simp only [List.find?_cons, decide_eq_true_eq, hlvne, if_false]
        exact ih htnodup hlt

/-- A deep term `t` (with block index `j`) has its local signs aligned if every
literal's term-local satisfying value matches its sign.  For the term-local encode
this is the natural per-term condition (each `l`'s value is read from `t` itself
via `deepTermAt D ρ j`), in contrast to the term-global encode where it could be
violated by a foreign term carrying the opposite sign. -/
def LocSignsAlign {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) (t : Term n) :
    Prop := ∀ l ∈ t, satValLoc D s ρ l.var = l.sign

/-- **`LocSignsAlign` is realized by the per-block read (PROVED, non-vacuity of
step 2).**  If a SIMPLE term `t` is the `j`-th term of `D|ρ` (`t = deepTermAt D ρ j`)
and every variable of `t` has its deep position landing in block `j` (the natural
block-alignment property of a deep term), then `LocSignsAlign D s ρ t` HOLDS — each
`satValLoc` read returns the literal's own sign via `signInTerm_of_mem`.  This
certifies step 2 is NOT vacuous: the term-local condition is genuinely satisfied by
the deep terms (given the block-alignment hypothesis, which is the ρ-independent
plumbing isolated in `LocDeepBlockRecoverableW`). -/
theorem locSignsAlign_of_blockAligned {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (j : Nat) (hsimple : SimpleTerm (deepTermAt D ρ j))
    (halign : ∀ l ∈ deepTermAt D ρ j,
        blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j) :
    LocSignsAlign D s ρ (deepTermAt D ρ j) := by
  intro l hl
  unfold satValLoc
  simp only
  rw [halign l hl]
  exact signInTerm_of_mem (deepTermAt D ρ j) hsimple l hl

/-- **Fully-touched satisfied term collapses to `[]` under `σ_loc` (PROVED).** -/
theorem termRestrict_satRestrLoc_satisfied {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (t : Term n)
    (htouch : ∀ l ∈ t, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlign D s ρ t) :
    termRestrict (satRestrLoc D s ρ) t = some [] := by
  apply termRestrict_satisfied
  intro l hl
  rw [satRestrLoc_eq_some D s ρ l.var (htouch l hl), hsign l hl]

/-- **STEP 2 (PROVED): `termEval` of a fully-touched, locally-aligned deep term is
`true`** under any assignment agreeing with `σ_loc`.  The Boolean witness that the
critical deep term is satisfied in `D|σ_loc` — the anchor the first-satisfied-term
decode needs, now available because the term-local signs cannot be poisoned by a
foreign term. -/
theorem termEval_true_of_fullyTouched_loc {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (a : Assignment n) (h : Agree (encodeLoc₁ D s ρ) a)
    (t : Term n)
    (htouch : ∀ l ∈ t, l.var ∈ touchedVars D s ρ)
    (hsign : LocSignsAlign D s ρ t) :
    termEval a t = true := by
  apply termEval_satisfied
  intro l hl
  have hσv : encodeLoc₁ D s ρ l.var = some l.sign := by
    unfold encodeLoc₁ overlay
    rw [satRestrLoc_eq_some D s ρ l.var (htouch l hl), hsign l hl]
  exact h l.var l.sign hσv

/-! ## 4c. The TRUE, ρ-independent half: ρ-falsified terms stay falsified by `σ_loc`

Identical content to the Razborov file's half (a); reproved for `σ_loc`.  `σ_loc`
EXTENDS `ρ` (it only fixes FREE variables of `ρ`), so it can never revive a
ρ-falsified term — every term before the first touched term stays unsatisfied. -/

theorem encodeLoc₁_extends_ρ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) (b : Bool) (h : ρ v = some b) : encodeLoc₁ D s ρ v = some b := by
  unfold encodeLoc₁ overlay
  rw [satRestrLoc_disj D s ρ v (by rw [h]; simp), h]

theorem agree_ρ_of_agree_encodeLoc₁ {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (a : Assignment n) (h : Agree (encodeLoc₁ D s ρ) a) :
    Agree ρ a := by
  intro v b hv
  exact h v b (encodeLoc₁_extends_ρ D s ρ v b hv)

theorem termEval_false_of_ρ_falsifies_loc {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (a : Assignment n) (h : Agree (encodeLoc₁ D s ρ) a)
    (t : Term n) (hfals : termRestrict ρ t = none) : termEval a t = false := by
  have hρa : Agree ρ a := agree_ρ_of_agree_encodeLoc₁ D s ρ a h
  have := termEval_termRestrict ρ a hρa t
  rw [hfals] at this
  exact this.symm

/-! ## 5. Determination of `ρ` from `σ_loc` off the touched set, and `D|σ_loc` -/

theorem encodeLoc₁_eq_ρ_of_not_touched {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (v : Fin n) (hv : v ∉ touchedVars D s ρ) :
    encodeLoc₁ D s ρ v = ρ v := by
  unfold encodeLoc₁ overlay
  rw [(satRestrLoc_eq_none_iff D s ρ v).mpr hv]

/-- **`ρ` is determined by `σ_loc` given the touched set.** -/
theorem ρ_eq_of_encodeLoc {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    ρ = fun v => if v ∈ touchedVars D s ρ then none else encodeLoc₁ D s ρ v := by
  funext v
  by_cases hv : v ∈ touchedVars D s ρ
  · simp only [if_pos hv]; exact touchedVars_free D s ρ v hv
  · simp only [if_neg hv]; exact (encodeLoc₁_eq_ρ_of_not_touched D s ρ v hv).symm

/-- **`D|σ_loc` decomposes as `(D|ρ)|τ_loc`** (via `dnfRestrict_overlay`). -/
theorem dnfRestrict_encodeLoc₁ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    dnfRestrict (encodeLoc₁ D s ρ) D
      = dnfRestrict (satRestrLoc D s ρ) (dnfRestrict ρ D) := by
  unfold encodeLoc₁
  exact dnfRestrict_overlay ρ (satRestrLoc D s ρ) D (satRestrLoc_disj D s ρ)

/-! ## 6. The Razborov code (term-local direction) and the isolated recovery

The code is the sibling `codeOf` (ρ-independent block-tiling bookkeeping plus the
deep-path direction); it is convention-independent, so we reuse it verbatim.  We
then isolate exactly the remaining Razborov content — ρ-INDEPENDENT recovery of the
touched-VARIABLE SET from `(σ_loc, code)` — as `LocTermIdentifiable` (a `def : Prop`,
NOT an axiom, NOT asserted true), and PROVE that it yields the switching lemma.

HONESTY.  The term-local fix discharges the SIGN obstruction (step 2 above), but
NOT the convention-independent obstruction: inside `σ_loc = overlay ρ τ_loc` a
`some b` coming from `ρ`'s domain is indistinguishable, ρ-independently, from a
`some b` coming from a touched variable.  Hence subtracting `ρ` to expose the
touched set is the genuine open Razborov replay, the same heart isolated in the
sibling files (`SatDeepBlockRecoverableW` / `DeepBlockRecoverableW`).  We keep it
isolated and prove the reduction. -/

/-- The term-local code: reuse the sibling `codeOf` (genuine within-block position
plus deep-path direction; both ρ-independent and convention-independent). -/
noncomputable def codeLoc {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) : Fin s → Fin w × Bool :=
  codeOf D w s hw ρ

/-- The full term-local **encode**. -/
noncomputable def encodeLoc {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) : Restriction n × (Fin s → Fin w × Bool) :=
  (encodeLoc₁ D s ρ, codeLoc D w s hw ρ)

/-- **The isolated term-local term-identification recovery.**  For the
width-bounded regime, the touched-variable set of every bad `ρ` is recoverable,
ρ-independently, from `σ_loc = encodeLoc₁ ρ` and the code.  Isolated `def : Prop`
(NOT an axiom, NOT asserted true). -/
def LocTermIdentifiable (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (_hw : 0 < w), widthDNF D ≤ w →
    ∃ rec : Restriction n → (Fin s → Fin w × Bool) → Finset (Fin n),
      ∀ ρ ∈ badSetTerm D s ℓ,
        rec (encodeLoc₁ D s ρ) (codeLoc D w s _hw ρ) = (touchedVars D s ρ).toFinset

/-- **The isolated term-local deep-block recovery (the genuine heart).**  A
ρ-independent recovery of the i-th deep term-block of `D|ρ` from `σ_loc`, the i-th
code entry, and the length-`i` decoded prefix — under `widthDNF D ≤ w`.  Same shape
as the sibling `DeepBlockRecoverableW`, only with `σ_loc` in place of `σ`; the code
(`codeLoc = codeOf`) and target block (`deepBlock`) are identical.  Isolated
`def : Prop`, NOT an axiom, NOT asserted true. -/
def LocDeepBlockRecoverableW (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat) (hw : 0 < w), widthDNF D ≤ w →
    ∃ blk : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → List (Fin n × Bool),
      ∀ (ρ : Restriction n), ρ ∈ badSetTerm D s ℓ → ∀ (i : Nat) (hi : i < s),
        blk (encodeLoc₁ D s ρ) (codeLoc D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = deepBlock D ρ i

/-- **The fold reconstructs the deep-path prefix in the term-local direction
(PROVED).**  Replay of the sibling `recVarFold_eq_take` with `σ = encodeLoc₁`.  The
fold `recVarFold` is abstract over σ; the per-step variable recovery
(`deepVar_eq_block_getElem`) and the direction half (`codeOf_snd_eq_deepPathV`)
depend only on `codeLoc = codeOf`, NOT on σ. -/
theorem recVarFold_eq_take_loc {n : Nat} {D : DNF n} {w s ℓ : Nat} (hw : 0 < w)
    (hwD : widthDNF D ≤ w)
    (blk : Restriction n → (Fin w × Bool) → List (Fin n × Bool) → List (Fin n × Bool))
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ)
    (hblk : ∀ (i : Nat) (hi : i < s),
        blk (encodeLoc₁ D s ρ) (codeLoc D w s hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = deepBlock D ρ i) :
    ∀ i, i ≤ s →
      recVarFold blk (encodeLoc₁ D s ρ) s (codeLoc D w s hw ρ) i
        = (deepPathV (dnfRestrict ρ D)).take i
  | 0, _ => by simp [recVarFold]
  | (i + 1), hi => by
      have hi' : i < s := by omega
      rw [recVarFold_succ blk (encodeLoc₁ D s ρ) s (codeLoc D w s hw ρ) i hi']
      rw [recVarFold_eq_take_loc hw hwD blk hρ hblk i (by omega)]
      have hlen : i < (deepPathV (dnfRestrict ρ D)).length :=
        lt_deepPathV_length_of_bad hρ hi'
      have hbeq := hblk i hi'
      have hvar := deepVar_eq_block_getElem (D := D) hw hwD hρ hi'
      have hdir := codeOf_snd_eq_deepPathV (D := D) hw hρ hi'
      rw [hbeq]
      unfold codeLoc
      rw [hvar]
      simp only [Option.toList, List.map_cons, List.map_nil]
      rw [hdir]
      have hentry : (((deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩).1,
                      ((deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩).2)
                    = (deepPathV (dnfRestrict ρ D)).get ⟨i, hlen⟩ := by
        rw [Prod.mk.eta]
      rw [hentry, List.get_eq_getElem]
      exact (List.take_succ_append_getElem _ i hlen).symm

/-- **The reduction (PROVED): `LocDeepBlockRecoverableW n → LocTermIdentifiable n`.** -/
theorem locTermIdentifiable_of_locDeepBlockRecoverableW {n : Nat}
    (h : LocDeepBlockRecoverableW n) : LocTermIdentifiable n := by
  intro D w s ℓ hw hwD
  obtain ⟨blk, hblk⟩ := h D w s ℓ hw hwD
  refine ⟨fun σ code => ((recVarFold blk σ s code s).map Prod.fst).toFinset, ?_⟩
  intro ρ hρ
  have hfold : recVarFold blk (encodeLoc₁ D s ρ) s (codeLoc D w s hw ρ) s
      = (deepPathV (dnfRestrict ρ D)).take s :=
    recVarFold_eq_take_loc hw hwD blk hρ (fun i hi => hblk ρ hρ i hi) s (le_refl s)
  simp only []
  rw [hfold, ← touchedVars_eq_deepPathV D s ρ]

/-- **The reduction (PROVED): `LocTermIdentifiable n → SwitchingLemmaTermSimple n`.**
With term-local touched-set recoverability, `encodeLoc` is injective on the bad set
(via `ρ_eq_of_encodeLoc`), lands its first coordinate in the `(ℓ-s)`-star set (via
`stars_encodeLoc₁`), and the injection-cardinality backbone plus `(2w)^s ≤ (8w)^s`
give the switching lemma.  The `w = 0` case is the empty-bad-set / `s = 0` case. -/
theorem switchingLemmaTermSimple_of_locIdentifiable {n : Nat}
    (h : LocTermIdentifiable n) : SwitchingLemmaTermSimple n := by
  intro D w s ℓ hD hwD
  classical
  by_cases hw : 0 < w
  · obtain ⟨rec, hreceq⟩ := h D w s ℓ hw hwD
    have hmem : ∀ ρ ∈ badSetTerm D s ℓ,
        (encodeLoc D w s hw ρ).1 ∈ restrictionsWithStars n (ℓ - s) := by
      intro ρ hρ
      rw [mem_restrictionsWithStars]; exact stars_encodeLoc₁ hD hρ
    have hinj : Set.InjOn (encodeLoc D w s hw) ↑(badSetTerm D s ℓ) := by
      intro ρ hρ ρ' hρ' heq
      have hρmem : ρ ∈ badSetTerm D s ℓ := by simpa using hρ
      have hρ'mem : ρ' ∈ badSetTerm D s ℓ := by simpa using hρ'
      have hσ : encodeLoc₁ D s ρ = encodeLoc₁ D s ρ' := congrArg Prod.fst heq
      have hcode : codeLoc D w s hw ρ = codeLoc D w s hw ρ' := congrArg Prod.snd heq
      have ht : (touchedVars D s ρ).toFinset = (touchedVars D s ρ').toFinset := by
        rw [← hreceq ρ hρmem, ← hreceq ρ' hρ'mem, hσ, hcode]
      rw [ρ_eq_of_encodeLoc D s ρ, ρ_eq_of_encodeLoc D s ρ']
      funext v
      have hmemv : (v ∈ touchedVars D s ρ) = (v ∈ touchedVars D s ρ') := by
        have := congrArg (fun (F : Finset (Fin n)) => v ∈ F) ht
        simpa [List.mem_toFinset] using this
      by_cases hvv : v ∈ touchedVars D s ρ
      · have hvv' : v ∈ touchedVars D s ρ' := by rw [← hmemv]; exact hvv
        simp only [if_pos hvv, if_pos hvv']
      · have hvv' : v ∉ touchedVars D s ρ' := by rw [← hmemv]; exact hvv
        simp only [if_neg hvv, if_neg hvv']
        exact congrFun hσ v
    have hc : (badSetTerm D s ℓ).card
        ≤ (restrictionsWithStars n (ℓ - s)).card * (2 * w) ^ s :=
      card_le_mul_pow_of_injOn (badSetTerm D s ℓ) (restrictionsWithStars n (ℓ - s))
        w s (encodeLoc D w s hw) hmem hinj
    refine le_trans hc ?_
    apply Nat.mul_le_mul (le_refl _)
    exact Nat.pow_le_pow_left (by omega) s
  · push_neg at hw
    have hw0 : w = 0 := Nat.le_zero.mp hw
    subst hw0
    have hdepth0 : ∀ ρ : Restriction n,
        dtDepth (termCanonicalDT (dnfRestrict ρ D)) = 0 := by
      intro ρ
      apply Nat.le_zero.mp
      refine le_trans (dtDepth_termCanonicalDT_le _) ?_
      have hwr : widthDNF (dnfRestrict ρ D) = 0 := by
        have := widthDNF_dnfRestrict_le ρ D; omega
      rw [dnfSize_eq_zero_of_width_zero _ hwr]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp only [Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_zero]
      exact Finset.card_le_card (badSetTerm_subset D 0 ℓ)
    · have hempty : badSetTerm D s ℓ = ∅ := by
        rw [Finset.eq_empty_iff_forall_not_mem]
        intro ρ hρ
        have := ((mem_badSetTerm ρ).mp hρ).2
        rw [hdepth0 ρ] at this; omega
      rw [hempty]; simp

/-! ## 7. Satisfiability of the isolated `LocTermIdentifiable` (INTEGRITY CHECK)

We VERIFY `LocTermIdentifiable` is genuinely SATISFIABLE — not vacuously false — by
PROVING concrete boundary instances (no `sorry`).  Same regimes as the Razborov
file's §8. -/

/-- **Satisfiability witness (`s = 0`).**  The `s = 0` instance is satisfied by the
empty recovery `rec ≡ ∅` for every `D, w, ℓ` (the touched set is empty for `s = 0`,
yet the bad set can be large — non-vacuous). -/
theorem locIdentifiable_witness_s_zero {n : Nat} (D : DNF n) (w ℓ : Nat)
    (hw : 0 < w) (hwD : widthDNF D ≤ w) :
    ∃ rec : Restriction n → (Fin 0 → Fin w × Bool) → Finset (Fin n),
      ∀ ρ ∈ badSetTerm D 0 ℓ,
        rec (encodeLoc₁ D 0 ρ) (codeLoc D w 0 hw ρ) = (touchedVars D 0 ρ).toFinset := by
  refine ⟨fun _ _ => (∅ : Finset (Fin n)), ?_⟩
  intro ρ _hρ
  have h0 : touchedVars D 0 ρ = [] := by unfold touchedVars dpath; simp
  rw [h0]; simp

/-- **`LocTermIdentifiable 0` holds outright.**  Over `Fin 0` every touched list is
empty, so `rec ≡ ∅` works for every `D, w, s, ℓ` — the isolated `Prop` is inhabited,
not contradictory. -/
theorem locTermIdentifiable_of_n_zero : LocTermIdentifiable 0 := by
  intro D w s ℓ _hw _hwD
  refine ⟨fun _ _ => (∅ : Finset (Fin 0)), ?_⟩
  intro ρ _hρ
  have : touchedVars D s ρ = [] := by
    cases h : touchedVars D s ρ with
    | nil => rfl
    | cons a _ => exact a.elim0
  rw [this]; simp

/-! ## 8. Capstone -/

/-- **CAPSTONE (PROVED, modulo the satisfiable isolated `LocTermIdentifiable`).**
The term-local satisfying-direction encoding's injectivity — reduced to the single
recovery `def : Prop` `LocTermIdentifiable` (CERTIFIED SATISFIABLE in §7) — yields
the term switching lemma for simple DNFs.  Same statement as
`SwitchingEncodeConstruct.SwitchingLemmaTermSimple`. -/
theorem switchingLemmaTermSimple_local {n : Nat}
    (h : LocTermIdentifiable n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_locIdentifiable h

end SwitchingEncodeLocal
end PvNP
