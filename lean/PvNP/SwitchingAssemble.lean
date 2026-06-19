/-
# Assembling the two PROVED order halves into the per-step decode identification

This file carries out the ASSEMBLY the task names: combine the two now-proved halves of
the order argument —

* HALF 1 (prefix falsification): a D-original term whose ρ-restriction is killed by the
  accumulated first-`j`-block deep directions (`accumDir (D|ρ) j`) is FALSIFIED under the
  evolving decoder state (`SwitchingOrder.accumDir_killed_falsified_stateAt`);
* HALF 2 (j-th term collapses): the j-th ENTERED term collapses to `some []` under the
  evolving state (`SwitchingEnteredOrder.termRestrict_stateAt_encodeEnt₁_satisfied`),

into the per-step identification of the D-ORIGINAL scan `firstNonFalsified`, by an
induction on the step `j`.

## What this file PROVES OUTRIGHT (axioms ⊆ [propext, Classical.choice, Quot.sound])

The genuine new content is the COMPLETENESS lemma and the per-step term identification
on the EVOLVING state, assembled ρ-DEPENDENTLY:

* `accumDir_killed_falsified_stateAt_ent` — `encodeEnt₁` analogue of HALF 1; the prefix
  falsification proof is generic over the base σ, so it transports verbatim from
  `encodeLoc₁` to `encodeEnt₁`.
* `residualIter_eq_dnfRestrict_combRestr` — the residual after `j` blocks is `D` ORIGINAL
  restricted by the combined `overlay ρ (accumDir (D|ρ) j)`, an ORDER-PRESERVING filter
  of `D`.
* `combRestr_killed_falsified_stateAt` (**COMPLETENESS, PROVED**) — every D-original term
  killed by the combined restriction is FALSIFIED under the evolving state: ρ-killed ones
  by §4, accumDir-killed ρ-survivors by HALF 1 (§1).
* `enteredTerm_block_aligned` / `_head` (**discharges `halign`, PROVED**) — the j-th
  entered term's variables have deep BLOCK NUMBER `j` (it is the head deep block of
  `residualIter (D|ρ) j`, a contiguous slice of the nodup deep path).  This was an OPEN
  hypothesis of `SwitchingEnteredOrder.enteredTerm_collapse`.
* `survivor_ne_none_stateAt` (**survivor not falsified, PROVED**) — the first
  combRestr-survivor `C₀` (mapping to the residual head = `enteredTerm D ρ j`) is NOT
  falsified under the evolving state; no literal of `C₀` is fixed against its sign (the
  ρ-fixed and accumDir-fixed literals agree with the prefix/encode; the entered-term free
  literals are
  fixed to `satValEnt = signInTerm(enteredTerm) = their own sign` via the discharged
  block-alignment, or left free).
* `firstNonFalsified_eq_survivor` (**THE PER-STEP TERM IDENTIFICATION, PROVED,
  unconditional at a block boundary**): for any `j` with `residualIter (D|ρ) j = Cr ::
  rest'`, `D` ORIGINAL factors as `pre ++ C₀ :: restD`, the D-original scan
  `firstNonFalsified D (stateAt (encodeEnt₁ …) prev_j) = some C₀`, and
  `termRestrict (combRestr D ρ j) C₀ = some Cr`.  HALF 1 + ρ-killed (completeness) falsify
  every earlier term; HALF 2 (via the survivor lemma) keeps `C₀` alive.

## What does NOT close (the EXACT obstructions — NOT faked, NOT a dodging def)

The per-step identification recovers, ρ-independently, the ORIGINAL term `C₀` at the
j-th entered position.  TWO precise gaps remain to `RCodeRecoverable` /
`SwitchingLemmaTermSimple`, both already isolated (unchanged) in the sibling files:

(G1) THE COLUMN READ (Wall A).  `DOrigStepData` (and `RCodeBlockStepVar`) require reading
the j-th deep VARIABLE off `C₀` as `colVar C₀ codeColumn = (C₀.map var)[codeColumn]?`.  But
the code column indexes the deep BLOCK (deep-path order of `D|ρ` = `Cr = enteredTerm`'s var
order), whereas `C₀` is the original term with the ρ-fixed literals RE-INSERTED in their
ORIGINAL positions (`termRestrict ρ C₀ = some (… Cr …)`), shifting the column.  The decoder
is ρ-independent and has only `C₀` (not `Cr`, which needs `ρ`).  This is exactly
`SwitchingDOrig.colVar_orig_eq_iff_column_agree`'s column-agreement wall — NOT generally
true, NOT asserted here.

(G2) BLOCK-BOUNDARY vs MID-BLOCK PREFIX.  `firstNonFalsified_eq_survivor` is stated at a
BLOCK boundary (prefix `take (start j)`, `j` a block NUMBER).  The reductions
(`DOrigStepData`, `RCodeBlockStepVar`) recover the i-th deep POSITION via the prefix
`take i` (`i` a deep-path index, possibly MID-block).  Bridging mid-block prefixes
(`take (start j + k)`) to the block-boundary order argument is the remaining list-order /
deep-order alignment — the same residual content noted (iii) in
`SwitchingStateDecode`'s honesty note.

We do NOT fake either gap.  Everything above (HALF-1-ent, completeness, the `halign`
discharge, the survivor non-falsification, and the unconditional per-step term
identification at a block boundary) is PROVED outright with axioms ⊆ `[propext,
Classical.choice, Quot.sound]`.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  NOT a lower
bound, NOT P≠NP.  Imported files are untouched.
-/
import PvNP.SwitchingDOrig
import PvNP.SwitchingEnteredOrder

namespace PvNP
namespace SwitchingAssemble

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
open SwitchingEnteredOrder
open SwitchingRazborovCode
open Classical

/-! ## 1. HALF 1 for the entered-order encode `encodeEnt₁`

`SwitchingOrder.accumDir_killed_falsified_stateAt` is stated for `encodeLoc₁`, but its
proof only uses that the offending literal is fixed AGAINST its sign by `prefixRestr` of
the recorded prefix — generic over the BASE restriction the prefix is overlaid onto.  We
transport it to `encodeEnt₁` (the encode HALF 2's collapse is proved for). -/

/-- **HALF 1 for `encodeEnt₁` (PROVED).**  A D-original term `C₀` whose ρ-restriction
`Cr` is FALSIFIED by the accumulated first-`j`-block deep directions is FALSIFIED under
the evolving state `stateAt (encodeEnt₁ D s ρ) ((deepPathV (D|ρ)).take (start j))`.
Identical proof shape to `accumDir_killed_falsified_stateAt`, with `encodeEnt₁` as the
base σ. -/
theorem accumDir_killed_falsified_stateAt_ent {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (hD : SimpleDNF D) (j : Nat)
    (C₀ Cr : Term n) (hres : termRestrict ρ C₀ = some Cr)
    (hkill : termRestrict (accumDir (dnfRestrict ρ D) j) Cr = none) :
    termRestrict (stateAt (encodeEnt₁ D s ρ)
        ((deepPathV (dnfRestrict ρ D)).take
          (startLen (deepBlockLens (dnfRestrict ρ D)) j)) ) C₀ = none := by
  set E := dnfRestrict ρ D
  have hEsimp : SimpleDNF E := simpleDNF_dnfRestrict hD ρ
  obtain ⟨l, hlCr, c, hc, hcs⟩ :=
    SwitchingStepData.termRestrict_none_witness (accumDir E j) Cr hkill
  have hlC0 : l ∈ C₀ := termRestrict_mem_of_mem ρ C₀ Cr hres l hlCr
  have hacc_ne : accumDir E j l.var ≠ none := by rw [hc]; simp
  have hpref : prefixRestr ((deepPathV E).take (startLen (deepBlockLens E) j)) l.var
      = some c := by
    rw [prefixRestr_take_eq_accumDir E hEsimp j l.var hacc_ne]; exact hc
  rw [stateAt]
  exact termRestrict_overlay_none_of_lit (encodeEnt₁ D s ρ)
    ((deepPathV E).take (startLen (deepBlockLens E) j)) C₀ l hlC0 c hpref hcs

/-! ## 2. The residual after `j` blocks is `D` ORIGINAL filtered by a combined restriction

`SwitchingOrder.residualIter_eq_dnfRestrict_accumDir` gives `residualIter (D|ρ) j =
dnfRestrict (accumDir (D|ρ) j) (D|ρ)`.  Composing with `dnfRestrict ρ D = D|ρ` and the
disjointness of `accumDir`'s domain from `ρ`'s, this is `dnfRestrict (overlay ρ accumDir)
D` — an ORDER-PRESERVING filterMap of `D` ORIGINAL.  This is the lever for the
completeness step: the FIRST surviving D-original term maps to the residual HEAD, and all
earlier ones are filtered out (killed by the combined restriction). -/

/-- The combined first-`j`-block restriction on `D` ORIGINAL: `ρ` overlaid with the
accumulated deep directions of the first `j` blocks of `D|ρ`. -/
noncomputable def combRestr {n : Nat} (D : DNF n) (ρ : Restriction n) (j : Nat) :
    Restriction n :=
  overlay ρ (accumDir (dnfRestrict ρ D) j)

/-- `accumDir (D|ρ) j` is disjoint from `ρ`'s domain: it fixes only variables of `D|ρ`'s
deep blocks, which are FREE in `ρ` (literals of `dnfRestrict ρ D` are on ρ-free vars). -/
theorem accumDir_disj_ρ {n : Nat} (D : DNF n) (ρ : Restriction n) (hD : SimpleDNF D)
    (j : Nat) : ∀ v, ρ v ≠ none → accumDir (dnfRestrict ρ D) j v = none := by
  intro v hv
  by_contra hne
  -- accumDir fixes only vars of D|ρ's residual head terms, which are ρ-free.  Reuse the
  -- proved support membership: such a v lies in deepPathV (D|ρ), whose vars are ρ-free.
  have hmem : v ∈ (deepPathV (dnfRestrict ρ D)).map Prod.fst :=
    accumDir_some_mem_deepPathV (dnfRestrict ρ D) (simpleDNF_dnfRestrict hD ρ) j v hne
  -- every variable of deepPathV (D|ρ) is touched, hence ρ-free.  Use touchedVars link.
  rw [List.mem_map] at hmem
  obtain ⟨vd, hvd, hvdv⟩ := hmem
  -- vd ∈ deepPathV (D|ρ) = deepestPath (termCanonicalDT (D|ρ)); its var is ρ-free
  rw [deepPathV_eq] at hvd
  have := deepestPath_var_free ρ D vd hvd
  rw [hvdv] at this
  exact hv this

/-- **Residual after `j` blocks = `D` ORIGINAL filtered by `combRestr` (PROVED).** -/
theorem residualIter_eq_dnfRestrict_combRestr {n : Nat} (D : DNF n) (ρ : Restriction n)
    (hD : SimpleDNF D) (j : Nat) :
    residualIter (dnfRestrict ρ D) j = dnfRestrict (combRestr D ρ j) D := by
  rw [residualIter_eq_dnfRestrict_accumDir j (simpleDNF_dnfRestrict hD ρ)]
  unfold combRestr
  rw [dnfRestrict_overlay ρ (accumDir (dnfRestrict ρ D) j) D (accumDir_disj_ρ D ρ hD j)]

/-! ## 3. The filterMap head factorization (pure list lemma)

`dnfRestrict P D = List.filterMap (termRestrict P) D`.  When this filtered list is
nonempty with head `y`, `D` ORIGINAL factors as `pre ++ C₀ :: rest` with `pre` all
`P`-killed (`termRestrict P = none`) and `C₀` the first `P`-survivor mapping to `y`.  This
is the precise list-order link the completeness step needs. -/

/-- **filterMap head factorization (PROVED, pure list lemma).**  If
`(L.filterMap f) = y :: ys` then `L = pre ++ x :: rest` with `f x = some y` and every
element of `pre` mapping to `none`.  By induction on `L`. -/
theorem filterMap_head_factor {α β : Type*} (f : α → Option β) :
    ∀ (L : List α) (y : β) (ys : List β), L.filterMap f = y :: ys →
      ∃ (pre : List α) (x : α) (rest : List α),
        L = pre ++ x :: rest ∧ f x = some y ∧ ∀ p ∈ pre, f p = none
  | [], y, ys, h => by simp [List.filterMap_nil] at h
  | a :: as, y, ys, h => by
      rw [List.filterMap_cons] at h
      cases hfa : f a with
      | none =>
          rw [hfa] at h
          obtain ⟨pre, x, rest, hL, hfx, hpre⟩ := filterMap_head_factor f as y ys h
          refine ⟨a :: pre, x, rest, ?_, hfx, ?_⟩
          · rw [hL, List.cons_append]
          · intro p hp
            rcases List.mem_cons.mp hp with hpa | hppre
            · subst hpa; exact hfa
            · exact hpre p hppre
      | some b =>
          rw [hfa] at h
          simp only [List.cons.injEq] at h
          obtain ⟨hby, _⟩ := h
          subst hby
          exact ⟨[], a, as, by simp, hfa, by simp⟩

/-! ## 4. The ρ-killed prefix half for `encodeEnt₁`

A ρ-FALSIFIED original term stays falsified under the evolving `encodeEnt₁`-state.  Same
generic content as `SwitchingDOrig.orig_ρ_killed_none_stateAt`, transported to
`encodeEnt₁` (the proof is generic over the base σ via `termRestrict_overlay`). -/

/-- A ρ-FALSIFIED original term of `D` is FALSIFIED under the evolving `encodeEnt₁`-state
on a DEEP prefix `(deepPathV (D|ρ)).take i`.  `encodeEnt₁` extends `ρ` so it cannot revive
a ρ-killed term; the offending literal sits on a ρ-fixed (hence deep-prefix-free) variable,
so the overlay preserves the falsification. -/
theorem orig_ρ_killed_none_stateAt_ent {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (i : Nat) (C : Term n) (h : termRestrict ρ C = none) :
    termRestrict (stateAt (encodeEnt₁ D s ρ) ((deepPathV (dnfRestrict ρ D)).take i)) C
      = none := by
  obtain ⟨l, hl, c, hc, hcs⟩ := SwitchingStepData.termRestrict_none_witness ρ C h
  have hσ : encodeEnt₁ D s ρ l.var = some c := encodeEnt₁_extends_ρ D s ρ l.var c hc
  have hpref : prefixRestr ((deepPathV (dnfRestrict ρ D)).take i) l.var = none :=
    SwitchingStepData.prefixRestr_take_none_of_ρ_fixed D ρ i l.var c hc
  rw [stateAt]
  apply SwitchingStepData.termRestrict_none_of_lit_fixed _ C l hl c _ hcs
  rw [overlay_eq_ρ_of_τ_none _ _ _ hpref]; exact hσ

/-! ## 5. COMPLETENESS: every `combRestr`-killed D-original term is falsified under `stateAt`

A D-original term killed by `combRestr D ρ j = overlay ρ (accumDir (D|ρ) j)` is killed by
exactly one of the two halves: ρ-killed (`termRestrict ρ p = none`) — handled by §4 — or
ρ-survives but accumDir-killed (`termRestrict ρ p = some Cr`, `termRestrict accumDir Cr =
none`) — handled by HALF 1 (§1).  We assemble both into ONE statement. -/

/-- **COMPLETENESS (PROVED).**  Any D-original term `p` killed by `combRestr D ρ j` is
FALSIFIED under the evolving state `stateAt (encodeEnt₁ D s ρ) prev_j`
(`prev_j = (deepPathV (D|ρ)).take (start j)`).  Split via `termRestrict_overlay`:
ρ-killed terms by `orig_ρ_killed_none_stateAt_ent`; accumDir-killed ρ-survivors by
`accumDir_killed_falsified_stateAt_ent` (HALF 1). -/
theorem combRestr_killed_falsified_stateAt {n : Nat} (D : DNF n) (s : Nat)
    (ρ : Restriction n) (hD : SimpleDNF D) (j : Nat) (p : Term n)
    (hkill : termRestrict (combRestr D ρ j) p = none) :
    termRestrict (stateAt (encodeEnt₁ D s ρ)
        ((deepPathV (dnfRestrict ρ D)).take
          (startLen (deepBlockLens (dnfRestrict ρ D)) j))) p = none := by
  -- combRestr = overlay ρ accumDir; decompose via termRestrict_overlay
  have hov : termRestrict (combRestr D ρ j) p
      = (termRestrict ρ p).bind (termRestrict (accumDir (dnfRestrict ρ D) j)) := by
    unfold combRestr
    exact termRestrict_overlay ρ (accumDir (dnfRestrict ρ D) j) p (accumDir_disj_ρ D ρ hD j)
  rw [hov] at hkill
  cases hρp : termRestrict ρ p with
  | none =>
      -- ρ-killed
      exact orig_ρ_killed_none_stateAt_ent D s ρ
        (startLen (deepBlockLens (dnfRestrict ρ D)) j) p hρp
  | some Cr =>
      -- ρ-survives to Cr, but accumDir kills Cr ⇒ HALF 1
      rw [hρp] at hkill
      simp only [Option.bind] at hkill
      exact accumDir_killed_falsified_stateAt_ent D s ρ hD j p Cr hρp hkill

/-! ## 6. The survivor is NOT falsified: a term no literal of which is fixed against its
sign survives `termRestrict`

A clean induction: if no literal of `t` is fixed AGAINST its sign by `μ`, then
`termRestrict μ t ≠ none`.  This is the converse direction the per-step identification
needs for the j-th entered term's ORIGINAL term `C₀`. -/

/-- **Survival criterion (PROVED).**  If for every literal `l ∈ t`, `μ l.var` is NOT
`some (¬l.sign)` (i.e. either free or fixed TO `l.sign`), then `termRestrict μ t ≠ none`.
Induction on `t`. -/
theorem termRestrict_ne_none_of_no_conflict {n : Nat} (μ : Restriction n) :
    ∀ (t : Term n), (∀ l ∈ t, ∀ c, μ l.var = some c → c = l.sign) →
      termRestrict μ t ≠ none := by
  intro t
  induction t with
  | nil => intro _; simp [termRestrict]
  | cons m t ih =>
      intro h
      have ht : ∀ l ∈ t, ∀ c, μ l.var = some c → c = l.sign :=
        fun l hl c hc => h l (List.mem_cons_of_mem m hl) c hc
      rw [termRestrict]
      cases hμ : μ m.var with
      | none =>
          cases hr : termRestrict μ t with
          | none => exact absurd hr (ih ht)
          | some t' => simp only [Option.ne_none_iff_isSome, Option.isSome_some]
      | some b =>
          have hb : b = m.sign := h m (List.mem_cons_self m t) b hμ
          simp only [if_pos hb]; exact ih ht

/-- **Free literals of a survivor land in the restriction (PROVED).**  If
`termRestrict μ C₀ = some Cr` and `l ∈ C₀` with `μ l.var = none` (free), then `l ∈ Cr` —
`termRestrict` keeps free literals verbatim.  Induction on `C₀`. -/
theorem mem_termRestrict_of_free {n : Nat} (μ : Restriction n) :
    ∀ (C₀ Cr : Term n), termRestrict μ C₀ = some Cr → ∀ l ∈ C₀, μ l.var = none → l ∈ Cr
  | [], Cr, _, l, hl, _ => by exact absurd hl (List.not_mem_nil l)
  | m :: t, Cr, h, l, hl, hfree => by
      simp only [termRestrict] at h
      cases hμm : μ m.var with
      | none =>
          rw [hμm] at h
          cases hr : termRestrict μ t with
          | none => rw [hr] at h; simp at h
          | some t' =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hl with hlm | hlt
              · subst hlm; exact List.mem_cons_self _ _
              · exact List.mem_cons_of_mem m (mem_termRestrict_of_free μ t t' hr l hlt hfree)
      | some b =>
          rw [hμm] at h
          by_cases hb : b = m.sign
          · simp only [if_pos hb] at h
            rcases List.mem_cons.mp hl with hlm | hlt
            · -- l = m but μ l.var = some b ≠ none contradicts hfree
              subst hlm; rw [hμm] at hfree; exact absurd hfree (by simp)
            · exact mem_termRestrict_of_free μ t Cr h l hlt hfree
          · simp only [if_neg hb] at h; simp at h

/-! ## 6b. Block-alignment of the entered term (discharging `halign` for general `j`)

The j-th entered term's variables have deep BLOCK NUMBER `j`.  This is the `halign`
hypothesis left undischarged by `SwitchingEnteredOrder.enteredTerm_collapse`.  We prove it
from the deep-path tiling: the entered term IS the j-th deep block by number
(`deepResidual_head`), so its variables sit at deep positions in `[start j, start (j+1))`,
whose block index is `j`.  Two ingredients: an arithmetic block-index lemma, and the
position identification via deep-path nodup. -/

/-- **Block-index arithmetic (PROVED).**  For a deep position `p` in the j-th block
range `[startLen bs j, startLen bs j + (bs.drop j).headI)` with `j < bs.length`,
`blockIndexOfIndex bs p = j`.  Induction on `bs` and `j`. -/
theorem blockIndexOfIndex_eq_of_range :
    ∀ (bs : List Nat) (j p : Nat), j < bs.length →
      startLen bs j ≤ p → p < startLen bs j + (bs.drop j).headI →
        blockIndexOfIndex bs p = j
  | [], j, p, hj, _, _ => by simp at hj
  | b :: bs, 0, p, _, hlo, hhi => by
      simp only [startLen, List.drop_zero, List.headI, Nat.zero_add] at hlo hhi
      rw [blockIndexOfIndex]
      simp only [if_pos hhi]
  | b :: bs, (j + 1), p, hj, hlo, hhi => by
      simp only [startLen, List.drop_succ_cons] at hlo hhi
      simp only [List.length_cons] at hj
      have hjb : j < bs.length := by omega
      -- p ≥ b + startLen bs j ≥ b, so not in head block
      have hpb : ¬ p < b := by omega
      rw [blockIndexOfIndex]
      simp only [if_neg hpb]
      have hlo' : startLen bs j ≤ p - b := by omega
      have hhi' : p - b < startLen bs j + (bs.drop j).headI := by omega
      rw [blockIndexOfIndex_eq_of_range bs j (p - b) hjb hlo' hhi']
      omega

/-- **`dirRestrQ` fixes every variable of `vars` (PROVED).**  If `x ∈ vars.map var` then
`dirRestrQ vars D x ≠ none`.  Induction mirroring `dirRestrQ`: the head literal is fixed
by its `single`; tail variables by the recursive `dirRestrQ` (overlay preserves both). -/
theorem dirRestrQ_ne_none_of_mem {n : Nat} :
    ∀ (vars : Term n) (D : DNF n) (x : Fin n),
      x ∈ vars.map (·.var) → dirRestrQ vars D x ≠ none
  | [], _, x, hx => by simp at hx
  | l :: vs, D, x, hx => by
      simp only [List.map_cons, List.mem_cons] at hx
      rw [dirRestrQ]
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · simp only [if_pos h]
        rcases hx with hxl | hxvs
        · -- x = l.var: overlay of (single l.var true) — τ wins if defined else single
          subst hxl
          cases hd : dirRestrQ vs (assignVar l.var true D) l.var with
          | some b => rw [overlay_eq_some_of_τ _ _ _ b hd]; simp
          | none => rw [overlay_eq_ρ_of_τ_none _ _ _ hd]; unfold single; simp
        · -- x ∈ vs vars: recursive dirRestrQ fixes it
          have hrec := dirRestrQ_ne_none_of_mem vs (assignVar l.var true D) x hxvs
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hrec
          rw [overlay_eq_some_of_τ _ _ _ b hb]; simp
      · simp only [if_neg h]
        rcases hx with hxl | hxvs
        · subst hxl
          cases hd : dirRestrQ vs (assignVar l.var false D) l.var with
          | some b => rw [overlay_eq_some_of_τ _ _ _ b hd]; simp
          | none => rw [overlay_eq_ρ_of_τ_none _ _ _ hd]; unfold single; simp
        · have hrec := dirRestrQ_ne_none_of_mem vs (assignVar l.var false D) x hxvs
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hrec
          rw [overlay_eq_some_of_τ _ _ _ b hb]; simp
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)

/-- A variable of the head term `l0 :: t0` is fixed by `dirRestrBlock ((l0::t0)::Ds)`. -/
theorem dirRestrBlock_mem_of_head {n : Nat} (l0 : Literal n) (t0 : Term n) (Ds : DNF n)
    (x : Fin n) (hx : x ∈ (l0 :: t0).map (·.var)) :
    dirRestrBlock ((l0 :: t0) :: Ds) x ≠ none := by
  rw [dirRestrBlock]
  simp only [List.map_cons, List.mem_cons] at hx
  by_cases hcmp : dtDepth (queryTerm t0 (assignVar l0.var false ((l0 :: t0) :: Ds)))
      ≤ dtDepth (queryTerm t0 (assignVar l0.var true ((l0 :: t0) :: Ds)))
  · simp only [if_pos hcmp]
    rcases hx with hxl0 | hxt0
    · subst hxl0
      cases hd : dirRestrQ t0 (assignVar l0.var true ((l0 :: t0) :: Ds)) l0.var with
      | some b => rw [overlay_eq_some_of_τ _ _ _ b hd]; simp
      | none => rw [overlay_eq_ρ_of_τ_none _ _ _ hd]; unfold single; simp
    · have hrec := dirRestrQ_ne_none_of_mem t0 (assignVar l0.var true ((l0 :: t0) :: Ds)) x
          (by simpa using hxt0)
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hrec
      rw [overlay_eq_some_of_τ _ _ _ b hb]; simp
  · simp only [if_neg hcmp]
    rcases hx with hxl0 | hxt0
    · subst hxl0
      cases hd : dirRestrQ t0 (assignVar l0.var false ((l0 :: t0) :: Ds)) l0.var with
      | some b => rw [overlay_eq_some_of_τ _ _ _ b hd]; simp
      | none => rw [overlay_eq_ρ_of_τ_none _ _ _ hd]; unfold single; simp
    · have hrec := dirRestrQ_ne_none_of_mem t0 (assignVar l0.var false ((l0 :: t0) :: Ds)) x
          (by simpa using hxt0)
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hrec
      rw [overlay_eq_some_of_τ _ _ _ b hb]; simp

/-- **Converse support bridge (PROVED): a prefix-`take` variable is accumDir-fixed.**  If
`x` is among the variables of `(deepPathV E).take (startLen bs j)` (the first `j` blocks),
then `accumDir E j x ≠ none`.  Induction on `j`, peeling the j-th block: earlier-block
vars are accumDir-`j`-fixed (overlay monotone); the j-th block's vars are fixed by
`dirRestrBlock (residualIter E j)`.  The exact converse of `accumDir_mem_take_startLen`. -/
theorem accumDir_ne_none_of_mem_take {n : Nat} (E : DNF n) (_hE : SimpleDNF E) :
    ∀ (j : Nat) (x : Fin n),
      x ∈ ((deepPathV E).take (startLen (deepBlockLens E) j)).map Prod.fst →
        accumDir E j x ≠ none := by
  intro j
  induction j with
  | zero => intro x hx; simp only [startLen, List.take_zero, List.map_nil] at hx;
            exact absurd hx (List.not_mem_nil x)
  | succ j ih =>
      intro x hx
      -- split take (start (j+1)) into take (start j) ++ block j
      have hsl : startLen (deepBlockLens E) (j + 1)
          = startLen (deepBlockLens E) j + (deepBlockLens (residualIter E j)).headI := by
        rw [startLen_succ_eq, deepBlockLens_residualIter]
      rw [hsl] at hx
      -- x ∈ map fst (take (a+b) L) = map fst (take a L ++ take b (drop a L))
      rw [List.map_take] at hx
      have hsplit : (List.map Prod.fst (deepPathV E)).take
            (startLen (deepBlockLens E) j + (deepBlockLens (residualIter E j)).headI)
          = (List.map Prod.fst (deepPathV E)).take (startLen (deepBlockLens E) j)
            ++ ((List.map Prod.fst (deepPathV E)).drop
                (startLen (deepBlockLens E) j)).take
                (deepBlockLens (residualIter E j)).headI :=
        List.take_add _ _ _
      rw [hsplit, List.mem_append] at hx
      rw [accumDir]
      rcases hx with hpre | hblk
      · -- earlier blocks: accumDir E j x ≠ none ⇒ overlay still ≠ none
        rw [← List.map_take] at hpre
        have haj : accumDir E j x ≠ none := ih x hpre
        intro hov
        by_cases hd : dirRestrBlock (residualIter E j) x = none
        · rw [overlay_eq_ρ_of_τ_none _ _ _ hd] at hov; exact haj hov
        · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hd
          rw [overlay_eq_some_of_τ _ _ _ b hb] at hov; simp at hov
      · -- the j-th block: x is in the head block of residualIter E j ⇒ dirRestrBlock fixes it
        -- so the overlay (τ wins) is ≠ none.
        rw [← List.map_drop, ← List.map_take] at hblk
        -- relate the residual head block to dirRestrBlock support
        have hdrop : deepPathV (residualIter E j)
            = (deepPathV E).drop (startLen (deepBlockLens E) j) := deepPathV_residualIter j E
        rw [← hdrop] at hblk
        -- x is a var of the head block of residualIter E j ⇒ dirRestrBlock (residualIter E j) x ≠ none
        -- hblk : x ∈ map fst ((deepPathV (residualIter E j)).take headLen)
        have hdrb : dirRestrBlock (residualIter E j) x ≠ none := by
          revert hblk
          generalize hR : residualIter E j = R
          cases R with
          | nil =>
              intro hblk
              simp only [show deepPathV ([] : DNF n) = [] from by rw [deepPathV],
                List.take_nil, List.map_nil] at hblk
              exact absurd hblk (List.not_mem_nil x)
          | cons term Ds =>
              cases term with
              | nil =>
                  intro hblk
                  simp only [show deepPathV (([] : Term n) :: Ds) = [] from by rw [deepPathV],
                    List.take_nil, List.map_nil] at hblk
                  exact absurd hblk (List.not_mem_nil x)
              | cons l0 t0 =>
                  intro hblk
                  have hbl : (deepBlockLens ((l0 :: t0) :: Ds)).headI = 1 + t0.length := by
                    rw [deepBlockLens_cons_cons_eq]; rfl
                  have htake : ((deepPathV ((l0 :: t0) :: Ds)).map Prod.fst).take (1 + t0.length)
                      = (l0 :: t0).map (·.var) := deepPathV_cons_cons_take l0 t0 Ds
                  rw [hbl] at hblk
                  rw [List.map_take, htake] at hblk
                  exact dirRestrBlock_mem_of_head l0 t0 Ds x hblk
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hdrb
        rw [overlay_eq_some_of_τ _ _ _ b hb]; simp

/-! ## 7. The survivor's ORIGINAL term is NOT falsified under the evolving state

The first `combRestr`-survivor `C₀` maps to the residual HEAD = `enteredTerm D ρ j`.  We
show no literal of `C₀` is fixed AGAINST its sign by `stateAt (encodeEnt₁ D s ρ) prev_j`,
hence `C₀` is not falsified.  The literals split exactly into:

* combRestr-FIXED literals: `stateAt` AGREES with `combRestr` there (ρ-fixed → encodeEnt₁
  extends ρ + prefix free; accumDir-fixed → prefix records accumDir via the bridge), and
  since `C₀` survives `combRestr` they are fixed TO their sign;
* combRestr-FREE literals: these are the `enteredTerm`'s literals (`mem_termRestrict_of_free`),
  fixed by `stateAt` either to `satValEnt = signInTerm(enteredTerm) = l.sign` (touched), or
  left free (untouched + prefix free, since accumDir-free ⟹ prefix-free by the bridge). -/

/-- **The survivor is not falsified (PROVED).**  If `C₀` is a D-original term with
`termRestrict (combRestr D ρ j) C₀ = some Cr` and `Cr = enteredTerm D ρ j` (i.e. `C₀` maps
to the residual head), then `C₀` is NOT falsified under
`stateAt (encodeEnt₁ D s ρ) ((deepPathV (D|ρ)).take (start j))`. -/
theorem survivor_ne_none_stateAt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (hD : SimpleDNF D) (j : Nat) (C₀ Cr : Term n)
    (hsurv : termRestrict (combRestr D ρ j) C₀ = some Cr)
    (hCr : Cr = enteredTerm D ρ j)
    (halign : ∀ l ∈ Cr,
        blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j) :
    termRestrict (stateAt (encodeEnt₁ D s ρ)
        ((deepPathV (dnfRestrict ρ D)).take
          (startLen (deepBlockLens (dnfRestrict ρ D)) j))) C₀ ≠ none := by
  set E := dnfRestrict ρ D with hE
  set k := startLen (deepBlockLens E) j with hk
  have hEsimp : SimpleDNF E := simpleDNF_dnfRestrict hD ρ
  -- the entered term (= Cr) is simple
  have hCrsimp : SimpleTerm Cr := by rw [hCr]; exact enteredTerm_simple hD ρ j
  apply termRestrict_ne_none_of_no_conflict
  intro l hl c hc
  -- hc : stateAt (encodeEnt₁) (take k) l.var = some c
  rw [stateAt] at hc
  -- decompose the overlay: prefix wins, else encodeEnt₁
  cases hpref : prefixRestr ((deepPathV E).take k) l.var with
  | some d =>
      -- prefix fixes l.var to a deep direction d; then c = d.  l.var is accumDir-fixed
      -- (prefix records accumDir), so combRestr l.var = d, and C₀ surviving ⇒ d = l.sign.
      rw [overlay_eq_some_of_τ _ _ _ d hpref] at hc
      have hcd : c = d := by rw [Option.some.injEq] at hc; exact hc.symm
      -- l.var ∈ prefix vars ⇒ accumDir-fixed (converse bridge) ⇒ prefix = accumDir = some d
      have hmem : l.var ∈ ((deepPathV E).take k).map Prod.fst := by
        by_contra hcon
        rw [prefixRestr_eq_none _ l.var hcon] at hpref
        simp at hpref
      have haccne : accumDir E j l.var ≠ none := accumDir_ne_none_of_mem_take E hEsimp j l.var hmem
      have hbridge : prefixRestr ((deepPathV E).take k) l.var = accumDir E j l.var :=
        prefixRestr_take_eq_accumDir E hEsimp j l.var haccne
      have hacc : accumDir E j l.var = some d := by rw [← hbridge]; exact hpref
      have hcomb : combRestr D ρ j l.var = some d := by
        unfold combRestr
        exact overlay_eq_some_of_τ ρ (accumDir E j) l.var d hacc
      -- C₀ survives combRestr ⇒ the literal l (∈ C₀) is fixed TO its sign by combRestr
      have hsign : d = l.sign := by
        have := termRestrict_ne_none_of_no_conflict (combRestr D ρ j) C₀
        -- extract: combRestr fixes l.var to d = l.sign (no conflict, since survives)
        by_contra hds
        have hkill : termRestrict (combRestr D ρ j) C₀ = none :=
          SwitchingStepData.termRestrict_none_of_lit_fixed (combRestr D ρ j) C₀ l hl d hcomb hds
        rw [hkill] at hsurv; simp at hsurv
      rw [hcd, hsign]
  | none =>
      -- prefix free: stateAt = encodeEnt₁.  l.var free in accumDir (else prefix some).
      rw [overlay_eq_ρ_of_τ_none _ _ _ hpref] at hc
      -- accumDir E j l.var = none  (else prefix = accumDir ≠ none)
      have hacc_none : accumDir E j l.var = none := by
        by_contra hne
        have hp := prefixRestr_take_eq_accumDir E hEsimp j l.var hne
        rw [hp] at hpref
        exact hne hpref
      -- encodeEnt₁ = overlay ρ satRestrEnt; cases on ρ
      unfold encodeEnt₁ at hc
      cases hρl : ρ l.var with
      | some b =>
          -- combRestr l.var = some b (ρ wins, accumDir none); C₀ survives ⇒ b = l.sign
          have hsatn : satRestrEnt D s ρ l.var = none :=
            satRestrEnt_disj D s ρ l.var (by rw [hρl]; simp)
          rw [overlay_eq_ρ_of_τ_none ρ (satRestrEnt D s ρ) l.var hsatn, hρl] at hc
          have hcb : c = b := by rw [Option.some.injEq] at hc; exact hc.symm
          have hcomb : combRestr D ρ j l.var = some b := by
            unfold combRestr
            rw [overlay_eq_ρ_of_τ_none ρ (accumDir E j) l.var hacc_none, hρl]
          have hsign : b = l.sign := by
            by_contra hds
            have hkill : termRestrict (combRestr D ρ j) C₀ = none :=
              SwitchingStepData.termRestrict_none_of_lit_fixed (combRestr D ρ j) C₀ l hl b hcomb hds
            rw [hkill] at hsurv; simp at hsurv
          rw [hcb, hsign]
      | none =>
          -- ρ free, accumDir free ⇒ combRestr free ⇒ l ∈ Cr = enteredTerm (free literal)
          have hcombn : combRestr D ρ j l.var = none := by
            unfold combRestr
            rw [overlay_eq_ρ_of_τ_none ρ (accumDir E j) l.var hacc_none, hρl]
          have hlCr : l ∈ Cr := mem_termRestrict_of_free (combRestr D ρ j) C₀ Cr hsurv l hl hcombn
          -- encodeEnt₁ l.var = satRestrEnt (ρ none); if some c, then c = satValEnt = sign
          cases hsat : satRestrEnt D s ρ l.var with
          | none =>
              rw [overlay_eq_ρ_of_τ_none ρ (satRestrEnt D s ρ) l.var hsat, hρl] at hc
              simp at hc
          | some sv =>
              rw [overlay_eq_some_of_τ ρ (satRestrEnt D s ρ) l.var sv hsat] at hc
              have hcsv : c = sv := by rw [Option.some.injEq] at hc; exact hc.symm
              -- sv = satValEnt D s ρ l.var ; touched
              have htouch : l.var ∈ touchedVars D s ρ := by
                by_contra hnt
                rw [(satRestrEnt_eq_none_iff D s ρ l.var).mpr hnt] at hsat; simp at hsat
              have hsveq : sv = satValEnt D s ρ l.var := by
                rw [satRestrEnt_eq_some D s ρ l.var htouch] at hsat; injection hsat with hsv
                exact hsv.symm
              -- satValEnt l.var = signInTerm (enteredTerm D ρ jv) l.var where jv is l.var's block.
              -- But l ∈ Cr = enteredTerm D ρ j, simple, so signInTerm reads l.sign — provided
              -- the block of l.var is j.  We instead read directly: l ∈ enteredTerm D ρ j,
              -- and satValEnt reads signInTerm of l.var's OWN block's entered term.
              rw [hcsv, hsveq]
              -- satValEnt l.var = signInTerm (enteredTerm D ρ (blockOf l.var)) l.var.
              -- With halign (blockOf l.var = j), this is signInTerm Cr l.var = l.sign.
              unfold satValEnt
              simp only
              rw [halign l hlCr, ← hCr]
              exact signInTerm_of_mem Cr hCrsimp l hlCr

/-! ## 7b. Discharging `halign`: the entered term is block-aligned (general `j`)

The j-th entered term's variables have deep BLOCK NUMBER `j`.  Proof: the entered term IS
the head block of `residualIter (D|ρ) j` (`deepResidual_head`), so its variables, as a
contiguous slice `[start j, start(j+1))` of the (nodup) deep path, have deep positions in
that range, whose block index is `j` (the arithmetic lemma `blockIndexOfIndex_eq_of_range`).
This discharges the `halign` hypothesis left open in `SwitchingEnteredOrder`. -/

/-- The entered term's variable list equals the j-th deep block slice's variable list.
`enteredTerm = (residualIter E j).headI`; for a nonempty head term `l0::t0`, its vars in
deep order are the head block of `deepPathV (residualIter E j)`, which by `deepResidual_head`
is `deepBlockNum D ρ j`. -/
theorem enteredTerm_map_var_eq {n : Nat} (D : DNF n) (ρ : Restriction n) (j : Nat) :
    (enteredTerm D ρ j).map (·.var) = (deepBlockNum D ρ j).map Prod.fst := by
  rw [deepResidual_head]
  unfold enteredTerm
  cases hR : residualIter (dnfRestrict ρ D) j with
  | nil =>
      rw [show deepPathV ([] : DNF n) = [] from by rw [deepPathV]]
      simp only [List.headI_nil, List.take_nil, List.map_nil]
      rfl
  | cons term Ds =>
      cases term with
      | nil =>
          rw [show deepPathV (([] : Term n) :: Ds) = [] from by rw [deepPathV]]
          simp only [List.headI_cons, List.take_nil, List.map_nil]
      | cons l0 t0 =>
          have hbl : (deepBlockLens ((l0 :: t0) :: Ds)).headI = 1 + t0.length := by
            rw [deepBlockLens_cons_cons_eq]; rfl
          have htake : ((deepPathV ((l0 :: t0) :: Ds)).map Prod.fst).take (1 + t0.length)
              = (l0 :: t0).map (·.var) := deepPathV_cons_cons_take l0 t0 Ds
          rw [List.headI_cons, hbl, List.map_take, htake]

/-- **Entered term block-alignment (PROVED, discharges `halign`).**  For `j < #blocks` (so
the j-th block slice is nonempty / in range) and `l ∈ enteredTerm D ρ j`, the deep block
number of `l.var` is `j`.  Via `enteredTerm_map_var_eq`, `l.var` is in the block slice
`[start j, start(j+1))` of the nodup deep path, so `deepPosOf l.var` lands in that range and
`blockIndexOfIndex … = j`. -/
theorem enteredTerm_block_aligned {n : Nat} (D : DNF n) (ρ : Restriction n)
    (hD : SimpleDNF D) (j : Nat) (hj : j < (deepBlockLens (dnfRestrict ρ D)).length) :
    ∀ l ∈ enteredTerm D ρ j,
      blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j := by
  -- Abbreviations (plain `let`-style via `have` rfl-equations to avoid `set` fragility)
  have hnd : ((deepPathV (dnfRestrict ρ D)).map Prod.fst).Nodup := by
    rw [deepPathV_eq]
    exact deepestPath_nodup _ (distinctPaths_termCanonicalDT _ (simpleDNF_dnfRestrict hD ρ))
  intro l hl
  -- l.var is in the j-th deep block slice
  have hvmem : l.var ∈ (deepBlockNum D ρ j).map Prod.fst := by
    rw [← enteredTerm_map_var_eq]; exact List.mem_map_of_mem (·.var) hl
  -- deepBlockNum's vars = (path-vars).drop (start j) |>.take blockLen
  have hslice : (deepBlockNum D ρ j).map Prod.fst
      = (((deepPathV (dnfRestrict ρ D)).map Prod.fst).drop
          (startLen (deepBlockLens (dnfRestrict ρ D)) j)).take
          ((deepBlockLens (dnfRestrict ρ D)).drop j).headI := by
    unfold deepBlockNum
    rw [List.map_take, List.map_drop]
  rw [hslice, List.mem_iff_getElem] at hvmem
  obtain ⟨o, ho, hoval⟩ := hvmem
  rw [List.length_take, List.length_drop] at ho
  have ho_blk : o < ((deepBlockLens (dnfRestrict ρ D)).drop j).headI :=
    lt_of_lt_of_le ho (Nat.min_le_left _ _)
  have ho_len : startLen (deepBlockLens (dnfRestrict ρ D)) j + o
      < ((deepPathV (dnfRestrict ρ D)).map Prod.fst).length := by
    have := lt_of_lt_of_le ho (Nat.min_le_right _ _); omega
  have hpos_elt : ((deepPathV (dnfRestrict ρ D)).map Prod.fst)[
        startLen (deepBlockLens (dnfRestrict ρ D)) j + o]'ho_len = l.var := by
    rw [← hoval, List.getElem_take, List.getElem_drop]
  have hdeeppos : deepPosOf D ρ l.var
      = startLen (deepBlockLens (dnfRestrict ρ D)) j + o := by
    unfold deepPosOf
    rw [← hpos_elt]
    exact List.get_indexOf hnd ⟨_, ho_len⟩
  rw [hdeeppos]
  exact blockIndexOfIndex_eq_of_range (deepBlockLens (dnfRestrict ρ D)) j _ hj
    (Nat.le_add_right _ _) (by omega)

/-- **Entered term block-alignment, packaged for the bad set (PROVED).**  On the bad set,
when `residualIter (D|ρ) j` is nonempty (head term `Cr`), every literal of `Cr` is
block-`j`-aligned — `j < #blocks` because the residual head occupies block `j`. -/
theorem enteredTerm_block_aligned_head {n : Nat} (D : DNF n) (ρ : Restriction n)
    (hD : SimpleDNF D) (j : Nat) (Cr : Term n) (rest' : DNF n)
    (hhead : residualIter (dnfRestrict ρ D) j = Cr :: rest') :
    ∀ l ∈ Cr,
      blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j := by
  intro l hl
  -- Cr is nonempty (it has the literal l), say Cr = l0 :: t0
  have hCrent : Cr = enteredTerm D ρ j := by unfold enteredTerm; rw [hhead]; rfl
  -- j < #blocks: the j-th block (head of residualIter E j) is a NONEMPTY term, so
  -- deepBlockLens (residualIter E j) = (deepBlockLens E).drop j is nonempty.
  have hj : j < (deepBlockLens (dnfRestrict ρ D)).length := by
    cases Cr with
    | nil => exact absurd hl (List.not_mem_nil l)
    | cons l0 t0 =>
        have hlen : 0 < (deepBlockLens (residualIter (dnfRestrict ρ D) j)).length := by
          rw [hhead]
          rw [deepBlockLens_cons_cons_eq l0 t0 rest']
          simp
        rw [deepBlockLens_residualIter, List.length_drop] at hlen
        omega
  rw [hCrent] at hl
  exact enteredTerm_block_aligned D ρ hD j hj l hl

/-! ## 8. THE PER-STEP TERM IDENTIFICATION (assembled, PROVED at a block boundary)

We now assemble §1 (HALF 1), §4 (ρ-killed), §5 (completeness), §3 (filterMap factor) and
§7 (survivor) into the per-step identification: the D-ORIGINAL scan
`firstNonFalsified D (stateAt (encodeEnt₁ …) prev_j)` returns the FIRST D-original term
`C₀` mapping to the residual head = `enteredTerm D ρ j`, for any `j` with a nonempty
residual `residualIter (D|ρ) j` and the entered-term block-alignment `halign`.

This is the genuine assembly the task targets: HALF 1 + ρ-killed give every earlier term
falsified (completeness), HALF 2 (via §7) gives the survivor not falsified. -/

/-- **PER-STEP TERM IDENTIFICATION (PROVED, block boundary).**  Let `residualIter (D|ρ) j =
Cr :: rest'` (nonempty: the j-th entered term is its head `Cr = enteredTerm D ρ j`).  Then
`D` ORIGINAL factors as `pre ++ C₀ :: restD` with `pre` all FALSIFIED under
`stateAt (encodeEnt₁ D s ρ) prev_j` (completeness: §4 + §1), `C₀` NOT falsified (§7), and
`termRestrict (combRestr D ρ j) C₀ = some Cr`.  Consequently the D-original scan
`firstNonFalsified D (stateAt (encodeEnt₁ D s ρ) prev_j) = some C₀`. -/
theorem firstNonFalsified_eq_survivor {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (hD : SimpleDNF D) (j : Nat) (Cr : Term n) (rest' : DNF n)
    (hhead : residualIter (dnfRestrict ρ D) j = Cr :: rest') :
    ∃ (pre : List (Term n)) (C₀ : Term n) (restD : DNF n),
      D = pre ++ C₀ :: restD
      ∧ firstNonFalsified D (stateAt (encodeEnt₁ D s ρ)
          ((deepPathV (dnfRestrict ρ D)).take
            (startLen (deepBlockLens (dnfRestrict ρ D)) j))) = some C₀
      ∧ termRestrict (combRestr D ρ j) C₀ = some Cr := by
  -- residualIter = dnfRestrict combRestr D = filterMap (termRestrict combRestr) D
  have hfilt : dnfRestrict (combRestr D ρ j) D = Cr :: rest' := by
    rw [← residualIter_eq_dnfRestrict_combRestr D ρ hD j]; exact hhead
  -- factor D ORIGINAL via the filterMap head factorization
  have hfm : (D.filterMap (termRestrict (combRestr D ρ j))) = Cr :: rest' := by
    rw [← hfilt]; rfl
  obtain ⟨pre, C₀, restD, hDfac, hC₀surv, hpreKill⟩ :=
    filterMap_head_factor (termRestrict (combRestr D ρ j)) D Cr rest' hfm
  refine ⟨pre, C₀, restD, hDfac, ?_, hC₀surv⟩
  set st := stateAt (encodeEnt₁ D s ρ)
    ((deepPathV (dnfRestrict ρ D)).take
      (startLen (deepBlockLens (dnfRestrict ρ D)) j)) with hst
  -- completeness: every pre-term is falsified under st
  have hpre : ∀ p ∈ pre, termRestrict st p = none := by
    intro p hp
    rw [hst]
    exact combRestr_killed_falsified_stateAt D s ρ hD j p (hpreKill p hp)
  -- survivor: C₀ not falsified under st (Cr = enteredTerm D ρ j = residual head)
  have hCrent : Cr = enteredTerm D ρ j := by
    unfold enteredTerm; rw [hhead]; rfl
  have halign : ∀ l ∈ Cr,
      blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) (deepPosOf D ρ l.var) = j :=
    enteredTerm_block_aligned_head D ρ hD j Cr rest' hhead
  have hC₀ : termRestrict st C₀ ≠ none := by
    rw [hst]
    exact survivor_ne_none_stateAt D s ρ hD j C₀ Cr hC₀surv hCrent halign
  -- firstNonFalsified lands on C₀
  rw [hst]
  exact firstNonFalsified_eq_of_factor D st pre C₀ restD hDfac hpre hC₀

/-! ## 9. HONESTY: the exact residual to `DOrigStepData` / `SwitchingLemmaTermSimple`

The per-step term identification `firstNonFalsified_eq_survivor` supplies, ρ-DEPENDENTLY
but verifiably, the first three of the four conjuncts of `SwitchingDOrig.DOrigStepData` at
a block boundary: the factorization `D = pre ++ C₀ :: restD`, the prefix-falsification, and
the non-falsification of `C₀`.  The FOURTH conjunct — the column read
`colVar C₀ codeColumn = [i-th deep var]` — is the column-agreement wall (G1), recorded
PROVED-EQUIVALENT to a `(C₀.map var)[col]? = (deepBlock).map fst)[col]?` agreement in
`SwitchingDOrig.colVar_orig_eq_iff_column_agree`, which we do NOT assert.  Combined with the
block-boundary-vs-mid-block prefix mismatch (G2), `SwitchingLemmaTermSimple` is NOT proved
outright here.  We re-export the proved reduction that would reach it FROM `DOrigStepData`,
so the chain is reached from the isolated, satisfiable factorization datum — not faked. -/

/-- **Re-export (PROVED): `DOrigStepData n → SwitchingLemmaTermSimple n`.**  The proved
capstone of `SwitchingDOrig`.  Our per-step identification (`firstNonFalsified_eq_survivor`)
discharges three of `DOrigStepData`'s four conjuncts at a block boundary; the column read
(G1) and the mid-block prefix (G2) remain the isolated residual.  We do NOT assert
`DOrigStepData`. -/
theorem switchingLemmaTermSimple_of_dorigStepData_reexport {n : Nat}
    (h : SwitchingDOrig.DOrigStepData n) : SwitchingLemmaTermSimple n :=
  SwitchingDOrig.switchingLemmaTermSimple_of_dorigStepData h

end SwitchingAssemble
end PvNP
