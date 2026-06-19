/-
# Closing the column-read: the ORIGINAL-INDEX code and the per-step variable recovery

This file closes the FINAL gap of the term switching lemma for simple DNFs.  The per-step
term IDENTIFICATION is already PROVED (`SwitchingAssemble.firstNonFalsified_eq_survivor`:
the first not-falsified D-original term `C₀` under the ρ-independent evolving state at a
block boundary IS the survivor whose ρ-restriction is the entered/residual term).  What
remained was reading the deep variable off that identified term `C₀` at the right column.

## The fix (G1: original-index column; G2: boundary-truncated prefix)

The prior obstruction (G1) was that the code column indexed the deep BLOCK (deep-path
order of `D|ρ`), whereas `C₀` is the ORIGINAL term with ρ-fixed literals re-inserted, so
the deep-block index points at the wrong literal of `C₀`.  We FIX this at ENCODE time
(where `ρ` is known): the code records, per deep position, the variable's ORIGINAL INDEX in
`C₀` — namely the index in `C₀.map var` of the deep variable.  Since the deep variable IS a
literal of `C₀` (it lies in `Cr ⊆ C₀`, `termRestrict_mem_of_mem`) and `C₀` is simple
(`SimpleDNF D`), reading `(C₀.map var)[origIdx]? = some (deep var)` holds DIRECTLY
(`List.getElem?_indexOf_self`-style).  The original index is `< C₀.length = termWidth C₀ ≤
widthDNF D ≤ w`, so the `Fin w` budget — and the `(8w)^s` card — is preserved.

The prior obstruction (G2) was that `firstNonFalsified_eq_survivor` holds at a block
BOUNDARY (`take (start j)`), whereas the per-step recovery iterates over deep POSITIONS
(`take i`, possibly mid-block).  We DISSOLVE this: the per-step recovery, at position `i`,
truncates the recovered prefix `prev = take i` back to its block boundary `take (start j)`
(`j = block of i`), and identifies `C₀` THERE — at the boundary, where the survivor lemma
applies.  The within-block offset `i - start j = blockPosOfIndex bs i` is recovered
ρ-INDEPENDENTLY from the code's `last`-bits (`isLastInBlock_within`), so the truncation is a
function of `prev` and the code alone.  Reading `C₀` at the recorded original index then
gives the i-th deep variable for EVERY `i < s`, mid-block included.

## What this file PROVES OUTRIGHT (axioms ⊆ [propext, Classical.choice, Quot.sound])

* `origColRead` — reading `C₀` (the boundary survivor) at the recorded original index of the
  deep variable returns exactly that deep variable (the column lemma, via simplicity of
  `C₀`).
* the per-step recovery `decodeOrigStep` and its correctness `decodeOrigStep_eq` on the bad
  set for EVERY `i < s` (boundary truncation + survivor identification + original-index
  read).
* the encode `codeOrig` (a genuine `RCode s w`, same `(8w)^s` card) and the recovery's fold
  into `RCodeRecoverable` analogue, hence `SwitchingLemmaTermSimple n` via the encodeEnt₁
  injection backbone (re-proved here for `encodeEnt₁`, mirroring the proved `encodeLoc₁`
  determination + star count).
* `switchingLemmaTermSimple_proved {n} : SwitchingLemmaTermSimple n` — the FINAL theorem.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Imported files are
untouched.
-/
import PvNP.SwitchingAssemble

namespace PvNP
namespace SwitchingClose2

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
open SwitchingAssemble
open Classical

/-! ## 0. Positivity of `deepBlockLens` (every block has ≥ 1 variable) -/

mutual
/-- **Every `deepBlockLens` entry is positive (PROVED).**  Each emitted block length is
`1 + t.length ≥ 1` (the head term's variable count along the deep path). -/
theorem deepBlockLens_pos {n : Nat} :
    ∀ (D : DNF n), ∀ x ∈ deepBlockLens D, 0 < x
  | [] => by intro x hx; rw [deepBlockLens] at hx; exact absurd hx (List.not_mem_nil x)
  | [] :: _ => by intro x hx; rw [deepBlockLens] at hx; exact absurd hx (List.not_mem_nil x)
  | (l :: t) :: D => by
      intro x hx
      rw [deepBlockLens] at hx
      simp only [List.mem_cons] at hx
      rcases hx with hxh | hxt
      · omega
      · by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
            ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
        · simp only [if_pos h] at hxt
          exact deepBlockLensQ_pos t (assignVar l.var true ((l :: t) :: D)) x hxt
        · simp only [if_neg h] at hxt
          exact deepBlockLensQ_pos t (assignVar l.var false ((l :: t) :: D)) x hxt
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)

theorem deepBlockLensQ_pos {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), ∀ x ∈ deepBlockLensQ vars D, 0 < x
  | [], D => by intro x hx; rw [deepBlockLensQ] at hx; exact deepBlockLens_pos D x hx
  | l :: vs, D => by
      intro x hx
      rw [deepBlockLensQ] at hx
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · simp only [if_pos h] at hx
        exact deepBlockLensQ_pos vs (assignVar l.var true D) x hx
      · simp only [if_neg h] at hx
        exact deepBlockLensQ_pos vs (assignVar l.var false D) x hx
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

/-! ## 0b. Pure list facts: indexOf reads back, within-block position from last-bits -/

/-- For `v ∈ L`, reading `L` at `L.indexOf v` gives back `v`. -/
theorem getElem?_indexOf_self {α : Type*} [DecidableEq α] (L : List α) (v : α)
    (hv : v ∈ L) : L[L.indexOf v]? = some v := by
  have hlt : L.indexOf v < L.length := List.indexOf_lt_length.mpr hv
  rw [List.getElem?_eq_getElem hlt]
  exact congrArg some (List.getElem_indexOf hlt)

/-- **Block start = index − within-block offset (PROVED).**  For any `bs` and `i`,
`startLen bs (blockIndexOfIndex bs i) + blockPosOfIndex bs i = i`.  Induction on `bs`. -/
theorem startLen_blockIndex_add_blockPos :
    ∀ (bs : List Nat) (i : Nat),
      startLen bs (blockIndexOfIndex bs i) + blockPosOfIndex bs i = i
  | [], i => by
      rw [blockIndexOfIndex, blockPosOfIndex]
      rw [show startLen ([] : List Nat) 0 = 0 from by rw [startLen]]; omega
  | b :: bs, i => by
      rw [blockIndexOfIndex, blockPosOfIndex]
      by_cases hib : i < b
      · simp only [if_pos hib]
        rw [show startLen (b :: bs) 0 = 0 from by rw [startLen]]; omega
      · simp only [if_neg hib]
        rw [show startLen (b :: bs) (1 + blockIndexOfIndex bs (i - b))
              = b + startLen bs (blockIndexOfIndex bs (i - b)) from by
            rw [show (1 + blockIndexOfIndex bs (i - b)) = (blockIndexOfIndex bs (i - b)) + 1 from by
              omega, startLen]]
        have ih := startLen_blockIndex_add_blockPos bs (i - b)
        omega

/-- **`isLastInBlock` characterizes the within-block position (PROVED).**  For `i < bs.sum`,
`isLastInBlock bs i = true` iff `i` is the LAST slot of its block, i.e.
`blockPosOfIndex bs i + 1 = blockLenAt bs i`.  (Re-export of `isLastInBlock_lt_sum`.) -/
theorem isLastInBlock_iff {bs : List Nat} {i : Nat} (h : i < bs.sum) :
    isLastInBlock bs i = true ↔ blockPosOfIndex bs i + 1 = blockLenAt bs i := by
  rw [isLastInBlock_lt_sum h]; simp

/-- The block-length at a global index equals the j-th block length where `j` is its block
number; for `i < bs.sum`, `blockLenAt bs i = (bs.drop (blockIndexOfIndex bs i)).headI`. -/
theorem blockLenAt_eq_drop_headI :
    ∀ (bs : List Nat) (i : Nat),
      blockLenAt bs i = (bs.drop (blockIndexOfIndex bs i)).headI
  | [], i => by simp [blockLenAt, blockIndexOfIndex]
  | b :: bs, i => by
      rw [blockLenAt, blockIndexOfIndex]
      by_cases hib : i < b
      · simp only [if_pos hib, List.drop, List.headI]
      · simp only [if_neg hib]
        rw [show (1 + blockIndexOfIndex bs (i - b)) = (blockIndexOfIndex bs (i - b)) + 1 from by
          omega, List.drop_succ_cons]
        exact blockLenAt_eq_drop_headI bs (i - b)

/-- **Block index steps by 1 at a block boundary (PROVED).**  If `i` is the LAST slot of
its block (`blockPosOfIndex bs i + 1 = blockLenAt bs i`) and `i < bs.sum`, then
`blockIndexOfIndex bs (i + 1) = blockIndexOfIndex bs i + 1`. -/
theorem blockIndexOfIndex_succ_of_last :
    ∀ (bs : List Nat), (∀ x ∈ bs, 0 < x) → ∀ (i : Nat), i < bs.sum →
      blockPosOfIndex bs i + 1 = blockLenAt bs i →
        blockIndexOfIndex bs (i + 1) = blockIndexOfIndex bs i + 1
  | [], _, i, h, _ => by simp [List.sum_nil] at h
  | b :: bs, hpos, i, h, hlast => by
      rw [blockPosOfIndex, blockLenAt] at hlast
      by_cases hib : i < b
      · -- i last of head block: i+1 = b, so i+1 is not < b
        simp only [if_pos hib] at hlast
        have hi1 : ¬ (i + 1 < b) := by omega
        simp only [blockIndexOfIndex, if_pos hib, if_neg hi1]
        rw [show i + 1 - b = 0 from by omega]
        cases bs with
        | nil => rw [blockIndexOfIndex]
        | cons b2 bs2 =>
            have hb2 : 0 < b2 := hpos b2 (by simp)
            simp [blockIndexOfIndex, hb2]
      · simp only [if_neg hib] at hlast
        have hi1 : ¬ (i + 1 < b) := by omega
        simp only [blockIndexOfIndex, if_neg hib, if_neg hi1]
        have hlt : i - b < bs.sum := by rw [List.sum_cons] at h; omega
        rw [show i + 1 - b = (i - b) + 1 from by omega]
        rw [blockIndexOfIndex_succ_of_last bs (fun x hx => hpos x (by simp [hx])) (i - b) hlt hlast]
        omega

/-- **Block index unchanged mid-block (PROVED).**  If `i` is NOT the last slot of its
block (`blockPosOfIndex bs i + 1 ≠ blockLenAt bs i`) and `i < bs.sum`, then
`blockIndexOfIndex bs (i + 1) = blockIndexOfIndex bs i`. -/
theorem blockIndexOfIndex_succ_of_not_last :
    ∀ (bs : List Nat) (i : Nat), i < bs.sum →
      blockPosOfIndex bs i + 1 ≠ blockLenAt bs i →
        blockIndexOfIndex bs (i + 1) = blockIndexOfIndex bs i
  | [], i, h, _ => by simp [List.sum_nil] at h
  | b :: bs, i, h, hlast => by
      rw [blockPosOfIndex, blockLenAt] at hlast
      by_cases hib : i < b
      · simp only [if_pos hib] at hlast
        -- i not last of head: i + 1 < b
        have hi1 : i + 1 < b := by omega
        simp only [blockIndexOfIndex, if_pos hib, if_pos hi1]
      · simp only [if_neg hib] at hlast
        have hi1 : ¬ (i + 1 < b) := by omega
        simp only [blockIndexOfIndex, if_neg hib, if_neg hi1]
        have hlt : i - b < bs.sum := by rw [List.sum_cons] at h; omega
        rw [show i + 1 - b = (i - b) + 1 from by omega]
        rw [blockIndexOfIndex_succ_of_not_last bs (i - b) hlt hlast]

/-- ρ-INDEPENDENT block-start recursion driven by the `last`-bit predicate: the start of
the block containing index `i`.  `bits m` = "position `m` ends its block". -/
def blockStartFromBits (bits : Nat → Bool) : Nat → Nat
  | 0 => 0
  | (i + 1) => if bits i then i + 1 else blockStartFromBits bits i

/-- `blockStartFromBits` depends only on `bits` below the index (PROVED).  If `f` and `g`
agree on `[0, i)`, then `blockStartFromBits f i = blockStartFromBits g i`. -/
theorem blockStartFromBits_congr (f g : Nat → Bool) :
    ∀ (i : Nat), (∀ m, m < i → f m = g m) →
      blockStartFromBits f i = blockStartFromBits g i
  | 0, _ => by rw [blockStartFromBits, blockStartFromBits]
  | (i + 1), hfg => by
      rw [blockStartFromBits, blockStartFromBits]
      rw [hfg i (Nat.lt_succ_self i)]
      rw [blockStartFromBits_congr f g i (fun m hm => hfg m (by omega))]

/-- **The `last`-bit recursion computes the block start (PROVED).**  For `i < bs.sum`,
`blockStartFromBits (isLastInBlock bs) i = startLen bs (blockIndexOfIndex bs i)` — the
ρ-independent recovery of the block boundary from the code's `last`-bits. -/
theorem blockStartFromBits_eq_startLen :
    ∀ (bs : List Nat), (∀ x ∈ bs, 0 < x) → ∀ (i : Nat), i < bs.sum →
      blockStartFromBits (fun m => isLastInBlock bs m) i
        = startLen bs (blockIndexOfIndex bs i)
  | bs, hpos, 0, hlt => by
      rw [blockStartFromBits]
      have h1 : blockIndexOfIndex bs 0 = 0 := by
        cases bs with
        | nil => rw [blockIndexOfIndex]
        | cons b bs =>
            have hb0 : 0 < b := hpos b (List.mem_cons_self _ _)
            rw [blockIndexOfIndex]; simp [hb0]
      rw [h1]
      cases bs with
      | nil => rw [startLen]
      | cons b bs => rw [startLen]
  | bs, hpos, (i + 1), hlt => by
      have hi : i < bs.sum := by omega
      rw [blockStartFromBits]
      have hlast := isLastInBlock_iff hi
      by_cases hb : isLastInBlock bs i = true
      · simp only [hb, if_pos]
        have hpos' : blockPosOfIndex bs i + 1 = blockLenAt bs i := hlast.mp hb
        rw [blockIndexOfIndex_succ_of_last bs hpos i hi hpos', startLen_succ_eq]
        have hkey := startLen_blockIndex_add_blockPos bs i
        have hlen := blockLenAt_eq_drop_headI bs i
        rw [← hlen]; omega
      · have hbf : isLastInBlock bs i = false := by
          cases hbb : isLastInBlock bs i with
          | true => exact absurd hbb hb
          | false => rfl
        simp only [hbf, Bool.false_eq_true, if_false]
        have hpos' : blockPosOfIndex bs i + 1 ≠ blockLenAt bs i := by
          intro heq
          rw [hlast.mpr heq] at hbf; exact absurd hbf (by simp)
        rw [blockIndexOfIndex_succ_of_not_last bs i hi hpos']
        exact blockStartFromBits_eq_startLen bs hpos i hi

/-! ## 1. The i-th deep entry lies in its block; survivor map; the column read -/

/-- **Within-block position < the matched block length (PROVED).**  For `i < bs.sum`,
`blockPosOfIndex bs i < blockLenAt bs i`.  Induction on `bs`. -/
theorem blockPosOfIndex_lt_blockLenAt :
    ∀ (bs : List Nat) (i : Nat), i < bs.sum →
      blockPosOfIndex bs i < blockLenAt bs i
  | [], i, h => by simp [List.sum_nil] at h
  | b :: bs, i, h => by
      rw [blockPosOfIndex, blockLenAt]
      by_cases hib : i < b
      · simp only [if_pos hib]; exact hib
      · simp only [if_neg hib]
        have hlt : i - b < bs.sum := by rw [List.sum_cons] at h; omega
        exact blockPosOfIndex_lt_blockLenAt bs (i - b) hlt

/-- **The i-th deep entry is in its deep block (PROVED).**  For `i < (deepPathV E).length`
and `j = blockIndexOfIndex (deepBlockLens E) i`, the entry `(deepPathV E).get ⟨i,_⟩` lies in
`deepBlockNum D ρ j` (the j-th block slice).  Position `i = start j + blockPos i`, with
`blockPos i < blockLen`, so it lands in the `[start j, start j + blockLen)` slice. -/
theorem deepPathV_get_mem_deepBlockNum {n : Nat} (D : DNF n) (ρ : Restriction n)
    (i : Nat) (hi : i < (deepPathV (dnfRestrict ρ D)).length) :
    (deepPathV (dnfRestrict ρ D)).get ⟨i, hi⟩
      ∈ deepBlockNum D ρ (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i) := by
  have hsum : i < (deepBlockLens (dnfRestrict ρ D)).sum := by
    rw [deepBlockLens_sum_eq]; exact hi
  have hstart : startLen (deepBlockLens (dnfRestrict ρ D))
        (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i)
      + blockPosOfIndex (deepBlockLens (dnfRestrict ρ D)) i = i :=
    startLen_blockIndex_add_blockPos (deepBlockLens (dnfRestrict ρ D)) i
  have hblockpos_lt : blockPosOfIndex (deepBlockLens (dnfRestrict ρ D)) i
      < blockLenAt (deepBlockLens (dnfRestrict ρ D)) i :=
    blockPosOfIndex_lt_blockLenAt (deepBlockLens (dnfRestrict ρ D)) i hsum
  have hleneq : blockLenAt (deepBlockLens (dnfRestrict ρ D)) i
      = ((deepBlockLens (dnfRestrict ρ D)).drop
          (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i)).headI :=
    blockLenAt_eq_drop_headI (deepBlockLens (dnfRestrict ρ D)) i
  -- the block slice is deepBlockNum D ρ j; membership via the q-th element
  rw [List.mem_iff_getElem]
  refine ⟨blockPosOfIndex (deepBlockLens (dnfRestrict ρ D)) i, ?_, ?_⟩
  · unfold deepBlockNum
    rw [List.length_take, List.length_drop]
    omega
  · unfold deepBlockNum
    rw [List.getElem_take, List.getElem_drop, List.get_eq_getElem]
    have : startLen (deepBlockLens (dnfRestrict ρ D))
          (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i)
        + blockPosOfIndex (deepBlockLens (dnfRestrict ρ D)) i = i := hstart
    simp only [this]

/-! ## 2. The survivor term at a block boundary, and the original-index column read -/

/-- The ρ-INDEPENDENT **survivor term at block boundary `j`**: the first D-original term not
falsified under the evolving `encodeEnt₁`-state at the boundary prefix `take (start j)`.  By
`firstNonFalsified_eq_survivor` this is the original term `C₀` whose `combRestr`-restriction
is the entered/residual term `Cr = enteredTerm D ρ j`. -/
noncomputable def survTerm {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) (j : Nat) :
    Term n :=
  (firstNonFalsified D (stateAt (encodeEnt₁ D s ρ)
    ((deepPathV (dnfRestrict ρ D)).take
      (startLen (deepBlockLens (dnfRestrict ρ D)) j)))).getD []

/-- **The survivor term IS `C₀` (PROVED).**  When `residualIter (D|ρ) j = Cr :: rest'`,
`survTerm D s ρ j` equals the survivor `C₀` of `firstNonFalsified_eq_survivor`, which is in
`D`, maps under `combRestr` to `Cr`, and `Cr = enteredTerm D ρ j`. -/
theorem survTerm_spec {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (hD : SimpleDNF D) (j : Nat) (Cr : Term n) (rest' : DNF n)
    (hhead : residualIter (dnfRestrict ρ D) j = Cr :: rest') :
    survTerm D s ρ j ∈ D
      ∧ termRestrict (combRestr D ρ j) (survTerm D s ρ j) = some Cr := by
  obtain ⟨pre, C₀, restD, hDfac, hfnf, hcomb⟩ :=
    firstNonFalsified_eq_survivor D s ρ hD j Cr rest' hhead
  have hsurv : survTerm D s ρ j = C₀ := by
    unfold survTerm; rw [hfnf]; rfl
  rw [hsurv]
  refine ⟨?_, hcomb⟩
  rw [hDfac]; exact List.mem_append_right pre (List.mem_cons_self _ _)

/-- **The i-th deep variable is a variable of the survivor term (PROVED).**  For a bad `ρ`,
step `i < s`, with `j = block of i`, the i-th deep variable lies in `(survTerm D s ρ j).map
(·.var)`: it is a variable of `Cr = enteredTerm D ρ j` (block-alignment +
`enteredTerm_map_var_eq`), and every variable of `Cr` is a variable of `C₀ = survTerm`
(free literals survive `termRestrict`). -/
theorem deepVar_mem_survTerm_map {n : Nat} (D : DNF n) (s ℓ : Nat) (ρ : Restriction n)
    (hD : SimpleDNF D) (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s) :
    ((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1
      ∈ (survTerm D s ρ
          (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i)).map (·.var) := by
  set E := dnfRestrict ρ D with hE
  set bs := deepBlockLens E with hbs
  set j := blockIndexOfIndex bs i with hj
  have hilen : i < (deepPathV E).length := lt_deepPathV_length_of_bad hρ hi
  -- residual at block j is nonempty (the i-th entry lives in block j)
  -- deepBlockNum D ρ j is nonempty since it contains the i-th entry
  have hmemblk : (deepPathV E).get ⟨i, hilen⟩ ∈ deepBlockNum D ρ j :=
    deepPathV_get_mem_deepBlockNum D ρ i hilen
  -- the block equals the head block of residualIter; nonempty ⇒ residual head exists
  have hheadeq : deepBlockNum D ρ j
      = (deepPathV (residualIter E j)).take (deepBlockLens (residualIter E j)).headI :=
    deepResidual_head D ρ j
  have hresne : residualIter E j ≠ [] := by
    intro hnil
    rw [hnil] at hheadeq
    rw [show deepPathV ([] : DNF n) = [] from by rw [deepPathV]] at hheadeq
    simp only [List.take_nil] at hheadeq
    rw [hheadeq] at hmemblk
    exact absurd hmemblk (List.not_mem_nil _)
  obtain ⟨Cr, rest', hhead⟩ : ∃ Cr rest', residualIter E j = Cr :: rest' := by
    cases hR : residualIter E j with
    | nil => exact absurd hR hresne
    | cons Cr rest' => exact ⟨Cr, rest', rfl⟩
  -- Cr = enteredTerm D ρ j
  have hCrent : Cr = enteredTerm D ρ j := by unfold enteredTerm; rw [hhead]; rfl
  -- deep var v ∈ (deepBlockNum j).map fst
  have hvmem : ((deepPathV E).get ⟨i, hilen⟩).1 ∈ (deepBlockNum D ρ j).map Prod.fst :=
    List.mem_map_of_mem Prod.fst hmemblk
  -- (deepBlockNum j).map fst = (enteredTerm D ρ j).map var = Cr.map var
  rw [← enteredTerm_map_var_eq] at hvmem
  rw [← hCrent] at hvmem
  -- v ∈ Cr.map var ⇒ ∃ l ∈ Cr, l.var = v ; l ∈ C₀ = survTerm ; v ∈ survTerm.map var
  rw [List.mem_map] at hvmem
  obtain ⟨l, hlCr, hlv⟩ := hvmem
  obtain ⟨_, hcombsurv⟩ := survTerm_spec D s ρ hD j Cr rest' hhead
  have hlC₀ : l ∈ survTerm D s ρ j :=
    termRestrict_mem_of_mem (combRestr D ρ j) (survTerm D s ρ j) Cr hcombsurv l hlCr
  rw [List.mem_map]
  exact ⟨l, hlC₀, hlv⟩

/-! ## 3. The ORIGINAL-INDEX encode `codeOrig` and the column-read correctness -/

/-- The i-th deep variable, total form (defaulting out of range via `getElem?`). -/
noncomputable def deepVarAt {n : Nat} (D : DNF n) (ρ : Restriction n) (i : Nat) : Option (Fin n) :=
  ((deepPathV (dnfRestrict ρ D)).map Prod.fst)[i]?

/-- The recorded **original index** of the i-th deep variable within its block's survivor
term: the index in `(survTerm D s ρ (block i)).map var` of the i-th deep variable.
Defaults to `0` out of range (never hit on the bad set with `i < s`). -/
noncomputable def origIdxAt {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) (i : Nat) :
    Nat :=
  match deepVarAt D ρ i with
  | some v =>
      ((survTerm D s ρ (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i)).map (·.var)).indexOf v
  | none => 0

/-- `deepVarAt` at an in-range index `i < s` (bad `ρ`) is the i-th deep variable. -/
theorem deepVarAt_eq {n : Nat} (D : DNF n) (s ℓ : Nat) (ρ : Restriction n)
    (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s) :
    deepVarAt D ρ i
      = some (((deepPathV (dnfRestrict ρ D)).get
          ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1) := by
  unfold deepVarAt
  have hilen : i < (deepPathV (dnfRestrict ρ D)).length := lt_deepPathV_length_of_bad hρ hi
  rw [List.getElem?_map, List.getElem?_eq_getElem hilen, List.get_eq_getElem]
  rfl

/-- **The recorded original index is `< widthDNF D` (budget preserved, PROVED).**  For a bad
`ρ` and `i < s`, `origIdxAt D s ρ i < widthDNF D`: it is the `indexOf` of the i-th deep
variable, which is PRESENT in `(survTerm).map var` (by `deepVar_mem_survTerm_map`), so the
index is `< (survTerm).length = termWidth (survTerm) ≤ widthDNF D` (`survTerm ∈ D`). -/
theorem origIdxAt_lt_width {n : Nat} (D : DNF n) (s ℓ : Nat) (ρ : Restriction n)
    (hD : SimpleDNF D) (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s) :
    origIdxAt D s ρ i < widthDNF D := by
  unfold origIdxAt
  rw [deepVarAt_eq D s ℓ ρ hρ i hi]
  simp only []
  set j := blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i with hj
  set v := ((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1 with hv
  have hvmem : v ∈ (survTerm D s ρ j).map (·.var) := by
    rw [hv, hj]; exact deepVar_mem_survTerm_map D s ℓ ρ hD hρ i hi
  -- residual at j nonempty ⇒ survTerm ∈ D
  have hilen : i < (deepPathV (dnfRestrict ρ D)).length := lt_deepPathV_length_of_bad hρ hi
  have hmemblk : (deepPathV (dnfRestrict ρ D)).get ⟨i, hilen⟩ ∈ deepBlockNum D ρ j := by
    rw [hj]; exact deepPathV_get_mem_deepBlockNum D ρ i hilen
  have hheadeq : deepBlockNum D ρ j
      = (deepPathV (residualIter (dnfRestrict ρ D) j)).take
          (deepBlockLens (residualIter (dnfRestrict ρ D) j)).headI :=
    deepResidual_head D ρ j
  have hresne : residualIter (dnfRestrict ρ D) j ≠ [] := by
    intro hnil
    rw [hnil, show deepPathV ([] : DNF n) = [] from by rw [deepPathV]] at hheadeq
    simp only [List.take_nil] at hheadeq
    rw [hheadeq] at hmemblk; exact absurd hmemblk (List.not_mem_nil _)
  obtain ⟨Cr, rest', hhead⟩ : ∃ Cr rest', residualIter (dnfRestrict ρ D) j = Cr :: rest' := by
    cases hR : residualIter (dnfRestrict ρ D) j with
    | nil => exact absurd hR hresne
    | cons Cr rest' => exact ⟨Cr, rest', rfl⟩
  obtain ⟨hmemD, _⟩ := survTerm_spec D s ρ hD j Cr rest' hhead
  -- indexOf < length of the mapped list = termWidth survTerm ≤ widthDNF D
  have hidx_lt : ((survTerm D s ρ j).map (·.var)).indexOf v
      < ((survTerm D s ρ j).map (·.var)).length :=
    List.indexOf_lt_length.mpr hvmem
  rw [List.length_map] at hidx_lt
  have hwle : termWidth (survTerm D s ρ j) ≤ widthDNF D := termWidth_le_widthDNF hmemD
  unfold termWidth at hwle
  omega

/-- **THE COLUMN READ (PROVED).**  For a bad `ρ` and `i < s`, reading the survivor term at
the recorded ORIGINAL index returns exactly the i-th deep variable:
`colVar (survTerm D s ρ (block i)) (origIdxAt D s ρ i) = [i-th deep var]`.  Direct from
`getElem?_indexOf_self` (the deep var is present in `(survTerm).map var`) — NO column
agreement / deep-order wall, because the index is the ORIGINAL index in `survTerm`. -/
theorem origColRead {n : Nat} (D : DNF n) (s ℓ : Nat) (ρ : Restriction n)
    (hD : SimpleDNF D) (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s) :
    colVar (survTerm D s ρ (blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i))
        (origIdxAt D s ρ i)
      = [((deepPathV (dnfRestrict ρ D)).get
          ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1] := by
  set j := blockIndexOfIndex (deepBlockLens (dnfRestrict ρ D)) i with hj
  set v := ((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1 with hv
  have hvmem : v ∈ (survTerm D s ρ j).map (·.var) := by
    rw [hv, hj]; exact deepVar_mem_survTerm_map D s ℓ ρ hD hρ i hi
  unfold colVar
  -- origIdxAt = indexOf v in (survTerm j).map var
  have horig : origIdxAt D s ρ i = ((survTerm D s ρ j).map (·.var)).indexOf v := by
    unfold origIdxAt
    rw [deepVarAt_eq D s ℓ ρ hρ i hi]
  rw [horig]
  rw [getElem?_indexOf_self _ v hvmem]
  rfl

/-! ## 4. The full-code encode `codeOrig` and the boundary-truncating decoder

Because the boundary truncation needs the ENTIRE `last`-bit sequence (not a single code
entry), we work at the full-code level (`RCodeRecoverable`'s interface), re-proving the
injection/card bound for `codeOrig` directly (reusing `card_le_mul_rcode_of_injOn`). -/

/-- The ORIGINAL-INDEX per-term code: the within-survivor-term ORIGINAL index (`Fin w`,
budget `< widthDNF D ≤ w` by `origIdxAt_lt_width`), the SAME per-term partition `last`-bit
as `codeRC` (`isLastInBlock`), and the SAME deep direction as `codeRC`. -/
noncomputable def codeOrig {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) : RCode s w :=
  fun i =>
    (⟨origIdxAt D s ρ i.1 % w, Nat.mod_lt _ hw⟩,
     isLastInBlock (deepBlockLens (dnfRestrict ρ D)) i.1,
     (codeLoc D w s hw ρ i).2)

/-- The `last`-bit predicate read off a full code (total `Nat → Bool`, `false` out of
range). -/
def codeLastBits {s w : Nat} (code : RCode s w) : Nat → Bool :=
  fun m => if hm : m < s then (code ⟨m, hm⟩).2.1 else false

/-- **The boundary-truncating ρ-INDEPENDENT decoder fold.**  At position `i`, truncate the
recovered prefix `prev` back to its block boundary (`blockStartFromBits` of the code's
`last`-bits), identify the survivor `C₀` by `firstNonFalsified` at that boundary, read its
`(code i).1`-th ORIGINAL-index variable, and append it paired with the code's direction. -/
noncomputable def origVarFold {n : Nat} (D : DNF n) (σ : Restriction n) (s w : Nat)
    (code : RCode s w) : Nat → List (Fin n × Bool)
  | 0 => []
  | (i + 1) =>
      let prev := origVarFold D σ s w code i
      if h : i < s then
        let start := blockStartFromBits (codeLastBits code) i
        let surv := (firstNonFalsified D (stateAt σ (prev.take start))).getD []
        prev ++ (colVar surv (code ⟨i, h⟩).1.val).map (fun v => (v, (code ⟨i, h⟩).2.2))
      else prev

theorem origVarFold_succ {n : Nat} (D : DNF n) (σ : Restriction n) (s w : Nat)
    (code : RCode s w) (i : Nat) (h : i < s) :
    origVarFold D σ s w code (i + 1)
      = origVarFold D σ s w code i
          ++ (colVar ((firstNonFalsified D (stateAt σ
                ((origVarFold D σ s w code i).take
                  (blockStartFromBits (codeLastBits code) i)))).getD [])
                (code ⟨i, h⟩).1.val).map (fun v => (v, (code ⟨i, h⟩).2.2)) := by
  conv_lhs => rw [origVarFold]
  simp only [h, dif_pos]

/-! ## 5. The decoder reconstructs the deep-path prefix (the assembled correctness) -/

/-- `codeLastBits (codeOrig …) m = isLastInBlock bs m` for `m < s`. -/
theorem codeLastBits_codeOrig {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) (m : Nat) (hm : m < s) :
    codeLastBits (codeOrig D w s hw ρ) m
      = isLastInBlock (deepBlockLens (dnfRestrict ρ D)) m := by
  unfold codeLastBits codeOrig
  simp only [hm, dif_pos]

/-- The direction recorded by `codeOrig` at `i` is the i-th deep direction (`codeLoc.2`
matches `codeOf.2 = deep dir`). -/
theorem codeOrig_dir {n : Nat} (D : DNF n) (w s ℓ : Nat) (hw : 0 < w)
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s) :
    (codeOrig D w s hw ρ ⟨i, hi⟩).2.2
      = ((deepPathV (dnfRestrict ρ D)).get ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).2 := by
  have hd := codeOf_snd_eq_deepPathV (D := D) hw hρ hi
  unfold codeOrig
  show (codeLoc D w s hw ρ ⟨i, hi⟩).2 = _
  unfold codeLoc
  rw [hd]

/-- The column field of `codeOrig` at `i` is `origIdxAt` (the `% w` is the identity since
`origIdxAt < widthDNF D ≤ w`). -/
theorem codeOrig_col {n : Nat} (D : DNF n) (w s ℓ : Nat) (hw : 0 < w)
    (hwD : widthDNF D ≤ w) {ρ : Restriction n} (hD : SimpleDNF D)
    (hρ : ρ ∈ badSetTerm D s ℓ) (i : Nat) (hi : i < s) :
    (codeOrig D w s hw ρ ⟨i, hi⟩).1.val = origIdxAt D s ρ i := by
  unfold codeOrig
  simp only []
  have hlt : origIdxAt D s ρ i < w :=
    lt_of_lt_of_le (origIdxAt_lt_width D s ℓ ρ hD hρ i hi) hwD
  exact Nat.mod_eq_of_lt hlt

/-- **The decoder reconstructs the deep-path prefix (PROVED).**  For a bad `ρ` with
`widthDNF D ≤ w`, `origVarFold D (encodeEnt₁ D s ρ) s w (codeOrig D w s hw ρ) i =
(deepPathV (D|ρ)).take i` for every `i ≤ s`.  The boundary truncation recovers the block
start ρ-independently; the survivor identification is `firstNonFalsified_eq_survivor` (via
`survTerm`); the column read is the original-index lemma `origColRead`; the direction is
the code's third component. -/
theorem origVarFold_eq_take {n : Nat} (D : DNF n) (w s ℓ : Nat) (hw : 0 < w)
    (hwD : widthDNF D ≤ w) (hD : SimpleDNF D) {ρ : Restriction n}
    (hρ : ρ ∈ badSetTerm D s ℓ) :
    ∀ i, i ≤ s →
      origVarFold D (encodeEnt₁ D s ρ) s w (codeOrig D w s hw ρ) i
        = (deepPathV (dnfRestrict ρ D)).take i
  | 0, _ => by simp [origVarFold]
  | (i + 1), hile => by
      have hi : i < s := by omega
      have hilen : i < (deepPathV (dnfRestrict ρ D)).length := lt_deepPathV_length_of_bad hρ hi
      rw [origVarFold_succ D (encodeEnt₁ D s ρ) s w (codeOrig D w s hw ρ) i hi]
      -- IH: the recovered prefix is take i
      rw [origVarFold_eq_take D w s ℓ hw hwD hD hρ i (by omega)]
      -- the block start computed from the code's last-bits equals startLen bs (block i)
      set bs := deepBlockLens (dnfRestrict ρ D) with hbs
      set j := blockIndexOfIndex bs i with hj
      have hsum : i < bs.sum := by rw [hbs, deepBlockLens_sum_eq]; exact hilen
      have hbits : ∀ m, m < i →
          codeLastBits (codeOrig D w s hw ρ) m = (fun m => isLastInBlock bs m) m := by
        intro m hm
        have hms : m < s := by omega
        rw [codeLastBits_codeOrig D w s hw ρ m hms]
      have hstart_eq : blockStartFromBits (codeLastBits (codeOrig D w s hw ρ)) i
          = startLen bs j := by
        rw [blockStartFromBits_congr (codeLastBits (codeOrig D w s hw ρ))
            (fun m => isLastInBlock bs m) i hbits]
        rw [blockStartFromBits_eq_startLen bs (deepBlockLens_pos _) i hsum]
      rw [hstart_eq]
      -- truncate the recovered prefix (take i) to the boundary (start j)
      have hstart_le : startLen bs j ≤ i := by
        have hk := startLen_blockIndex_add_blockPos bs i
        rw [← hj] at hk; omega
      have htrunc : ((deepPathV (dnfRestrict ρ D)).take i).take (startLen bs j)
          = (deepPathV (dnfRestrict ρ D)).take (startLen bs j) := by
        rw [List.take_take, Nat.min_eq_left hstart_le]
      rw [htrunc]
      -- the survivor identified at the boundary is survTerm
      have hsurv : (firstNonFalsified D (stateAt (encodeEnt₁ D s ρ)
            ((deepPathV (dnfRestrict ρ D)).take (startLen bs j)))).getD []
          = survTerm D s ρ j := by
        rw [hbs]; rfl
      rw [hsurv]
      -- column read
      have hcol_field : (codeOrig D w s hw ρ ⟨i, hi⟩).1.val = origIdxAt D s ρ i :=
        codeOrig_col D w s ℓ hw hwD hD hρ i hi
      rw [hcol_field]
      have hread : colVar (survTerm D s ρ j) (origIdxAt D s ρ i)
          = [((deepPathV (dnfRestrict ρ D)).get ⟨i, hilen⟩).1] := by
        have := origColRead D s ℓ ρ hD hρ i hi
        rw [← hj] at this
        rw [this]
      rw [hread]
      -- direction
      have hdir : (codeOrig D w s hw ρ ⟨i, hi⟩).2.2
          = ((deepPathV (dnfRestrict ρ D)).get ⟨i, hilen⟩).2 := by
        have := codeOrig_dir D w s ℓ hw hρ i hi
        exact this
      rw [hdir]
      -- assemble: take i ++ [(v, d)] = take (i+1)
      simp only [List.map_cons, List.map_nil]
      have hentry : (((deepPathV (dnfRestrict ρ D)).get ⟨i, hilen⟩).1,
                      ((deepPathV (dnfRestrict ρ D)).get ⟨i, hilen⟩).2)
                    = (deepPathV (dnfRestrict ρ D)).get ⟨i, hilen⟩ := by rw [Prod.mk.eta]
      rw [hentry, List.get_eq_getElem]
      exact (List.take_succ_append_getElem _ i hilen).symm

/-! ## 6. The `encodeEnt₁` injection backbone (mirrors the proved `encodeLoc₁` one) -/

/-- `encodeEnt₁` is `none` exactly on stars of `ρ` that are NOT touched (same support as
`encodeLoc₁`).  Mirrors `encodeLoc₁_eq_none_iff` via `satRestrEnt`'s support facts. -/
theorem encodeEnt₁_eq_none_iff {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) :
    encodeEnt₁ D s ρ v = none ↔ (ρ v = none ∧ v ∉ touchedVars D s ρ) := by
  unfold encodeEnt₁ overlay
  cases hτ : satRestrEnt D s ρ v with
  | some d =>
      simp only [hτ]
      have hin : v ∈ touchedVars D s ρ := by
        by_contra hc
        rw [(satRestrEnt_eq_none_iff D s ρ v).mpr hc] at hτ; exact absurd hτ (by simp)
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨_, hnt⟩; exact absurd hin hnt
  | none =>
      simp only [hτ]
      have hnt : v ∉ touchedVars D s ρ := (satRestrEnt_eq_none_iff D s ρ v).mp hτ
      constructor
      · intro h; exact ⟨h, hnt⟩
      · rintro ⟨h, _⟩; exact h

/-- `encodeEnt₁` agrees with `ρ` off the touched set. -/
theorem encodeEnt₁_eq_ρ_of_not_touched {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n)
    (v : Fin n) (hv : v ∉ touchedVars D s ρ) : encodeEnt₁ D s ρ v = ρ v := by
  unfold encodeEnt₁ overlay
  rw [(satRestrEnt_eq_none_iff D s ρ v).mpr hv]

/-- **`ρ` is determined by `encodeEnt₁ ρ` and the touched set (PROVED).**  Mirrors
`ρ_eq_of_encodeLoc`. -/
theorem ρ_eq_of_encodeEnt₁ {n : Nat} (D : DNF n) (s : Nat) (ρ : Restriction n) :
    ρ = fun v => if v ∈ touchedVars D s ρ then none else encodeEnt₁ D s ρ v := by
  funext v
  by_cases hv : v ∈ touchedVars D s ρ
  · simp only [if_pos hv]; exact touchedVars_free D s ρ v hv
  · simp only [if_neg hv]; exact (encodeEnt₁_eq_ρ_of_not_touched D s ρ v hv).symm

/-- **Star count of `encodeEnt₁ ρ` is `ℓ - s` (PROVED).**  Mirrors `stars_encodeLoc₁`. -/
theorem stars_encodeEnt₁ {n : Nat} {D : DNF n} (hD : SimpleDNF D) {s ℓ : Nat}
    {ρ : Restriction n} (hρ : ρ ∈ badSetTerm D s ℓ) :
    stars (encodeEnt₁ D s ρ) = ℓ - s := by
  classical
  have hstarsρ : stars ρ = ℓ := ((mem_badSetTerm ρ).mp hρ).1
  set Tf : Finset (Fin n) := (touchedVars D s ρ).toFinset with hTf
  have hsub : Tf ⊆ Finset.univ.filter (fun v => ρ v = none) := by
    intro v hv
    rw [hTf, List.mem_toFinset] at hv
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, touchedVars_free D s ρ v hv⟩
  have hσset : (Finset.univ.filter (fun v => encodeEnt₁ D s ρ v = none))
      = (Finset.univ.filter (fun v => ρ v = none)) \ Tf := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      hTf, List.mem_toFinset]
    rw [encodeEnt₁_eq_none_iff]
  unfold stars
  rw [hσset, Finset.card_sdiff hsub, touched_finset_card hD hρ]
  have : (Finset.univ.filter (fun v => ρ v = none)).card = ℓ := by
    rw [← hstarsρ]; rfl
  rw [this]

/-! ## 7. The recovery and the final theorem -/

/-- **The ORIGINAL-INDEX touched-set recovery (PROVED).**  For a bad `ρ` with `widthDNF D ≤
w`, the touched-variable SET is recovered ρ-INDEPENDENTLY from `encodeEnt₁ D s ρ` and the
ORIGINAL-index per-term code `codeOrig`: run the boundary-truncating fold for `s` steps and
take the variables.  This is the `RCodeRecoverable`-analogue, proved OUTRIGHT (the column
read `origColRead` + the survivor identification `firstNonFalsified_eq_survivor` close it). -/
theorem origRecovery {n : Nat} (D : DNF n) (w s ℓ : Nat) (hw : 0 < w) (hwD : widthDNF D ≤ w)
    (hD : SimpleDNF D) (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D s ℓ) :
    ((origVarFold D (encodeEnt₁ D s ρ) s w (codeOrig D w s hw ρ) s).map Prod.fst).toFinset
      = (touchedVars D s ρ).toFinset := by
  have hfold : origVarFold D (encodeEnt₁ D s ρ) s w (codeOrig D w s hw ρ) s
      = (deepPathV (dnfRestrict ρ D)).take s :=
    origVarFold_eq_take D w s ℓ hw hwD hD hρ s (le_refl s)
  rw [hfold, ← touchedVars_eq_deepPathV D s ρ]

/-- The full ORIGINAL-INDEX **encode**: `encodeEnt₁` paired with the original-index code. -/
noncomputable def encodeOrig {n : Nat} (D : DNF n) (w s : Nat) (hw : 0 < w)
    (ρ : Restriction n) : Restriction n × RCode s w :=
  (encodeEnt₁ D s ρ, codeOrig D w s hw ρ)

/-- **THE FINAL THEOREM (PROVED): the term switching lemma for simple DNFs.**  The
ORIGINAL-INDEX encode `encodeOrig` is injective on the bad set: its first coordinate
`encodeEnt₁` determines `ρ` together with the touched set (`ρ_eq_of_encodeEnt₁`), the
touched set is recovered ρ-independently from `(encodeEnt₁, codeOrig)` by `origRecovery`,
and the first coordinate lands in the `(ℓ-s)`-star set (`stars_encodeEnt₁`).  The per-term
code card `(4w)^s ≤ (8w)^s` closes the count (`card_le_mul_rcode_of_injOn`).  The column
read (G1) is dissolved by recording the ORIGINAL index; the mid-block prefix (G2) is
dissolved by boundary truncation.  NO `sorry`, NO new axiom. -/
theorem switchingLemmaTermSimple_proved {n : Nat} : SwitchingLemmaTermSimple n := by
  intro D w s ℓ hD hwD
  classical
  by_cases hw : 0 < w
  · have hmem : ∀ ρ ∈ badSetTerm D s ℓ,
        (encodeOrig D w s hw ρ).1 ∈ restrictionsWithStars n (ℓ - s) := by
      intro ρ hρ
      rw [mem_restrictionsWithStars]; exact stars_encodeEnt₁ hD hρ
    have hinj : Set.InjOn (encodeOrig D w s hw) ↑(badSetTerm D s ℓ) := by
      intro ρ hρ ρ' hρ' heq
      have hρmem : ρ ∈ badSetTerm D s ℓ := by simpa using hρ
      have hρ'mem : ρ' ∈ badSetTerm D s ℓ := by simpa using hρ'
      have hσ : encodeEnt₁ D s ρ = encodeEnt₁ D s ρ' := congrArg Prod.fst heq
      have hcode : codeOrig D w s hw ρ = codeOrig D w s hw ρ' := congrArg Prod.snd heq
      have ht : (touchedVars D s ρ).toFinset = (touchedVars D s ρ').toFinset := by
        rw [← origRecovery D w s ℓ hw hwD hD ρ hρmem,
            ← origRecovery D w s ℓ hw hwD hD ρ' hρ'mem, hσ, hcode]
      rw [ρ_eq_of_encodeEnt₁ D s ρ, ρ_eq_of_encodeEnt₁ D s ρ']
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
    exact card_le_mul_rcode_of_injOn (badSetTerm D s ℓ) (restrictionsWithStars n (ℓ - s))
      w s (encodeOrig D w s hw) hmem hinj
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

end SwitchingClose2
end PvNP
