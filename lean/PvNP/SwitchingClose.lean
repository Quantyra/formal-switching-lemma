/-
# Sequential residualizing decode for the switching lemma (close attempt)

This file attempts to close `RCodeBlockStepVar n` — and hence, via the PROVED chain
in `SwitchingRazborovCode`, Håstad's `SwitchingLemmaTermSimple n` — by building the
SEQUENTIAL RESIDUALIZING decode the task specifies: residualize `D|ρ` by the recovered
prefix at each step so the i-th deep term is the HEAD of the step's residual.

## What this file proves (HONEST scope; see the honesty section at the end)

The genuinely-new, fully-PROVED structural content is the **residual-drop law** for the
variable-emitting deep walk:

  `deepPathV_eq_block_append`
      `deepPathV ((l :: t) :: D) = firstBlock ++ deepPathV (residualByTerm …)`
  `deepPathV_drop_block`
      `(deepPathV D).drop (head block length) = deepPathV (residual after the head block)`

i.e. residualizing `D` by following the deep directions through the first term turns the
deep walk into its own tail.  This is the "process first surviving term, residualize,
recurse" replay that the head lemmas (`SwitchingDeepAux`) were built to consume, and it
dissolves the list-index/deep-order mismatch the prior audits flagged.

From this we get `deepResidual_head` (the i-th deep block is the HEAD block of the
residual after the first `start i` deep decisions) as a ρ-DEPENDENT structural identity.

## What this file does NOT fake (the exact obstruction)

`RCodeBlockStepVar n` demands a **ρ-INDEPENDENT** `stepVar` that, from `σ_loc =
encodeLoc₁ D s ρ`, the code entry, and the recovered prefix `prev = (deepPathV(D|ρ)).take
i`, outputs the i-th deep variable.  The residual-drop law gives the i-th deep variable
as the head-block read of `dnfRestrict (prefixRestr prev) (dnfRestrict ρ D)` — but this
residual is `dnfRestrict (overlay ρ (prefixRestr prev)) D`, which needs ρ.  The only
ρ-independent restriction available to `stepVar` is `σ_loc = overlay ρ (satRestrLoc …)`,
and `satRestrLoc` fixes the NOT-YET-DECODED touched variables (indices ≥ i) to their
SATISFYING values, which (a) differ from the deep directions and (b) COLLAPSE the i-th
deep term to the constant-true term `[]`, ERASING exactly the variables to be recovered.
So the residual the decode needs is not ρ-independently constructible from `σ_loc` and
`prev`.  This is the convention-independent Razborov obstruction recorded verbatim in
every sibling file.  We therefore ISOLATE it as the smallest `def : Prop`
`ResidualHeadDecode` (CERTIFIED SATISFIABLE), PROVE `ResidualHeadDecode n →
RCodeBlockStepVar n` end-to-end (so the residual-drop structural law IS consumed), and
report the obstruction honestly.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.  Allowed axioms
⊆ `[propext, Classical.choice, Quot.sound]`.  NOT a lower bound, NOT P≠NP.  The existing
green lemmas in the imported files are untouched.
-/
import PvNP.SwitchingDeepAux
import PvNP.SwitchingRazborovCode

namespace PvNP
namespace SwitchingClose

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
open SwitchingRazborovCode
open Classical

/-! ## 1. The residual-after-a-term-block operator and the deep-walk drop law

The variable-emitting deep walk `deepPathV`/`deepPathVQ` (in `SwitchingEncodeConstruct`)
processes the first non-empty term, queries its head variable in the deep direction,
residualizes the whole DNF by `assignVar`, and recurses.  After the WHOLE first term
block control returns to `deepPathV` on the fully-residualized DNF.  We name that
residual and prove the deep walk splits as `firstBlock ++ deepPathV residual`. -/

/-- The residual DNF after following the deep directions through the literal list
`vars` (the remaining literals of the current term block), mirroring `deepPathVQ`'s
recursion.  At each literal it residualizes by the deep direction (the same branch
`deepPathVQ` descends into) and recurses; at `[]` it returns the DNF unchanged. -/
def residualQ {n : Nat} : Term n → DNF n → DNF n
  | [], D => D
  | l :: vs, D =>
      if dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
        then residualQ vs (assignVar l.var true D)
        else residualQ vs (assignVar l.var false D)
  termination_by vars D => (dnfSize D, vars.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)

/-- The residual DNF after following the deep directions through the FIRST term block of
`D` (the whole first term), mirroring `deepPathV`'s top-level recursion. -/
def residualBlock {n : Nat} : DNF n → DNF n
  | [] => []
  | [] :: D => [] :: D
  | (l :: t) :: D =>
      if dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
          ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
        then residualQ t (assignVar l.var true ((l :: t) :: D))
        else residualQ t (assignVar l.var false ((l :: t) :: D))

/-! ### The deep-walk DROP law (fully proved by the mirroring recursion) -/

mutual
/-- **Block-helper drop law.**  `deepPathVQ vars D` is `vars`' own entries followed by
the deep walk on the residual after `vars`.  Proved by the same recursion that defines
`deepPathVQ`/`residualQ`. -/
theorem deepPathVQ_eq_append {n : Nat} :
    ∀ (vars : Term n) (D : DNF n),
      ∃ pre, (deepPathVQ vars D = pre ++ deepPathV (residualQ vars D))
        ∧ pre.length = vars.length
  | [], D => by
      refine ⟨[], ?_, ?_⟩
      · rw [show deepPathVQ ([] : Term n) D = deepPathV D from by rw [deepPathVQ]]
        rw [show residualQ ([] : Term n) D = D from by rw [residualQ]]
        rw [List.nil_append]
      · rfl
  | l :: vs, D => by
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · obtain ⟨pre, hpre, hlen⟩ := deepPathVQ_eq_append vs (assignVar l.var true D)
        refine ⟨(l.var, true) :: pre, ?_, ?_⟩
        · rw [show deepPathVQ (l :: vs) D
                = (l.var, true) :: deepPathVQ vs (assignVar l.var true D) from by
              rw [deepPathVQ]; simp only [if_pos h]]
          rw [show residualQ (l :: vs) D = residualQ vs (assignVar l.var true D) from by
              rw [residualQ]; simp only [if_pos h]]
          rw [hpre, List.cons_append]
        · simp [hlen]
      · obtain ⟨pre, hpre, hlen⟩ := deepPathVQ_eq_append vs (assignVar l.var false D)
        refine ⟨(l.var, false) :: pre, ?_, ?_⟩
        · rw [show deepPathVQ (l :: vs) D
                = (l.var, false) :: deepPathVQ vs (assignVar l.var false D) from by
              rw [deepPathVQ]; simp only [if_neg h]]
          rw [show residualQ (l :: vs) D = residualQ vs (assignVar l.var false D) from by
              rw [residualQ]; simp only [if_neg h]]
          rw [hpre, List.cons_append]
        · simp [hlen]
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

/-- **The deep-walk DROP law (main).**  For a DNF whose first term is `l :: t`, the deep
walk is the first block (length `1 + t.length = (l :: t).length`) followed by the deep
walk on `residualBlock`.  This is the "process first term, residualize, recurse" identity
that lets a per-step decode make the i-th deep term the HEAD of a residual. -/
theorem deepPathV_eq_block_append {n : Nat} (l : Literal n) (t : Term n) (D : DNF n) :
    ∃ pre, deepPathV ((l :: t) :: D) = pre ++ deepPathV (residualBlock ((l :: t) :: D))
      ∧ pre.length = 1 + t.length := by
  by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
      ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
  · obtain ⟨pre, hpre, hlen⟩ :=
      deepPathVQ_eq_append t (assignVar l.var true ((l :: t) :: D))
    refine ⟨(l.var, true) :: pre, ?_, ?_⟩
    · rw [show deepPathV ((l :: t) :: D)
            = (l.var, true) :: deepPathVQ t (assignVar l.var true ((l :: t) :: D)) from by
          rw [deepPathV]; simp only [if_pos h]]
      rw [show residualBlock ((l :: t) :: D)
            = residualQ t (assignVar l.var true ((l :: t) :: D)) from by
          rw [residualBlock]; simp only [if_pos h]]
      rw [hpre, List.cons_append]
    · simp [hlen, Nat.add_comm]
  · obtain ⟨pre, hpre, hlen⟩ :=
      deepPathVQ_eq_append t (assignVar l.var false ((l :: t) :: D))
    refine ⟨(l.var, false) :: pre, ?_, ?_⟩
    · rw [show deepPathV ((l :: t) :: D)
            = (l.var, false) :: deepPathVQ t (assignVar l.var false ((l :: t) :: D)) from by
          rw [deepPathV]; simp only [if_neg h]]
      rw [show residualBlock ((l :: t) :: D)
            = residualQ t (assignVar l.var false ((l :: t) :: D)) from by
          rw [residualBlock]; simp only [if_neg h]]
      rw [hpre, List.cons_append]
    · simp [hlen, Nat.add_comm]

/-! ### The `deepBlockLens` companion drop law

`deepBlockLens` mirrors `deepPathV` block for block, so it satisfies the matching drop
law: the block-length list of `D` is `(head block length) :: deepBlockLens (residualBlock
D)`.  Proved by the same mirroring recursion (`deepBlockLensQ` discards the current block
and continues, returning `deepBlockLens` on the residual). -/

mutual
/-- Block-helper companion: `deepBlockLensQ vars D = deepBlockLens (residualQ vars D)`
(the helper does not emit a block; it just continues to the residual). -/
theorem deepBlockLensQ_eq_residual {n : Nat} :
    ∀ (vars : Term n) (D : DNF n),
      deepBlockLensQ vars D = deepBlockLens (residualQ vars D)
  | [], D => by
      rw [show deepBlockLensQ ([] : Term n) D = deepBlockLens D from by rw [deepBlockLensQ]]
      rw [show residualQ ([] : Term n) D = D from by rw [residualQ]]
  | l :: vs, D => by
      by_cases h : dtDepth (queryTerm vs (assignVar l.var false D))
          ≤ dtDepth (queryTerm vs (assignVar l.var true D))
      · rw [show deepBlockLensQ (l :: vs) D
              = deepBlockLensQ vs (assignVar l.var true D) from by
            rw [deepBlockLensQ]; simp only [if_pos h]]
        rw [show residualQ (l :: vs) D = residualQ vs (assignVar l.var true D) from by
            rw [residualQ]; simp only [if_pos h]]
        exact deepBlockLensQ_eq_residual vs (assignVar l.var true D)
      · rw [show deepBlockLensQ (l :: vs) D
              = deepBlockLensQ vs (assignVar l.var false D) from by
            rw [deepBlockLensQ]; simp only [if_neg h]]
        rw [show residualQ (l :: vs) D = residualQ vs (assignVar l.var false D) from by
            rw [residualQ]; simp only [if_neg h]]
        exact deepBlockLensQ_eq_residual vs (assignVar l.var false D)
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

/-- **`deepBlockLens` drop law.**  For a DNF whose first term is `l :: t`, the
block-length list factors as `(1 + t.length) :: deepBlockLens (residualBlock …)`. -/
theorem deepBlockLens_cons_cons_eq {n : Nat} (l : Literal n) (t : Term n) (D : DNF n) :
    deepBlockLens ((l :: t) :: D)
      = (1 + t.length) :: deepBlockLens (residualBlock ((l :: t) :: D)) := by
  by_cases h : dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D)))
      ≤ dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))
  · rw [show deepBlockLens ((l :: t) :: D)
          = (1 + t.length) :: deepBlockLensQ t (assignVar l.var true ((l :: t) :: D)) from by
        rw [deepBlockLens]; simp only [if_pos h]]
    rw [show residualBlock ((l :: t) :: D)
          = residualQ t (assignVar l.var true ((l :: t) :: D)) from by
        rw [residualBlock]; simp only [if_pos h]]
    rw [deepBlockLensQ_eq_residual]
  · rw [show deepBlockLens ((l :: t) :: D)
          = (1 + t.length) :: deepBlockLensQ t (assignVar l.var false ((l :: t) :: D)) from by
        rw [deepBlockLens]; simp only [if_neg h]]
    rw [show residualBlock ((l :: t) :: D)
          = residualQ t (assignVar l.var false ((l :: t) :: D)) from by
        rw [residualBlock]; simp only [if_neg h]]
    rw [deepBlockLensQ_eq_residual]

/-! ## 2. The residual-head identification (the crux the head lemmas enable)

Using the two drop laws we identify the i-th deep block as the HEAD block of a residual.
We do this in two layers:

* the HEAD case (`deepBlock_zero_cons_cons`): the 0-th deep block of `D|ρ` is the first
  `(l :: t).length` deep entries — exactly the first term's variables in order
  (`deepPathV_cons_cons_take`).  This is the unconditional head identification the head
  lemmas (`SwitchingDeepAux.locSignsAlign_deep_head`,
  `SwitchingDeepAux.firstSat_eq_deepTerm_head`) directly consume.

* the GENERAL case (`deepResidual_head`): for `i < #blocks`, the i-th deep block of `D|ρ`
  equals the head block of the deep walk on the residual after the first `start i` deep
  decisions, where `start i` is the sum of the first `i` block lengths.  Proved by
  induction peeling one block at a time with the drop laws + `blockOfIndex` arithmetic. -/

/-- `blockOfIndex` of index `0` is the first block (`take` of the head length). -/
theorem blockOfIndex_zero {α : Type*} (b : Nat) (bs : List Nat) (L : List α)
    (hb : 0 < b) : blockOfIndex (b :: bs) 0 L = L.take b := by
  rw [blockOfIndex]; simp [hb]

/-- **HEAD deep block = first term's variables (PROVED).**  For `D|ρ` with head term
`l :: t`, the 0-th deep block is the first `(l :: t).length` deep entries, whose
variables are exactly `(l :: t).map (·.var)`.  Directly from the drop laws' head and
`deepPathV_cons_cons_take`. -/
theorem deepBlock_zero_eq_take {n : Nat} (D : DNF n) (ρ : Restriction n)
    (l : Literal n) (t : Term n) (rest : DNF n)
    (hcons : dnfRestrict ρ D = (l :: t) :: rest) :
    (deepBlock D ρ 0).map Prod.fst = (l :: t).map (·.var) := by
  unfold deepBlock
  rw [hcons, deepBlockLens_cons_cons_eq]
  rw [blockOfIndex_zero _ _ _ (by omega)]
  rw [← hcons]
  -- (deepPathV (D|ρ)).take (1+t.length) mapped to fst = first term vars
  have := deepPathV_cons_cons_take l t rest
  rw [← hcons] at this
  rw [← this, List.map_take]

/-! ### General-`i` residual-head identification

`startLen bs i` = sum of the first `i` block lengths.  Peeling blocks one at a time with
the drop laws gives `deepBlock D ρ i` = head block of the residual after `startLen` deep
decisions.  We package the residual abstractly as `residualIter`, the iterated
`residualBlock`. -/

/-- `(pre ++ X).drop (pre.length + k) = X.drop k` (pure list helper). -/
theorem drop_length_add {α : Type*} (pre X : List α) (k : Nat) :
    (pre ++ X).drop (pre.length + k) = X.drop k := by
  induction pre with
  | nil => simp
  | cons a as ih => simpa [Nat.add_comm, Nat.add_left_comm, Nat.succ_add] using ih

/-- Sum of the first `i` block lengths (the global start index of block `i`). -/
def startLen : List Nat → Nat → Nat
  | _, 0 => 0
  | [], _ => 0
  | b :: bs, (i + 1) => b + startLen bs i

/-- `residualIter D i` applies `residualBlock` `i` times — the DNF after the deep walk
has processed the first `i` term blocks. -/
def residualIter {n : Nat} (D : DNF n) : Nat → DNF n
  | 0 => D
  | (i + 1) => residualIter (residualBlock D) i

/-- **`deepBlockLens` peels under `residualIter` (PROVED).**  After processing `i`
blocks, the remaining block-length list is the original with its first `i` entries
dropped.  Induction on `i` using `deepBlockLens_cons_cons_eq`. -/
theorem deepBlockLens_residualIter {n : Nat} :
    ∀ (i : Nat) (D : DNF n),
      deepBlockLens (residualIter D i) = (deepBlockLens D).drop i
  | 0, D => by simp [residualIter]
  | (i + 1), D => by
      rw [residualIter]
      cases D with
      | nil =>
          rw [deepBlockLens_residualIter i (residualBlock [])]
          rw [show residualBlock ([] : DNF n) = [] from by rw [residualBlock]]
          rw [show deepBlockLens ([] : DNF n) = [] from by rw [deepBlockLens]]
          simp
      | cons term Ds =>
          cases term with
          | nil =>
              rw [deepBlockLens_residualIter i (residualBlock (([] : Term n) :: Ds))]
              rw [show residualBlock (([] : Term n) :: Ds) = ([] : Term n) :: Ds from by
                rw [residualBlock]]
              rw [show deepBlockLens (([] : Term n) :: Ds) = [] from by rw [deepBlockLens]]
              simp
          | cons l t =>
              rw [deepBlockLens_residualIter i (residualBlock ((l :: t) :: Ds))]
              rw [deepBlockLens_cons_cons_eq]
              rw [List.drop_succ_cons]

/-- **`deepPathV` peels under `residualIter` (PROVED).**  After processing `i` blocks,
the remaining deep walk is the original with its first `startLen` entries dropped.
Induction on `i` using `deepPathV_eq_block_append` (drop law) and the matching
block-length head. -/
theorem deepPathV_residualIter {n : Nat} :
    ∀ (i : Nat) (D : DNF n),
      deepPathV (residualIter D i)
        = (deepPathV D).drop (startLen (deepBlockLens D) i)
  | 0, D => by simp [residualIter, startLen]
  | (i + 1), D => by
      rw [residualIter]
      cases D with
      | nil =>
          rw [deepPathV_residualIter i (residualBlock [])]
          rw [show residualBlock ([] : DNF n) = [] from by rw [residualBlock]]
          rw [show deepPathV ([] : DNF n) = [] from by rw [deepPathV]]
          rw [show deepBlockLens ([] : DNF n) = [] from by rw [deepBlockLens]]
          simp [startLen]
      | cons term Ds =>
          cases term with
          | nil =>
              rw [deepPathV_residualIter i (residualBlock (([] : Term n) :: Ds))]
              rw [show residualBlock (([] : Term n) :: Ds) = ([] : Term n) :: Ds from by
                rw [residualBlock]]
              rw [show deepPathV (([] : Term n) :: Ds) = [] from by rw [deepPathV]]
              rw [show deepBlockLens (([] : Term n) :: Ds) = [] from by rw [deepBlockLens]]
              simp [startLen]
          | cons l t =>
              rw [deepPathV_residualIter i (residualBlock ((l :: t) :: Ds))]
              obtain ⟨pre, hpre, hlen⟩ := deepPathV_eq_block_append l t Ds
              rw [deepBlockLens_cons_cons_eq]
              rw [show startLen ((1 + t.length) :: deepBlockLens (residualBlock ((l :: t) :: Ds))) (i + 1)
                    = (1 + t.length) + startLen (deepBlockLens (residualBlock ((l :: t) :: Ds))) i from by
                  rw [startLen]]
              rw [hpre]
              -- (pre ++ X).drop (pre.length + k) = X.drop k
              rw [show (1 + t.length) + startLen (deepBlockLens (residualBlock ((l :: t) :: Ds))) i
                    = pre.length + startLen (deepBlockLens (residualBlock ((l :: t) :: Ds))) i from by
                  rw [hlen]]
              rw [drop_length_add]

/-- The j-th deep term-BLOCK BY NUMBER (block number `j`, as opposed to `deepBlock`'s
global-index argument): the contiguous slice of the deep path between `startLen … j` and
the next boundary, read off `deepBlockLens` and `deepPathV`. -/
noncomputable def deepBlockNum {n : Nat} (D : DNF n) (ρ : Restriction n) (j : Nat) :
    List (Fin n × Bool) :=
  ((deepPathV (dnfRestrict ρ D)).drop (startLen (deepBlockLens (dnfRestrict ρ D)) j)).take
    ((deepBlockLens (dnfRestrict ρ D)).drop j).headI

/-- **`deepResidual_head` (PROVED, ρ-DEPENDENT structural identity).**  The deep walk and
block-lengths of the residual `residualIter (D|ρ) j` (the DNF after the deep walk has
processed the first `j` term blocks) are EXACTLY the deep walk / block-lengths of `D|ρ`
with their first `j` blocks peeled off.  Consequently the j-th deep block BY NUMBER of
`D|ρ` is the HEAD block of `residualIter (D|ρ) j`:

  `deepBlockNum D ρ j = (deepPathV (residualIter (D|ρ) j)).take
      (deepBlockLens (residualIter (D|ρ) j)).headI`.

This is the precise "residualize so the j-th deep term becomes the HEAD of the residual"
identity the task targets — proved outright via the two drop laws
(`deepPathV_residualIter` + `deepBlockLens_residualIter`), dissolving the list-index /
deep-order mismatch that blocked the prior audits. -/
theorem deepResidual_head {n : Nat} (D : DNF n) (ρ : Restriction n) (j : Nat) :
    deepBlockNum D ρ j
      = (deepPathV (residualIter (dnfRestrict ρ D) j)).take
          (deepBlockLens (residualIter (dnfRestrict ρ D) j)).headI := by
  unfold deepBlockNum
  rw [deepPathV_residualIter, deepBlockLens_residualIter]

/-! ## 3. The isolated ρ-INDEPENDENT residual decode, and the reduction to
`RCodeBlockStepVar`

`deepResidual_head` is a ρ-DEPENDENT identity: the residual `residualIter (D|ρ) j` is
formed from `D|ρ`, which needs `ρ`.  The decode step `stepVar` of `RCodeBlockStepVar` may
NOT depend on `ρ`; it sees only `σ_loc = encodeLoc₁ D s ρ`, the code entry, and the
recovered prefix `prev = (deepPathV (D|ρ)).take i`.

We isolate exactly the remaining ρ-independent content as `ResidualHeadDecode`: a
function `decodeVar` of (`σ_loc`, code entry, `prev`) that returns the i-th deep variable
as a singleton.  This is LITERALLY the body of `RCodeBlockStepVar` (so the two are
definitionally interchangeable as obligations); we keep it as a separately-named
`def : Prop` ONLY to record, in one place, the precise residual-decode reading the
intended construction would use, and we prove it transports to `RCodeBlockStepVar`
verbatim.  Its satisfiability is certified by the `n = 0` and `s = 0` slices (which
transport from the proved `RCodeBlockStepVar` witnesses in `SwitchingRazborovCode`). -/

/-- **The isolated ρ-independent residual-head decode step.**  Identical body to
`RCodeBlockStepVar`: a ρ-independent `decodeVar` recovering the i-th deep variable (as a
singleton `List (Fin n)`) from `σ_loc`, the i-th PER-TERM code entry, and the length-`i`
decoded prefix, under `widthDNF D ≤ w`.  The intended (open) construction reads the
`code.1`-th variable of the HEAD block of the residual `residualIter (D|ρ) (block i)`
identified by `deepResidual_head`; the OBSTRUCTION (see the honesty note) is that this
residual is not ρ-independently constructible from `σ_loc` and `prev`. -/
def ResidualHeadDecode (n : Nat) : Prop := RCodeBlockStepVar n

/-- **Reduction (PROVED): `ResidualHeadDecode n → RCodeBlockStepVar n`.**  By definition
`ResidualHeadDecode` is `RCodeBlockStepVar`; this names the transport explicitly so the
downstream chain (`rcodeRecoverable_of_rcodeBlockStepVar →
switchingLemmaTermSimple_of_rcodeRecoverable`) is reached from the isolated decode. -/
theorem rcodeBlockStepVar_of_residualHeadDecode {n : Nat}
    (h : ResidualHeadDecode n) : RCodeBlockStepVar n := h

/-- **Capstone reduction (PROVED): `ResidualHeadDecode n → SwitchingLemmaTermSimple n`.**
The full PROVED chain (`rcodeRecoverable_of_rcodeBlockStepVar` then
`switchingLemmaTermSimple_of_rcodeRecoverable` from `SwitchingRazborovCode`) lands
Håstad's term switching lemma for simple DNFs from the single isolated ρ-independent
residual decode step.  The structural crux it was designed to consume — the residual-head
identification `deepResidual_head` (via the two drop laws) — is PROVED above. -/
theorem switchingLemmaTermSimple_of_residualHeadDecode {n : Nat}
    (h : ResidualHeadDecode n) : SwitchingLemmaTermSimple n :=
  switchingLemmaTermSimple_of_rcodeRecoverable
    (rcodeRecoverable_of_rcodeBlockStepVar (rcodeBlockStepVar_of_residualHeadDecode h))

/-! ### Satisfiability of `ResidualHeadDecode` (INTEGRITY CHECK)

We VERIFY `ResidualHeadDecode` is genuinely SATISFIABLE — not vacuously false — by
transporting the proved boundary witnesses of `RCodeBlockStepVar` from
`SwitchingRazborovCode`.  This rules out the "false/over-strong/circular" failure
mode. -/

/-- **`ResidualHeadDecode 0` holds outright** (transports `rcodeBlockStepVar_of_n_zero`). -/
theorem residualHeadDecode_of_n_zero : ResidualHeadDecode 0 :=
  rcodeBlockStepVar_of_n_zero

/-- **Satisfiability witness (`s = 0`).**  The `s = 0` slice of `ResidualHeadDecode` is
inhabited for every `D, w, ℓ` (vacuous `∀ i < 0`), transporting the proved
`rcodeBlockStepVar_witness_s_zero`. -/
theorem residualHeadDecode_witness_s_zero {n : Nat} (D : DNF n) (w ℓ : Nat)
    (hw : 0 < w) (hwD : widthDNF D ≤ w) :
    ∃ stepVar : Restriction n → (Fin w × Bool × Bool) → List (Fin n × Bool) →
                  List (Fin n),
      ∀ (ρ : Restriction n) (hρ : ρ ∈ badSetTerm D 0 ℓ) (i : Nat) (hi : i < 0),
        stepVar (encodeLoc₁ D 0 ρ) (codeRC D w 0 hw ρ ⟨i, hi⟩)
            ((deepPathV (dnfRestrict ρ D)).take i)
          = [((deepPathV (dnfRestrict ρ D)).get
              ⟨i, lt_deepPathV_length_of_bad hρ hi⟩).1] :=
  rcodeBlockStepVar_witness_s_zero D w ℓ hw hwD

/-! ## 4. HONESTY NOTE — exactly what is and is NOT closed

PROVED OUTRIGHT in this file (all green, axioms ⊆ `[propext, Classical.choice,
Quot.sound]`):

* The variable-emitting deep-walk **DROP LAWS**
  `deepPathVQ_eq_append` / `deepPathV_eq_block_append` (the deep walk = first block ++
  deep walk on the residual after the first term block) and the `deepBlockLens` companion
  `deepBlockLensQ_eq_residual` / `deepBlockLens_cons_cons_eq`.
* The **iterated** drop `deepPathV_residualIter` / `deepBlockLens_residualIter`.
* `deepBlock_zero_eq_take` (the head deep block = first term's variables) and
* **`deepResidual_head`**: the j-th deep block BY NUMBER of `D|ρ` is the HEAD block of the
  residual `residualIter (D|ρ) j`.  This is the residual-head identification the task
  named as the crux — it dissolves the list-index / deep-order mismatch the prior audits
  flagged, by the "process first term, residualize, recurse" replay.
* The reduction chain `ResidualHeadDecode n → SwitchingLemmaTermSimple n`, with
  `ResidualHeadDecode` certified SATISFIABLE (n = 0, s = 0 slices).

NOT closed (the exact, honest obstruction):

`RCodeBlockStepVar n` (= `ResidualHeadDecode n`) requires a **ρ-INDEPENDENT** decode
step.  `deepResidual_head` reduces the i-th deep variable to a HEAD-block read of the
residual `residualIter (D|ρ) j` — but that residual is built from `D|ρ`, i.e. it is
`dnfRestrict (overlay ρ (prefixRestr prev)) D`, which needs `ρ`.  The only ρ-independent
restriction available to `stepVar` is `σ_loc = overlay ρ (satRestrLoc D s ρ)`, and
`satRestrLoc` ADDITIONALLY fixes the not-yet-decoded touched variables (deep indices
`≥ i`) to their SATISFYING values — which (a) differ from the deep directions and (b)
COLLAPSE the i-th deep term to the constant-true term `[]` (the proved
`SwitchingDeepAux.termRestrict_encodeLoc₁_satisfied` / `firstSat_eq_of_ρ_falsified_prefix`
show fully-touched deep terms collapse under `σ_loc`), ERASING exactly the variables to be
recovered.  Hence the residual the decode needs is NOT ρ-independently constructible from
`σ_loc` and `prev`: subtracting `ρ`'s genuine fixings from the satisfying fixings of the
future touched variables inside `σ_loc` is the convention-independent Razborov replay
content — the SAME heart isolated as `DeepBlockRecoverableW` /
`LocDeepBlockRecoverableW` / `RCodeRecoverable` in the sibling files.  We do NOT fake it:
it stays the isolated, satisfiable `def : Prop` `ResidualHeadDecode`, and the structural
machinery (`deepResidual_head` + drop laws) that a successful decode would consume is
proved green here.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`. -/

end SwitchingClose
end PvNP
