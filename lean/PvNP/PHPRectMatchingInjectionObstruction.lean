import PvNP.PHPFullMatchingGateABadConflictSignature

/-!
# Rectangular injection-space obstruction for Gate A

This module is the first finite rectangular/injection-space pivot after S2138.
It defines a rectangular matching-restriction space whose points choose `s` rows
among `p` pigeons and inject those selected rows into `h` holes.  It then ports
the realized bad-path code/fiber interface from the square full-matching space to
this rectangular space.

The result is an obstruction, not a positive switching lemma: at `p = 3`,
`h = 2`, `s = 2`, `t = 2`, a full-row DNF family has at least three
row-collision realized rectangular bad-path codes.  Thus the natural rectangular
denominator `3^(2/2)` is still met by the row-collision/bad side.

This is finite rectangular matching-space/list-support bookkeeping only.  It is
not a PHP switching lemma, not a rectangular `p > h` lower-bound theorem, not a
Frege/PHP lower bound, not an NP/circuit lower bound, not arbitrary AC0, and not
a P-vs-NP claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPRectMatchingInjectionObstruction

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open BoundedDepthCanonicalDT
open RestrictedPHPFloor
open PHPSearchFloor
open PHPMatchingDistribution
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingCompressedBadPathCount
open PHPFullMatchingRealizedCodeParametricObstruction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT

/-! ## Rectangular matching-restriction space -/

/-- Rectangular PHP literal data: row, column, polarity. -/
abbrev RectLitDatum (p h : Nat) := Fin p × Fin h × Bool

/-- A rectangular matching point: selected rows plus a row-to-hole map.  The
finite space below filters this type by injectivity on the selected rows. -/
abbrev RectMatchingPoint (p h : Nat) := Finset (Fin p) × (Fin p → Fin h)

/-- The selected-row map is injective on the selected rows. -/
def RectInjectionOnSelected {p h : Nat} (P : RectMatchingPoint p h) : Prop :=
  Set.InjOn P.2 {i : Fin p | i ∈ P.1}

/-- Rectangular injection-space analogue of `fullMatchingSpace`: choose `s` rows
from `p` pigeons, then choose an arbitrary map into `h` holes, retaining only the
maps that are injective on the selected rows. -/
noncomputable def rectMatchingSpace (p h s : Nat) : Finset (RectMatchingPoint p h) :=
  by
    classical
    exact ((subsetSpace p s).product (Finset.univ : Finset (Fin p → Fin h))).filter
      RectInjectionOnSelected

/-- The restriction associated to a rectangular injection-space point.  Selected
rows are fixed to their assigned hole; unselected rows are left free. -/
def rectRestrictionOf {p h : Nat} (P : RectMatchingPoint p h) :
    Restriction (Nat.succ (p * h)) :=
  fun v =>
    if hv : v.val < p * h then
      if pigeonOf v hv ∈ P.1 then
        some (decide (holeOf v hv = P.2 (pigeonOf v hv)))
      else
        none
    else
      none

/-- A rectangular PHP variable is free exactly when its row is not selected. -/
theorem rectRestrictionOf_phpVar_eq_none_iff {p h : Nat}
    (P : RectMatchingPoint p h) (i : Fin p) (j : Fin h) :
    rectRestrictionOf P (phpVar p h i j) = none ↔ i ∉ P.1 := by
  have hlt := phpVar_lt (p := p) (h := h) i j
  rw [rectRestrictionOf, dif_pos hlt, pigeonOf_phpVar i j hlt]
  by_cases hi : i ∈ P.1
  · simp [hi]
  · simp [hi]

/-! ## Rectangular PHP DNF and canonical bad-path codes -/

/-- Translate one rectangular PHP literal datum into the generic literal type. -/
def rectPHPLit (p h : Nat) (e : RectLitDatum p h) :
    Literal (Nat.succ (p * h)) :=
  { var := phpVar p h e.1 e.2.1, sign := e.2.2 }

/-- Translate one rectangular PHP term into the generic DNF-term representation. -/
def rectPHPTermAsTerm (p h : Nat) (tv : List (RectLitDatum p h)) :
    Term (Nat.succ (p * h)) :=
  tv.map (rectPHPLit p h)

/-- Translate a rectangular PHP DNF list into the generic DNF representation. -/
def rectPHPDNFAsDNF (p h : Nat) (tvs : List (List (RectLitDatum p h))) :
    DNF (Nat.succ (p * h)) :=
  tvs.map (rectPHPTermAsTerm p h)

/-- The finite set of variable indices appearing in the rectangular PHP DNF. -/
def rectPHPDNFVarSet (p h : Nat) (tvs : List (List (RectLitDatum p h))) :
    Finset (Fin (Nat.succ (p * h))) :=
  (tvs.join.map (fun e => phpVar p h e.1 e.2.1)).toFinset

theorem rectDNFVarsIn_rectPHPDNFAsDNF (p h : Nat)
    (tvs : List (List (RectLitDatum p h))) :
    DNFVarsIn (rectPHPDNFAsDNF p h tvs) (rectPHPDNFVarSet p h tvs) := by
  intro t ht l hl
  unfold rectPHPDNFAsDNF at ht
  rw [List.mem_map] at ht
  rcases ht with ⟨tv, htv, rfl⟩
  unfold rectPHPTermAsTerm at hl
  rw [List.mem_map] at hl
  rcases hl with ⟨e, he, rfl⟩
  unfold rectPHPLit rectPHPDNFVarSet
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨e, List.mem_join.mpr ⟨tv, htv, he⟩, rfl⟩

/-- The rectangular restricted canonical DNF tree. -/
def rectCanonicalRestrictedDNFTree (p h : Nat)
    (tvs : List (List (RectLitDatum p h))) (P : RectMatchingPoint p h) :
    DTree (Nat.succ (p * h)) :=
  termCanonicalDT (dnfRestrict (rectRestrictionOf P) (rectPHPDNFAsDNF p h tvs))

/-- Query-variable containment in the original rectangular DNF support. -/
theorem rectTreeVarsIn_canonicalRestrictedDNFTree {p h : Nat}
    (P : RectMatchingPoint p h) (tvs : List (List (RectLitDatum p h))) :
    TreeVarsIn (rectCanonicalRestrictedDNFTree p h tvs P)
      (rectPHPDNFVarSet p h tvs) := by
  unfold rectCanonicalRestrictedDNFTree
  exact treeVarsIn_termCanonicalDT
    (dnfRestrict (rectRestrictionOf P) (rectPHPDNFAsDNF p h tvs))
    (dnfVarsIn_dnfRestrict (rectDNFVarsIn_rectPHPDNFAsDNF p h tvs)
      (rectRestrictionOf P))

/-- Query-variable containment in the free variables of the rectangular
restriction. -/
theorem rectTreeVarsIn_free_canonicalRestrictedDNFTree {p h : Nat}
    (P : RectMatchingPoint p h) (tvs : List (List (RectLitDatum p h))) :
    TreeVarsIn (rectCanonicalRestrictedDNFTree p h tvs P)
      ((Finset.univ : Finset (Fin (Nat.succ (p * h)))).filter
        (fun v => rectRestrictionOf P v = none)) := by
  unfold rectCanonicalRestrictedDNFTree
  exact treeVarsIn_termCanonicalDT
    (dnfRestrict (rectRestrictionOf P) (rectPHPDNFAsDNF p h tvs))
    (dnfVarsIn_dnfRestrict_free (rectRestrictionOf P) (rectPHPDNFAsDNF p h tvs))

/-- Every variable on the deepest path of the rectangular restricted canonical
tree is free under the rectangular restriction. -/
theorem deepestPath_rectCanonicalRestrictedDNFTree_free {p h : Nat}
    (P : RectMatchingPoint p h) (tvs : List (List (RectLitDatum p h)))
    (vd : Fin (Nat.succ (p * h)) × Bool)
    (hvd : vd ∈ deepestPath (rectCanonicalRestrictedDNFTree p h tvs P)) :
    rectRestrictionOf P vd.1 = none := by
  have hvset := deepestPath_treeVarsIn (rectCanonicalRestrictedDNFTree p h tvs P)
    (rectTreeVarsIn_free_canonicalRestrictedDNFTree P tvs) vd hvd
  exact (Finset.mem_filter.mp hvset).2

/-- The depth-`t` bad event for rectangular restricted PHP DNF canonical trees. -/
def rectCanonicalDepthBad (p h : Nat)
    (tvs : List (List (RectLitDatum p h))) (t : Nat)
    (P : RectMatchingPoint p h) : Prop :=
  t ≤ dtDepth (rectCanonicalRestrictedDNFTree p h tvs P)

instance instDecidableRectCanonicalDepthBad {p h : Nat}
    {tvs : List (List (RectLitDatum p h))} {t : Nat}
    {P : RectMatchingPoint p h} :
    Decidable (rectCanonicalDepthBad p h tvs t P) := by
  unfold rectCanonicalDepthBad
  infer_instance

instance instDecidablePredRectCanonicalDepthBad {p h : Nat}
    (tvs : List (List (RectLitDatum p h))) (t : Nat) :
    DecidablePred (rectCanonicalDepthBad p h tvs t) := by
  intro P
  infer_instance

/-- Rectangular bad-path code: `t` certified query/direction pairs drawn from the
rectangular DNF support. -/
def RectBadPathCode (p h : Nat)
    (tvs : List (List (RectLitDatum p h))) (t : Nat) : Type :=
  Fin t → {v : Fin (Nat.succ (p * h)) // v ∈ rectPHPDNFVarSet p h tvs} × Bool

noncomputable instance instFintypeRectBadPathCode {p h : Nat}
    (tvs : List (List (RectLitDatum p h))) (t : Nat) :
    Fintype (RectBadPathCode p h tvs t) := by
  classical
  unfold RectBadPathCode
  infer_instance

noncomputable instance instDecidableEqRectBadPathCode {p h : Nat}
    (tvs : List (List (RectLitDatum p h))) (t : Nat) :
    DecidableEq (RectBadPathCode p h tvs t) := by
  classical
  infer_instance

/-- Extract the first `t` entries of a deepest path from a rectangular bad point. -/
noncomputable def rectCanonicalDepthBadCode {p h : Nat}
    (tvs : List (List (RectLitDatum p h))) (t : Nat)
    (P : RectMatchingPoint p h)
    (hbad : rectCanonicalDepthBad p h tvs t P) :
    RectBadPathCode p h tvs t := by
  intro i
  let T := rectCanonicalRestrictedDNFTree p h tvs P
  have hlen : i.1 < (deepestPath T).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le i.2 hbad
  let vd := (deepestPath T).get ⟨i.1, hlen⟩
  have hvdmem : vd ∈ deepestPath T := by
    exact List.get_mem (deepestPath T) i.1 hlen
  have hv : vd.1 ∈ rectPHPDNFVarSet p h tvs := by
    exact deepestPath_treeVarsIn T
      (rectTreeVarsIn_canonicalRestrictedDNFTree P tvs) vd hvdmem
  exact (⟨vd.1, hv⟩, vd.2)

/-- Rectangular conservative encoder; it keeps the original rectangular point. -/
noncomputable def rectCanonicalDepthBadEncoding (p h : Nat)
    (tvs : List (List (RectLitDatum p h))) (t : Nat)
    (P : RectMatchingPoint p h) :
    RectMatchingPoint p h × Option (RectBadPathCode p h tvs t) :=
  if hbad : rectCanonicalDepthBad p h tvs t P then
    (P, some (rectCanonicalDepthBadCode tvs t P hbad))
  else
    (P, none)

theorem rectCanonicalDepthBadEncoding_fst {p h : Nat}
    (tvs : List (List (RectLitDatum p h))) (t : Nat)
    (P : RectMatchingPoint p h) :
    (rectCanonicalDepthBadEncoding p h tvs t P).1 = P := by
  unfold rectCanonicalDepthBadEncoding
  by_cases hbad : rectCanonicalDepthBad p h tvs t P <;> simp [hbad]

/-- Rectangular canonical bad-code fiber inside the rectangular injection space. -/
noncomputable def rectCanonicalDepthBadCodeFiber {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (c : RectBadPathCode p h tvs t) : Finset (RectMatchingPoint p h) :=
  (rectMatchingSpace p h s).filter (fun P => rectCanonicalDepthBad p h tvs t P ∧
    (rectCanonicalDepthBadEncoding p h tvs t P).2 = some c)

/-- A rectangular bad-path code is realized when its rectangular bad-code fiber is
nonempty. -/
def rectCanonicalDepthBadCodeFiberNonempty {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (c : RectBadPathCode p h tvs t) : Prop :=
  (rectCanonicalDepthBadCodeFiber (p := p) (h := h) (s := s) (t := t) tvs c).Nonempty

/-- Rectangular realized bad-path codes. -/
noncomputable def rectRealizedBadPathCodes {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h))) : Finset (RectBadPathCode p h tvs t) :=
  by
    classical
    exact Finset.univ.filter
      (rectCanonicalDepthBadCodeFiberNonempty (p := p) (h := h) (s := s) (t := t) tvs)

theorem mem_rectRealizedBadPathCodes {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (c : RectBadPathCode p h tvs t) :
    c ∈ rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs ↔
      rectCanonicalDepthBadCodeFiberNonempty (p := p) (h := h) (s := s) (t := t)
        tvs c := by
  classical
  simp [rectRealizedBadPathCodes]

/-! ## Rectangular recovered rows and row-collision split -/

open Classical in
private theorem rectCodeStageEntry_exists {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) (k : Fin t) :
    ∃ e : RectLitDatum p h,
      e ∈ tvs.join ∧ phpVar p h e.1 e.2.1 =
        ((c k).1 : Fin (Nat.succ (p * h))) := by
  have hv : ((c k).1 : Fin (Nat.succ (p * h))) ∈ rectPHPDNFVarSet p h tvs :=
    (c k).1.2
  unfold rectPHPDNFVarSet at hv
  rw [List.mem_toFinset] at hv
  exact List.mem_map.mp hv

open Classical in
/-- Decode the rectangular literal occurrence whose variable is stored at stage
`k` of a bad-path code. -/
noncomputable def rectCodeStageEntry {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) (k : Fin t) : RectLitDatum p h :=
  Classical.choose (rectCodeStageEntry_exists c k)

/-- Recovered rectangular row at stage `k`. -/
noncomputable def rectCodeStageRow {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) (k : Fin t) : Fin p :=
  (rectCodeStageEntry c k).1

/-- Finite image of rows recovered stage-by-stage by a rectangular code. -/
noncomputable def rectCodeStageRows {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) : Finset (Fin p) :=
  Finset.univ.image (rectCodeStageRow c)

/-- The decoded rectangular stage entry has the PHP variable stored in the code. -/
theorem rectCodeStageEntry_var_eq {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) (k : Fin t) :
    phpVar p h (rectCodeStageRow c k) (rectCodeStageEntry c k).2.1 =
      ((c k).1 : Fin (Nat.succ (p * h))) := by
  unfold rectCodeStageRow rectCodeStageEntry
  exact (Classical.choose_spec (rectCodeStageEntry_exists c k)).2

theorem mem_rectCodeStageRows {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) (i : Fin p) :
    i ∈ rectCodeStageRows c ↔ ∃ k : Fin t, rectCodeStageRow c k = i := by
  unfold rectCodeStageRows
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, _hk, hkrow⟩
    exact ⟨k, hkrow⟩
  · rintro ⟨k, hkrow⟩
    exact ⟨k, Finset.mem_univ k, hkrow⟩

/-- Every variable recorded by the rectangular canonical bad-path code is free
under the rectangular restriction of the bad point it was extracted from. -/
theorem rectCanonicalDepthBadCode_fst_free {p h : Nat}
    (tvs : List (List (RectLitDatum p h))) (t : Nat)
    (P : RectMatchingPoint p h)
    (hbad : rectCanonicalDepthBad p h tvs t P) (k : Fin t) :
    rectRestrictionOf P
      ((rectCanonicalDepthBadCode tvs t P hbad k).1 : Fin (Nat.succ (p * h))) =
      none := by
  have hlen : k.1 <
      (deepestPath (rectCanonicalRestrictedDNFTree p h tvs P)).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le k.2 hbad
  have hvdmem :
      (deepestPath (rectCanonicalRestrictedDNFTree p h tvs P)).get ⟨k.1, hlen⟩
        ∈ deepestPath (rectCanonicalRestrictedDNFTree p h tvs P) :=
    List.get_mem (deepestPath (rectCanonicalRestrictedDNFTree p h tvs P)) k.1 hlen
  exact deepestPath_rectCanonicalRestrictedDNFTree_free P tvs _ hvdmem

/-- Every recovered row at a fixed stage is outside the selected row set for any
rectangular bad point whose bad-path encoding is the code `c`. -/
theorem rectCodeStageRow_free_of_encoding_eq_some {p h t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (c : RectBadPathCode p h tvs t)
    (P : RectMatchingPoint p h)
    (hbad : rectCanonicalDepthBad p h tvs t P)
    (henc : (rectCanonicalDepthBadEncoding p h tvs t P).2 = some c)
    (k : Fin t) :
    rectCodeStageRow c k ∉ P.1 := by
  have hc : rectCanonicalDepthBadCode tvs t P hbad = c := by
    unfold rectCanonicalDepthBadEncoding at henc
    rw [dif_pos hbad] at henc
    exact Option.some.inj henc
  have hfree : rectRestrictionOf P
      ((c k).1 : Fin (Nat.succ (p * h))) = none := by
    rw [← hc]
    exact rectCanonicalDepthBadCode_fst_free tvs t P hbad k
  have hvar := rectCodeStageEntry_var_eq c k
  rw [← hvar, rectRestrictionOf_phpVar_eq_none_iff] at hfree
  exact hfree

/-- A rectangular code is row-variable-unique when equal recovered rows force
equal decoded columns. -/
def RectCodeRowVarUnique {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) : Prop :=
  ∀ k l : Fin t,
    rectCodeStageRow c k = rectCodeStageRow c l →
      (rectCodeStageEntry c k).2.1 = (rectCodeStageEntry c l).2.1

/-- A rectangular row-collision code has two stages using the same row and two
different decoded columns. -/
def RectCodeRowCollision {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) : Prop :=
  ∃ k l : Fin t,
    rectCodeStageRow c k = rectCodeStageRow c l ∧
      (rectCodeStageEntry c k).2.1 ≠ (rectCodeStageEntry c l).2.1

/-- Rectangular realized codes whose recovered stages are row-variable-unique. -/
noncomputable def rectRowVarUniqueRealizedBadPathCodes {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h))) :
    Finset (RectBadPathCode p h tvs t) :=
  by
    classical
    exact (rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs).filter
      (fun c => RectCodeRowVarUnique c)

/-- Rectangular realized codes with a same-row/different-column collision. -/
noncomputable def rectRowCollisionRealizedBadPathCodes {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h))) :
    Finset (RectBadPathCode p h tvs t) :=
  by
    classical
    exact (rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs).filter
      (fun c => RectCodeRowCollision c)

theorem mem_rectRowVarUniqueRealizedBadPathCodes {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (c : RectBadPathCode p h tvs t) :
    c ∈ rectRowVarUniqueRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs ↔
      c ∈ rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs ∧
        RectCodeRowVarUnique c := by
  classical
  simp [rectRowVarUniqueRealizedBadPathCodes]

theorem mem_rectRowCollisionRealizedBadPathCodes {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (c : RectBadPathCode p h tvs t) :
    c ∈ rectRowCollisionRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs ↔
      c ∈ rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs ∧
        RectCodeRowCollision c := by
  classical
  simp [rectRowCollisionRealizedBadPathCodes]

/-- The rectangular row-collision predicate is the complement of row-variable
uniqueness. -/
theorem rectCodeRowCollision_iff_not_rectCodeRowVarUnique {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t) :
    RectCodeRowCollision c ↔ ¬ RectCodeRowVarUnique c := by
  classical
  unfold RectCodeRowCollision RectCodeRowVarUnique
  constructor
  · rintro ⟨k, l, hrow, hne⟩ huniq
    exact hne (huniq k l hrow)
  · intro hnot
    by_contra hnocoll
    apply hnot
    intro k l hrow
    by_contra hne
    exact hnocoll ⟨k, l, hrow, hne⟩

/-- The rectangular realized-code set splits into row-variable-unique and
row-collision realized codes. -/
theorem rectRealizedBadPathCodes_eq_rowVarUnique_union_rowCollision {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h))) :
    rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs =
      rectRowVarUniqueRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs ∪
        rectRowCollisionRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs := by
  classical
  ext c
  constructor
  · intro hc
    by_cases huniq : RectCodeRowVarUnique c
    · exact Finset.mem_union.mpr <| Or.inl <|
        (mem_rectRowVarUniqueRealizedBadPathCodes (p := p) (h := h) (s := s)
          (t := t) tvs c).mpr ⟨hc, huniq⟩
    · have hcoll : RectCodeRowCollision c :=
        (rectCodeRowCollision_iff_not_rectCodeRowVarUnique c).mpr huniq
      exact Finset.mem_union.mpr <| Or.inr <|
        (mem_rectRowCollisionRealizedBadPathCodes (p := p) (h := h) (s := s)
          (t := t) tvs c).mpr ⟨hc, hcoll⟩
  · intro hc
    rcases Finset.mem_union.mp hc with huniq | hcoll
    · exact ((mem_rectRowVarUniqueRealizedBadPathCodes (p := p) (h := h) (s := s)
        (t := t) tvs c).mp huniq).1
    · exact ((mem_rectRowCollisionRealizedBadPathCodes (p := p) (h := h) (s := s)
        (t := t) tvs c).mp hcoll).1

theorem rectCodeStageRows_card_eq_of_injective {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (c : RectBadPathCode p h tvs t)
    (hinj : Function.Injective (rectCodeStageRow c)) :
    (rectCodeStageRows c).card = t := by
  unfold rectCodeStageRows
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Code-local row-variable uniqueness turns equal recovered rows into equal
stored rectangular PHP variables. -/
theorem rectCodeStageVar_eq_of_rectCodeRowVarUnique_row_eq {p h t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    {c : RectBadPathCode p h tvs t}
    (huniq : RectCodeRowVarUnique c) {k l : Fin t}
    (hrow : rectCodeStageRow c k = rectCodeStageRow c l) :
    ((c k).1 : Fin (Nat.succ (p * h))) =
      ((c l).1 : Fin (Nat.succ (p * h))) := by
  have hcol : (rectCodeStageEntry c k).2.1 = (rectCodeStageEntry c l).2.1 :=
    huniq k l hrow
  calc
    ((c k).1 : Fin (Nat.succ (p * h)))
        = phpVar p h (rectCodeStageRow c k) (rectCodeStageEntry c k).2.1 := by
          exact (rectCodeStageEntry_var_eq c k).symm
    _ = phpVar p h (rectCodeStageRow c l) (rectCodeStageEntry c l).2.1 := by
          rw [hrow, hcol]
    _ = ((c l).1 : Fin (Nat.succ (p * h))) := by
          exact rectCodeStageEntry_var_eq c l

/-- For realized simple rectangular DNF codes, row-variable uniqueness upgrades
variable injectivity to recovered-row injectivity. -/
theorem rectCodeStageRow_injective_of_realized_simple_rectCodeRowVarUnique {p h s t : Nat}
    {tvs : List (List (RectLitDatum p h))}
    (hsimple : SimpleDNF (rectPHPDNFAsDNF p h tvs))
    (c : RectBadPathCode p h tvs t)
    (hreal : rectCanonicalDepthBadCodeFiberNonempty (p := p) (h := h) (s := s)
      (t := t) tvs c)
    (huniq : RectCodeRowVarUnique c) :
    Function.Injective (rectCodeStageRow c) := by
  classical
  rcases hreal with ⟨P, hP⟩
  rw [rectCanonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨_hspace, hbad, henc⟩ := hP
  have hc : rectCanonicalDepthBadCode tvs t P hbad = c := by
    unfold rectCanonicalDepthBadEncoding at henc
    rw [dif_pos hbad] at henc
    exact Option.some.inj henc
  intro k l hrow
  have hkl : ((c k).1 : Fin (Nat.succ (p * h))) =
      ((c l).1 : Fin (Nat.succ (p * h))) :=
    rectCodeStageVar_eq_of_rectCodeRowVarUnique_row_eq huniq hrow
  let T := rectCanonicalRestrictedDNFTree p h tvs P
  have hlenk : k.1 < (deepestPath T).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le k.2 hbad
  have hlenl : l.1 < (deepestPath T).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le l.2 hbad
  have hnd : ((deepestPath T).map Prod.fst).Nodup := by
    unfold T rectCanonicalRestrictedDNFTree
    exact deepestPath_var_nodup hsimple (rectRestrictionOf P)
  have hget : ((deepestPath T).map Prod.fst).get ⟨k.1, by simpa using hlenk⟩ =
      ((deepestPath T).map Prod.fst).get ⟨l.1, by simpa using hlenl⟩ := by
    have hkl' :
        ((rectCanonicalDepthBadCode tvs t P hbad k).1 : Fin (Nat.succ (p * h))) =
          ((rectCanonicalDepthBadCode tvs t P hbad l).1 : Fin (Nat.succ (p * h))) := by
      simpa [hc] using hkl
    simpa [rectCanonicalDepthBadCode, T, hlenk, hlenl] using hkl'
  have hidx : (⟨k.1, by simpa using hlenk⟩ : Fin ((deepestPath T).map Prod.fst).length) =
      ⟨l.1, by simpa using hlenl⟩ := hnd.get_inj_iff.mp hget
  have hval :
      (⟨k.1, by simpa using hlenk⟩ : Fin ((deepestPath T).map Prod.fst).length).val =
        (⟨l.1, by simpa using hlenl⟩ : Fin ((deepestPath T).map Prod.fst).length).val :=
    congrArg (fun x : Fin ((deepestPath T).map Prod.fst).length => x.val) hidx
  exact Fin.ext hval

/-- Under rectangular `SimpleDNF`, the row-variable-unique realized-code class is
empty when the selected rows and `t` recovered rows cannot fit into `p` rows. -/
theorem rectRowVarUniqueRealizedBadPathCodes_eq_empty_of_simple_of_p_lt_s_add_t
    {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (hsimple : SimpleDNF (rectPHPDNFAsDNF p h tvs))
    (hfit : p < s + t) :
    rectRowVarUniqueRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hcmem := (mem_rectRowVarUniqueRealizedBadPathCodes (p := p) (h := h)
    (s := s) (t := t) tvs c).mp hc
  have hreal : rectCanonicalDepthBadCodeFiberNonempty (p := p) (h := h) (s := s)
      (t := t) tvs c :=
    (mem_rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs c).mp
      hcmem.1
  have hinj : Function.Injective (rectCodeStageRow (tvs := tvs) c) :=
    rectCodeStageRow_injective_of_realized_simple_rectCodeRowVarUnique
      (p := p) (h := h) (s := s) (t := t) hsimple c hreal hcmem.2
  have hrowsCard : (rectCodeStageRows c).card = t :=
    rectCodeStageRows_card_eq_of_injective c hinj
  rcases hreal with ⟨P, hP⟩
  rw [rectCanonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨hspace, hbad, henc⟩ := hP
  have hfree : ∀ i ∈ rectCodeStageRows c, i ∉ P.1 := by
    intro i hi
    obtain ⟨k, hkrow⟩ := (mem_rectCodeStageRows c i).mp hi
    rw [← hkrow]
    exact rectCodeStageRow_free_of_encoding_eq_some tvs c P hbad henc k
  have hPcard : P.1.card = s := by
    unfold rectMatchingSpace subsetSpace at hspace
    rw [Finset.mem_filter] at hspace
    have hsubset := (Finset.mem_product.mp hspace.1).1
    exact (Finset.mem_powersetCard.mp hsubset).2
  have hdisj : Disjoint P.1 (rectCodeStageRows c) := by
    rw [Finset.disjoint_left]
    intro r hrP hrRows
    exact hfree r hrRows hrP
  have hcardUnion : (P.1 ∪ rectCodeStageRows c).card = s + t := by
    rw [Finset.card_union_of_disjoint hdisj, hPcard, hrowsCard]
  have hle : s + t ≤ p := by
    rw [← hcardUnion]
    simpa [Fintype.card_fin] using
      (Finset.card_le_univ (P.1 ∪ rectCodeStageRows c) :
        (P.1 ∪ rectCodeStageRows c).card ≤ Fintype.card (Fin p))
  exact (Nat.not_lt_of_ge hle) hfit

/-- In the rectangular row-capacity obstruction regime, every realized code is a
row-collision code. -/
theorem rectRealizedBadPathCodes_eq_rectRowCollisionRealizedBadPathCodes_of_simple_of_p_lt_s_add_t
    {p h s t : Nat}
    (tvs : List (List (RectLitDatum p h)))
    (hsimple : SimpleDNF (rectPHPDNFAsDNF p h tvs))
    (hfit : p < s + t) :
    rectRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs =
      rectRowCollisionRealizedBadPathCodes (p := p) (h := h) (s := s) (t := t) tvs := by
  rw [rectRealizedBadPathCodes_eq_rowVarUnique_union_rowCollision
    (p := p) (h := h) (s := s) (t := t) tvs]
  rw [rectRowVarUniqueRealizedBadPathCodes_eq_empty_of_simple_of_p_lt_s_add_t
    (p := p) (h := h) (s := s) (t := t) tvs hsimple hfit]
  rw [Finset.empty_union]

/-! ## Bounded `3 × 2` rectangular obstruction family -/

/-- Positive full-row term over a rectangular `p × h` PHP surface. -/
def rectFullRowTerm (p h : Nat) (r : Fin p) : List (RectLitDatum p h) :=
  List.ofFn (fun c : Fin h => (r, c, true))

/-- Rectangular DNF with one positive full-row term for every row. -/
def rectFullRowTvs (p h : Nat) : List (List (RectLitDatum p h)) :=
  List.ofFn (fun r : Fin p => rectFullRowTerm p h r)

/-- The concrete `3 × 2` full-row DNF. -/
def rectThreeTwoFullRowTvs : List (List (RectLitDatum 3 2)) :=
  rectFullRowTvs 3 2

/-- Assignment used when row `r` is left free in the `3 × 2` obstruction.  On
the selected rows `univ.erase r`, this is the order-rank map into `Fin 2`. -/
def rectThreeTwoAssign (r : Fin 3) (i : Fin 3) : Fin 2 :=
  if hlt : i.val < r.val then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by omega⟩

theorem rectThreeTwoAssign_injOn_univ_erase (r : Fin 3) :
    Set.InjOn (rectThreeTwoAssign r) {i : Fin 3 | i ∈ (Finset.univ.erase r : Finset (Fin 3))} := by
  intro a ha b hb hab
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha hb
  apply Fin.ext
  have hval := congrArg Fin.val hab
  have hane : a.val ≠ r.val := by
    intro h
    exact ha (Fin.ext h)
  have hbne : b.val ≠ r.val := by
    intro h
    exact hb (Fin.ext h)
  unfold rectThreeTwoAssign at hval
  by_cases ha_lt : a.val < r.val <;> by_cases hb_lt : b.val < r.val <;>
    simp [ha_lt, hb_lt] at hval <;> omega

/-- Rectangular point fixing all rows except `r`, injectively into the two holes. -/
def rectThreeTwoP (r : Fin 3) : RectMatchingPoint 3 2 :=
  (Finset.univ.erase r, rectThreeTwoAssign r)

theorem rectThreeTwoP_mem_rectMatchingSpace (r : Fin 3) :
    rectThreeTwoP r ∈ rectMatchingSpace 3 2 2 := by
  classical
  unfold rectMatchingSpace rectThreeTwoP RectInjectionOnSelected subsetSpace
  rw [Finset.mem_filter]
  constructor
  · exact Finset.mem_product.mpr ⟨by simp, by simp⟩
  · simpa using rectThreeTwoAssign_injOn_univ_erase r

theorem rectFullRowTvs_simple (p h : Nat) :
    SimpleDNF (rectPHPDNFAsDNF p h (rectFullRowTvs p h)) := by
  classical
  intro t ht
  rw [rectPHPDNFAsDNF, List.mem_map] at ht
  rcases ht with ⟨tv, htv, rfl⟩
  unfold rectFullRowTvs at htv
  rw [List.mem_ofFn] at htv
  rcases htv with ⟨r, rfl⟩
  unfold SimpleTerm rectPHPTermAsTerm rectFullRowTerm rectPHPLit
  simpa [List.map_map, Function.comp_def, rectPHPLit, rectFullRowTerm] using
    (List.nodup_ofFn.mpr (by
      intro a b hab
      exact (phpVar_inj hab).2) :
      (List.ofFn fun c : Fin h => phpVar p h r c).Nodup)

theorem termRestrict_rectFullRowTerm_self {p h : Nat}
    (P : RectMatchingPoint p h) (r : Fin p) (hr : r ∉ P.1) :
    termRestrict (rectRestrictionOf P)
      (rectPHPTermAsTerm p h (rectFullRowTerm p h r)) =
        some (rectPHPTermAsTerm p h (rectFullRowTerm p h r)) := by
  classical
  apply termRestrict_eq_self_of_forall_none
  intro l hl
  unfold rectPHPTermAsTerm at hl
  rw [List.mem_map] at hl
  rcases hl with ⟨e, he, rfl⟩
  unfold rectPHPLit
  rw [rectRestrictionOf_phpVar_eq_none_iff]
  unfold rectFullRowTerm at he
  rw [List.mem_ofFn] at he
  rcases he with ⟨c, rfl⟩
  exact hr

theorem termRestrict_rectFullRowTerm_eq_none_of_row_selected {p h : Nat}
    (hh : 2 ≤ h) (P : RectMatchingPoint p h) {i : Fin p} (hi : i ∈ P.1) :
    termRestrict (rectRestrictionOf P)
      (rectPHPTermAsTerm p h (rectFullRowTerm p h i)) = none := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin h, c ≠ P.2 i := by
    exact Fintype.exists_ne_of_one_lt_card (by simpa using hh) (P.2 i)
  apply termRestrict_eq_none_of_mem_false
    (l := rectPHPLit p h (i, c, true)) (b := false)
  · unfold rectPHPTermAsTerm rectFullRowTerm
    rw [List.mem_map]
    refine ⟨(i, c, true), ?_, rfl⟩
    rw [List.mem_ofFn]
    exact ⟨c, rfl⟩
  · unfold rectPHPLit rectRestrictionOf
    rw [dif_pos (phpVar_lt (p := p) (h := h) i c)]
    rw [pigeonOf_phpVar, holeOf_phpVar]
    simp [hi, hc]
  · simp [rectPHPLit]

theorem dnfRestrict_rectThreeTwoFullRowTvs_eq_singleton (r : Fin 3) :
    dnfRestrict (rectRestrictionOf (rectThreeTwoP r))
        (rectPHPDNFAsDNF 3 2 rectThreeTwoFullRowTvs) =
      [rectPHPTermAsTerm 3 2 (rectFullRowTerm 3 2 r)] := by
  classical
  unfold dnfRestrict rectPHPDNFAsDNF rectThreeTwoFullRowTvs rectFullRowTvs
  rw [List.map_ofFn]
  simpa [Function.comp_def] using
    filterMap_ofFn_eq_singleton
      (G := fun i : Fin 3 => rectPHPTermAsTerm 3 2 (rectFullRowTerm 3 2 i))
      (F := termRestrict (rectRestrictionOf (rectThreeTwoP r)))
      r (rectPHPTermAsTerm 3 2 (rectFullRowTerm 3 2 r))
      (termRestrict_rectFullRowTerm_self (P := rectThreeTwoP r) r (by simp [rectThreeTwoP]))
      (by
        intro i hi
        exact termRestrict_rectFullRowTerm_eq_none_of_row_selected (p := 3) (h := 2)
          (by decide) (rectThreeTwoP r) (by simp [rectThreeTwoP, hi]))

theorem rectThreeTwoP_canonicalDepthBad (r : Fin 3) :
    rectCanonicalDepthBad 3 2 rectThreeTwoFullRowTvs 2 (rectThreeTwoP r) := by
  unfold rectCanonicalDepthBad rectCanonicalRestrictedDNFTree
  rw [dnfRestrict_rectThreeTwoFullRowTvs_eq_singleton r]
  have hlen : (rectPHPTermAsTerm 3 2 (rectFullRowTerm 3 2 r)).length = 2 := by
    simp [rectPHPTermAsTerm, rectFullRowTerm]
  simpa [hlen] using
    dtDepth_termCanonicalDT_cons_ge_length
      (t := rectPHPTermAsTerm 3 2 (rectFullRowTerm 3 2 r)) ([])

/-- The rectangular realized code associated with a free row in the `3 × 2`
full-row obstruction. -/
noncomputable def rectThreeTwoCode (r : Fin 3) :
    RectBadPathCode 3 2 rectThreeTwoFullRowTvs 2 :=
  rectCanonicalDepthBadCode rectThreeTwoFullRowTvs 2 (rectThreeTwoP r)
    (rectThreeTwoP_canonicalDepthBad r)

theorem rectThreeTwoCode_mem_realized (r : Fin 3) :
    rectThreeTwoCode r ∈
      rectRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
        rectThreeTwoFullRowTvs := by
  classical
  rw [mem_rectRealizedBadPathCodes]
  refine ⟨rectThreeTwoP r, ?_⟩
  unfold rectCanonicalDepthBadCodeFiber
  rw [Finset.mem_filter]
  refine ⟨rectThreeTwoP_mem_rectMatchingSpace r, rectThreeTwoP_canonicalDepthBad r, ?_⟩
  unfold rectCanonicalDepthBadEncoding rectThreeTwoCode
  rw [dif_pos (rectThreeTwoP_canonicalDepthBad r)]

theorem rectThreeTwoCode_injective :
    Function.Injective rectThreeTwoCode := by
  classical
  intro r r' hcode
  let k : Fin 2 := ⟨0, by decide⟩
  have hfree : rectCodeStageRow (rectThreeTwoCode r) k ∉ (rectThreeTwoP r).1 :=
    rectCodeStageRow_free_of_encoding_eq_some rectThreeTwoFullRowTvs (rectThreeTwoCode r)
      (rectThreeTwoP r) (rectThreeTwoP_canonicalDepthBad r) (by
        unfold rectCanonicalDepthBadEncoding rectThreeTwoCode
        rw [dif_pos (rectThreeTwoP_canonicalDepthBad r)]) k
  have hfree'_tmp : rectCodeStageRow (rectThreeTwoCode r') k ∉ (rectThreeTwoP r').1 :=
    rectCodeStageRow_free_of_encoding_eq_some rectThreeTwoFullRowTvs (rectThreeTwoCode r')
      (rectThreeTwoP r') (rectThreeTwoP_canonicalDepthBad r') (by
        unfold rectCanonicalDepthBadEncoding rectThreeTwoCode
        rw [dif_pos (rectThreeTwoP_canonicalDepthBad r')]) k
  have hfree' : rectCodeStageRow (rectThreeTwoCode r) k ∉ (rectThreeTwoP r').1 := by
    simpa [hcode] using hfree'_tmp
  have hr : rectCodeStageRow (rectThreeTwoCode r) k = r := by
    simpa [rectThreeTwoP] using hfree
  have hr' : rectCodeStageRow (rectThreeTwoCode r) k = r' := by
    simpa [rectThreeTwoP] using hfree'
  exact hr.symm.trans hr'

/-- The rectangular `3 × 2` full-row family has at least three row-collision
realized bad-path codes. -/
theorem rectThreeTwo_rowCollisionRealizedBadPathCodes_card_ge_three :
    3 ≤ (rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
      rectThreeTwoFullRowTvs).card := by
  classical
  have heq : rectRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
      rectThreeTwoFullRowTvs =
        rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
          rectThreeTwoFullRowTvs := by
    exact rectRealizedBadPathCodes_eq_rectRowCollisionRealizedBadPathCodes_of_simple_of_p_lt_s_add_t
      (p := 3) (h := 2) (s := 2) (t := 2) rectThreeTwoFullRowTvs
      (by simpa [rectThreeTwoFullRowTvs] using rectFullRowTvs_simple 3 2)
      (by decide)
  rw [← heq]
  simpa using Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := rectRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
      rectThreeTwoFullRowTvs)
    (f := rectThreeTwoCode)
    (by intro r _; exact rectThreeTwoCode_mem_realized r)
    (by intro a _ b _ hab; exact rectThreeTwoCode_injective hab)

/-- The natural rectangular denominator `3^(2/2)` is no larger than the bounded
`3 × 2` row-collision realized-code count. -/
theorem rectThreeTwo_denominator_le_rowCollisionRealizedBadPathCodes_card :
    3 ^ (2 / 2) ≤
      (rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
        rectThreeTwoFullRowTvs).card := by
  have hdiv : 2 / 2 = 1 := by decide
  rw [hdiv, Nat.pow_one]
  exact rectThreeTwo_rowCollisionRealizedBadPathCodes_card_ge_three

/-- The strict rectangular row-collision cardinality saving fails for the bounded
`3 × 2` full-row family. -/
theorem rectThreeTwo_not_rowCollisionRealizedBadPathCodes_card_lt_denominator :
    ¬ (rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
        rectThreeTwoFullRowTvs).card < 3 ^ (2 / 2) := by
  exact not_lt_of_ge rectThreeTwo_denominator_le_rowCollisionRealizedBadPathCodes_card

/-- Consequently, the naive rectangular/injection-space row-collision route is
not nontrivial on the bounded `3 × 2` family. -/
theorem rectThreeTwo_rectangular_route_nontrivial_impossible :
    ¬ (rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
        rectThreeTwoFullRowTvs).card * (3 - 2) ^ (2 / 2) < 3 ^ (2 / 2) := by
  have hone : (3 - 2) ^ (2 / 2) = 1 := by decide
  simpa [hone] using rectThreeTwo_not_rowCollisionRealizedBadPathCodes_card_lt_denominator

end PHPRectMatchingInjectionObstruction
end PvNP
