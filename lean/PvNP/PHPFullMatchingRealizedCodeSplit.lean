import PvNP.PHPFullMatchingRowUniqueStrict

/-!
# Realized-code row-variable split

This module splits realized canonical bad-path codes into two code-local classes:
codes whose recovered stages are row-variable-unique, and codes with an explicit
row collision where the same recovered row uses two different PHP columns.  Under
`SimpleDNF`, the row-variable-unique class is empty whenever `h < s + t`, so in
that regime every realized code lies in the row-collision class.

The scope is finite square full-matching realized-code bookkeeping only.  No PHP
switching lemma, Frege/PHP lower bound, rectangular `p > h` result, NP/circuit
lower bound, arbitrary AC0 result, or P-vs-NP claim is stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingRealizedCodeSplit

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingCompressedBadPathCount
open PHPFullMatchingDistribution
open PHPFullMatchingProbability
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeObstruction
open PHPFullMatchingRowUniqueStrict
open PHPFullMatchingStageRows
open PHPFullMatchingStageRowObstruction
open PHPMatchingDistribution
open PHPSearchFloor
open RestrictedPHPFloor
open SwitchingEncodeConstruct

/-! ## Code-local split definitions -/

/-- A bad-path code is row-variable-unique when equal recovered stage rows force
equal decoded PHP columns.  This is code-local and does not require a whole-DNF
global uniqueness condition. -/
def CodeRowVarUnique {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) : Prop :=
  ∀ k l : Fin t,
    codeStageRow c k = codeStageRow c l ->
      (codeStageEntry c k).2.1 = (codeStageEntry c l).2.1

/-- A row-collision code has two recovered stages using the same row but
different PHP columns. -/
def CodeRowCollision {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) : Prop :=
  ∃ k l : Fin t,
    codeStageRow c k = codeStageRow c l ∧
      (codeStageEntry c k).2.1 ≠ (codeStageEntry c l).2.1

/-- Realized bad-path codes whose recovered stages are code-local
row-variable-unique. -/
noncomputable def rowVarUniqueRealizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Finset (BadPathCode h tvs t) :=
  by
    classical
    exact (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).filter
      (fun c => CodeRowVarUnique c)

/-- Realized bad-path codes with an explicit same-row/different-column collision. -/
noncomputable def rowCollisionRealizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Finset (BadPathCode h tvs t) :=
  by
    classical
    exact (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).filter
      (fun c => CodeRowCollision c)

theorem mem_rowVarUniqueRealizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) :
    c ∈ rowVarUniqueRealizedBadPathCodes (h := h) (s := s) (t := t) tvs ↔
      c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ∧
        CodeRowVarUnique c := by
  classical
  simp [rowVarUniqueRealizedBadPathCodes]

theorem mem_rowCollisionRealizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) :
    c ∈ rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs ↔
      c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ∧
        CodeRowCollision c := by
  classical
  simp [rowCollisionRealizedBadPathCodes]

/-- The two code-local classes are complementary at the predicate level. -/
theorem codeRowCollision_iff_not_codeRowVarUnique {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) :
    CodeRowCollision c ↔ ¬ CodeRowVarUnique c := by
  classical
  unfold CodeRowCollision CodeRowVarUnique
  constructor
  · rintro ⟨k, l, hrow, hne⟩ huniq
    exact hne (huniq k l hrow)
  · intro hnot
    by_contra hnocoll
    apply hnot
    intro k l hrow
    by_contra hne
    exact hnocoll ⟨k, l, hrow, hne⟩

/-- The realized-code set splits exactly into the row-variable-unique realized
codes and the row-collision realized codes. -/
theorem realizedBadPathCodes_eq_rowVarUnique_union_rowCollision {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    realizedBadPathCodes (h := h) (s := s) (t := t) tvs =
      rowVarUniqueRealizedBadPathCodes (h := h) (s := s) (t := t) tvs ∪
        rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs := by
  classical
  ext c
  constructor
  · intro hc
    by_cases huniq : CodeRowVarUnique c
    · exact Finset.mem_union.mpr <| Or.inl <|
        (mem_rowVarUniqueRealizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mpr
          ⟨hc, huniq⟩
    · have hcoll : CodeRowCollision c :=
        (codeRowCollision_iff_not_codeRowVarUnique c).mpr huniq
      exact Finset.mem_union.mpr <| Or.inr <|
        (mem_rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mpr
          ⟨hc, hcoll⟩
  · intro hc
    rcases Finset.mem_union.mp hc with huniq | hcoll
    · exact ((mem_rowVarUniqueRealizedBadPathCodes
        (h := h) (s := s) (t := t) tvs c).mp huniq).1
    · exact ((mem_rowCollisionRealizedBadPathCodes
        (h := h) (s := s) (t := t) tvs c).mp hcoll).1

/-- The two realized-code classes are disjoint. -/
theorem disjoint_rowVarUniqueRealizedBadPathCodes_rowCollision {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Disjoint
      (rowVarUniqueRealizedBadPathCodes (h := h) (s := s) (t := t) tvs)
      (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs) := by
  classical
  rw [Finset.disjoint_left]
  intro c huniq hcoll
  have hrowuniq := ((mem_rowVarUniqueRealizedBadPathCodes
    (h := h) (s := s) (t := t) tvs c).mp huniq).2
  have hrowcoll := ((mem_rowCollisionRealizedBadPathCodes
    (h := h) (s := s) (t := t) tvs c).mp hcoll).2
  exact (codeRowCollision_iff_not_codeRowVarUnique c).mp hrowcoll hrowuniq

/-! ## Code-local row-variable uniqueness gives the S2130 row-capacity bound -/

/-- Code-local row-variable uniqueness turns equal recovered rows into equal
stored code variables. -/
theorem codeStageVar_eq_of_codeRowVarUnique_row_eq {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    {c : BadPathCode h tvs t}
    (huniq : CodeRowVarUnique c) {k l : Fin t}
    (hrow : codeStageRow c k = codeStageRow c l) :
    ((c k).1 : Fin (Nat.succ (h * h))) =
      ((c l).1 : Fin (Nat.succ (h * h))) := by
  have hcol : (codeStageEntry c k).2.1 = (codeStageEntry c l).2.1 :=
    huniq k l hrow
  calc
    ((c k).1 : Fin (Nat.succ (h * h)))
        = phpVar h h (codeStageRow c k) (codeStageEntry c k).2.1 := by
          exact (codeStageEntry_var_eq c k).symm
    _ = phpVar h h (codeStageRow c l) (codeStageEntry c l).2.1 := by
          rw [hrow, hcol]
    _ = ((c l).1 : Fin (Nat.succ (h * h))) := by
          exact codeStageEntry_var_eq c l

/-- For realized simple-DNF codes, code-local row-variable uniqueness upgrades
the existing variable injectivity theorem to injectivity of recovered stage rows. -/
theorem codeStageRow_injective_of_realized_simple_codeRowVarUnique {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (c : BadPathCode h tvs t)
    (hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c)
    (huniq : CodeRowVarUnique c) :
    Function.Injective (codeStageRow (tvs := tvs) c) := by
  intro k l hrow
  exact codeStageVar_injective_of_realized_simple (h := h) (s := s) (t := t)
    hsimple c hreal (codeStageVar_eq_of_codeRowVarUnique_row_eq huniq hrow)

/-- Under `SimpleDNF`, the row-variable-unique realized-code class is empty when
the `t` injective recovered rows and the `s` matching rows cannot fit in `h`
rows. -/
theorem rowVarUniqueRealizedBadPathCodes_eq_empty_of_simple_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (hfit : h < s + t) :
    rowVarUniqueRealizedBadPathCodes (h := h) (s := s) (t := t) tvs = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hcmem := (mem_rowVarUniqueRealizedBadPathCodes
    (h := h) (s := s) (t := t) tvs c).mp hc
  have hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c :=
    (mem_realizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mp hcmem.1
  have hinj : Function.Injective (codeStageRow (tvs := tvs) c) :=
    codeStageRow_injective_of_realized_simple_codeRowVarUnique
      (h := h) (s := s) (t := t) hsimple c hreal hcmem.2
  have hrowsCard : (codeStageRows c).card = t :=
    codeStageRows_card_eq_of_injective c hinj
  rcases hreal with ⟨P, hP⟩
  rw [canonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨hspace, hbad, henc⟩ := hP
  have hfree : fullRowsFree (codeStageRows c) P :=
    fullRowsFree_codeStageRows_of_encoding_eq_some tvs c P hbad henc
  have hPcard : P.1.card = s := by
    unfold fullMatchingSpace subsetSpace at hspace
    have hsubset := (Finset.mem_product.mp hspace).1
    exact (Finset.mem_powersetCard.mp hsubset).2
  have hdisj : Disjoint P.1 (codeStageRows c) := by
    rw [Finset.disjoint_left]
    intro r hrP hrRows
    exact hfree r hrRows hrP
  have hcardUnion : (P.1 ∪ codeStageRows c).card = s + t := by
    rw [Finset.card_union_of_disjoint hdisj, hPcard, hrowsCard]
  have hle : s + t <= h := by
    rw [← hcardUnion]
    simpa [Fintype.card_fin] using
      (Finset.card_le_univ (P.1 ∪ codeStageRows c) :
        (P.1 ∪ codeStageRows c).card <= Fintype.card (Fin h))
  exact (Nat.not_lt_of_ge hle) hfit

/-- In the S2131 `SimpleDNF` row-capacity regime, every realized code is a
row-collision code. -/
theorem realizedBadPathCodes_eq_rowCollisionRealizedBadPathCodes_of_simple_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (hfit : h < s + t) :
    realizedBadPathCodes (h := h) (s := s) (t := t) tvs =
      rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs := by
  rw [realizedBadPathCodes_eq_rowVarUnique_union_rowCollision
    (h := h) (s := s) (t := t) tvs]
  rw [rowVarUniqueRealizedBadPathCodes_eq_empty_of_simple_of_h_lt_s_add_t
    (h := h) (s := s) (t := t) tvs hsimple hfit]
  rw [Finset.empty_union]

/-- Cardinality form: in the S2131 row-capacity regime, the row-collision class
has exactly the full realized-code cardinality. -/
theorem rowCollisionRealizedBadPathCodes_card_eq_realizedBadPathCodes_card_of_simple_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (hfit : h < s + t) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card =
      (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card := by
  exact congrArg Finset.card
    (realizedBadPathCodes_eq_rowCollisionRealizedBadPathCodes_of_simple_of_h_lt_s_add_t
      (h := h) (s := s) (t := t) tvs hsimple hfit).symm

/-- The S2127 realized-code finite probability wrapper may be stated using only
the row-collision cardinality in the S2131 row-capacity regime. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_simple_rowCollision_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (hfit : h < s + t) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
      ((rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card *
        (h - s) ^ (t / h)) (h ^ (t / h)) := by
  have hprob := canonicalDepthBad_eventProbLe_geometric_of_simple_realizedCode_div_h
    (h := h) (s := s) (t := t) tvs hsimple
  have hcard :=
    rowCollisionRealizedBadPathCodes_card_eq_realizedBadPathCodes_card_of_simple_of_h_lt_s_add_t
      (h := h) (s := s) (t := t) tvs hsimple hfit
  simpa [hcard] using hprob

/-! ## Concrete row-collision obstruction -/

private theorem twoRowsTwoColsCode_row0_stage0_row_col :
    codeStageRow twoRowsTwoColsCode_row0_h2_t2 (0 : Fin 2) = (0 : Fin 2) ∧
      (codeStageEntry twoRowsTwoColsCode_row0_h2_t2 (0 : Fin 2)).2.1 = (0 : Fin 2) := by
  have hvar := codeStageEntry_var_eq twoRowsTwoColsCode_row0_h2_t2 (0 : Fin 2)
  simp [twoRowsTwoColsCode_row0_h2_t2] at hvar
  exact phpVar_inj hvar

private theorem twoRowsTwoColsCode_row0_stage1_row_col :
    codeStageRow twoRowsTwoColsCode_row0_h2_t2 (1 : Fin 2) = (0 : Fin 2) ∧
      (codeStageEntry twoRowsTwoColsCode_row0_h2_t2 (1 : Fin 2)).2.1 = (1 : Fin 2) := by
  have hvar := codeStageEntry_var_eq twoRowsTwoColsCode_row0_h2_t2 (1 : Fin 2)
  simp [twoRowsTwoColsCode_row0_h2_t2] at hvar
  exact phpVar_inj hvar

private theorem twoRowsTwoColsCode_row1_stage0_row_col :
    codeStageRow twoRowsTwoColsCode_row1_h2_t2 (0 : Fin 2) = (1 : Fin 2) ∧
      (codeStageEntry twoRowsTwoColsCode_row1_h2_t2 (0 : Fin 2)).2.1 = (0 : Fin 2) := by
  have hvar := codeStageEntry_var_eq twoRowsTwoColsCode_row1_h2_t2 (0 : Fin 2)
  simp [twoRowsTwoColsCode_row1_h2_t2] at hvar
  exact phpVar_inj hvar

private theorem twoRowsTwoColsCode_row1_stage1_row_col :
    codeStageRow twoRowsTwoColsCode_row1_h2_t2 (1 : Fin 2) = (1 : Fin 2) ∧
      (codeStageEntry twoRowsTwoColsCode_row1_h2_t2 (1 : Fin 2)).2.1 = (1 : Fin 2) := by
  have hvar := codeStageEntry_var_eq twoRowsTwoColsCode_row1_h2_t2 (1 : Fin 2)
  simp [twoRowsTwoColsCode_row1_h2_t2] at hvar
  exact phpVar_inj hvar

/-- The row-0 realized code from S2128 is a row-collision code: both stages use
row `0`, but with columns `0` and `1`. -/
theorem twoRowsTwoColsCode_row0_h2_t2_codeRowCollision :
    CodeRowCollision twoRowsTwoColsCode_row0_h2_t2 := by
  refine ⟨(0 : Fin 2), (1 : Fin 2), ?_, ?_⟩
  · rw [twoRowsTwoColsCode_row0_stage0_row_col.1,
      twoRowsTwoColsCode_row0_stage1_row_col.1]
  · intro hcol
    have hbad : (0 : Fin 2) = (1 : Fin 2) := by
      rw [← twoRowsTwoColsCode_row0_stage0_row_col.2, hcol,
        twoRowsTwoColsCode_row0_stage1_row_col.2]
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hbad

/-- The row-1 realized code from S2128 is a row-collision code: both stages use
row `1`, but with columns `0` and `1`. -/
theorem twoRowsTwoColsCode_row1_h2_t2_codeRowCollision :
    CodeRowCollision twoRowsTwoColsCode_row1_h2_t2 := by
  refine ⟨(0 : Fin 2), (1 : Fin 2), ?_, ?_⟩
  · rw [twoRowsTwoColsCode_row1_stage0_row_col.1,
      twoRowsTwoColsCode_row1_stage1_row_col.1]
  · intro hcol
    have hbad : (0 : Fin 2) = (1 : Fin 2) := by
      rw [← twoRowsTwoColsCode_row1_stage0_row_col.2, hcol,
        twoRowsTwoColsCode_row1_stage1_row_col.2]
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hbad

/-- At least two row-collision canonical bad-path codes are realized in the S2128
two-row/two-column SimpleDNF witness. -/
theorem twoRowsTwoCols_rowCollisionRealizedBadPathCodes_card_ge_two :
    2 <=
      (rowCollisionRealizedBadPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card := by
  classical
  let R := rowCollisionRealizedBadPathCodes (h := 2) (s := 1) (t := 2)
    twoRowsTwoColsTvs_h2
  let A : Finset (BadPathCode 2 twoRowsTwoColsTvs_h2 2) :=
    {twoRowsTwoColsCode_row0_h2_t2, twoRowsTwoColsCode_row1_h2_t2}
  have hsubset : A ⊆ R := by
    intro c hc
    simp [A] at hc
    rcases hc with hc | hc
    · subst hc
      exact (mem_rowCollisionRealizedBadPathCodes
        (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2
        twoRowsTwoColsCode_row0_h2_t2).mpr
        ⟨twoRowsTwoColsCode_row0_h2_t2_mem_realized,
          twoRowsTwoColsCode_row0_h2_t2_codeRowCollision⟩
    · subst hc
      exact (mem_rowCollisionRealizedBadPathCodes
        (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2
        twoRowsTwoColsCode_row1_h2_t2).mpr
        ⟨twoRowsTwoColsCode_row1_h2_t2_mem_realized,
          twoRowsTwoColsCode_row1_h2_t2_codeRowCollision⟩
  have hcard : A.card = 2 := by
    simp [A, twoRowsTwoColsCode_row0_ne_row1_h2_t2]
  calc
    2 = A.card := hcard.symm
    _ <= R.card := Finset.card_le_card hsubset

/-- The S2127 denominator is no larger than the row-collision realized-code count
in the concrete two-by-two witness. -/
theorem twoRowsTwoCols_denominator_le_rowCollisionRealizedBadPathCodes_card :
    2 ^ (2 / 2) <=
      (rowCollisionRealizedBadPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card := by
  simpa using twoRowsTwoCols_rowCollisionRealizedBadPathCodes_card_ge_two

/-- Therefore no SimpleDNF-only theorem can force the row-collision realized-code
count below the displayed S2127 denominator in this concrete witness. -/
theorem twoRowsTwoCols_not_rowCollisionRealizedBadPathCodes_card_lt_denominator :
    ¬ (rowCollisionRealizedBadPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card < 2 ^ (2 / 2) := by
  exact not_lt_of_ge twoRowsTwoCols_denominator_le_rowCollisionRealizedBadPathCodes_card

/-- Direct obstruction form for the collision-factor route in the concrete
two-by-two witness. -/
theorem twoRowsTwoCols_rowCollision_route_nontrivial_impossible :
    ¬ ((rowCollisionRealizedBadPathCodes (h := 2) (s := 1) (t := 2)
          twoRowsTwoColsTvs_h2).card *
        (2 - 1) ^ (2 / 2) < 2 ^ (2 / 2)) := by
  have hden := twoRowsTwoCols_denominator_le_rowCollisionRealizedBadPathCodes_card
  exact not_lt_of_ge (by simpa using hden)

/-- With one PHP column, row collisions are impossible.  Thus the two-column
S2128 witness is smallest in the column-count direction. -/
theorem not_codeRowCollision_h_one {t : Nat}
    {tvs : List (List (Fin 1 × Fin 1 × Bool))}
    (c : BadPathCode 1 tvs t) :
    ¬ CodeRowCollision c := by
  rintro ⟨_k, _l, _hrow, hne⟩
  exact hne (Subsingleton.elim _ _)

/-- Consequently, over `h = 1`, the row-collision realized-code class is empty
for every square full-matching parameter choice. -/
theorem rowCollisionRealizedBadPathCodes_eq_empty_h_one {s t : Nat}
    (tvs : List (List (Fin 1 × Fin 1 × Bool))) :
    rowCollisionRealizedBadPathCodes (h := 1) (s := s) (t := t) tvs = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  exact not_codeRowCollision_h_one c
    ((mem_rowCollisionRealizedBadPathCodes (h := 1) (s := s) (t := t) tvs c).mp hc).2

end PHPFullMatchingRealizedCodeSplit
end PvNP
