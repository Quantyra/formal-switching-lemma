import PvNP.PHPFullMatchingGateARouteDecision

/-!
# Gate-A realized-code path split

Finite square full-matching realized-code bookkeeping only.  This module splits
the realized canonical bad-path code set into codes that satisfy the S2135
row-to-variable functionality predicate and codes that do not.  It records that
the S2136 `h = 2, s = 1, t = 2` cross-term counterexample is classified on the
bad side, while an empty bad side recovers the existing denominator-control
route.

No PHP switching lemma, Frege/PHP lower bound, rectangular `p > h` result,
NP/circuit lower bound, arbitrary AC0 result, natural-syntax theorem, or P-vs-NP
claim is stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateARealizedCodePathSplit

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingGateAInvariant
open PHPFullMatchingGateANaturalInvariant
open PHPFullMatchingGateACanonicalRowDiscipline
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeSplit
open PHPFullMatchingRowUniqueStrict
open PHPFullMatchingStageRows
open PHPFullMatchingGateARouteDecision
open SwitchingEncodeConstruct

/-! ## Realized-code split definitions -/

/-- A good realized code is a realized canonical bad-path code whose recovered
rows functionally determine the stored PHP variable. -/
def GoodRealizedCode {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) : Prop :=
  c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ∧
    CodeRowToVarFunctional c

/-- A bad realized code is a realized canonical bad-path code that fails the
row-to-variable functionality predicate. -/
def BadRealizedCode {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) : Prop :=
  c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ∧
    ¬ CodeRowToVarFunctional c

/-- Finite set of good realized path codes. -/
noncomputable def goodRealizedPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Finset (BadPathCode h tvs t) :=
  by
    classical
    exact (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).filter
      (fun c => CodeRowToVarFunctional c)

/-- Finite set of bad realized path codes. -/
noncomputable def badRealizedPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Finset (BadPathCode h tvs t) :=
  by
    classical
    exact (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).filter
      (fun c => ¬ CodeRowToVarFunctional c)

theorem mem_goodRealizedPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) :
    c ∈ goodRealizedPathCodes (h := h) (s := s) (t := t) tvs ↔
      GoodRealizedCode (h := h) (s := s) (t := t) tvs c := by
  classical
  simp [goodRealizedPathCodes, GoodRealizedCode]

theorem mem_badRealizedPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (c : BadPathCode h tvs t) :
    c ∈ badRealizedPathCodes (h := h) (s := s) (t := t) tvs ↔
      BadRealizedCode (h := h) (s := s) (t := t) tvs c := by
  classical
  simp [badRealizedPathCodes, BadRealizedCode]

/-- The realized-code set is exactly the union of good and bad realized codes. -/
theorem realizedBadPathCodes_eq_good_union_bad {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    realizedBadPathCodes (h := h) (s := s) (t := t) tvs =
      goodRealizedPathCodes (h := h) (s := s) (t := t) tvs ∪
        badRealizedPathCodes (h := h) (s := s) (t := t) tvs := by
  classical
  ext c
  constructor
  · intro hc
    by_cases hfun : CodeRowToVarFunctional c
    · exact Finset.mem_union.mpr <| Or.inl <|
        (mem_goodRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mpr
          ⟨hc, hfun⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        (mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mpr
          ⟨hc, hfun⟩
  · intro hc
    rcases Finset.mem_union.mp hc with hgood | hbad
    · exact ((mem_goodRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mp hgood).1
    · exact ((mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mp hbad).1

/-- Good and bad realized-code classes are disjoint. -/
theorem disjoint_goodRealizedPathCodes_badRealizedPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Disjoint
      (goodRealizedPathCodes (h := h) (s := s) (t := t) tvs)
      (badRealizedPathCodes (h := h) (s := s) (t := t) tvs) := by
  classical
  rw [Finset.disjoint_left]
  intro c hgood hbad
  have hfun := ((mem_goodRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mp hgood).2
  have hnfun := ((mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mp hbad).2
  exact hnfun hfun

/-! ## Good paths recover row uniqueness and denominator control -/

theorem codeRowVarUnique_of_goodRealizedCode {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {c : BadPathCode h tvs t}
    (hgood : GoodRealizedCode (h := h) (s := s) (t := t) tvs c) :
    CodeRowVarUnique c :=
  codeRowVarUnique_of_codeRowToVarFunctional hgood.2

theorem not_codeRowCollision_of_goodRealizedCode {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {c : BadPathCode h tvs t}
    (hgood : GoodRealizedCode (h := h) (s := s) (t := t) tvs c) :
    ¬ CodeRowCollision c := by
  intro hcoll
  exact (codeRowCollision_iff_not_codeRowVarUnique c).mp hcoll
    (codeRowVarUnique_of_goodRealizedCode hgood)

theorem badRealizedPathCodes_eq_empty_iff_realizedCodeRowToVarFunctional {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    badRealizedPathCodes (h := h) (s := s) (t := t) tvs = ∅ ↔
      RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  classical
  constructor
  · intro hempty c hc
    by_contra hnfun
    have hmem : c ∈ badRealizedPathCodes (h := h) (s := s) (t := t) tvs :=
      (mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mpr ⟨hc, hnfun⟩
    rw [hempty] at hmem
    exact Finset.not_mem_empty c hmem
  · intro hfun
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    have hbad := (mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mp hc
    exact hbad.2 (hfun c hbad.1)

theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_badRealizedPathCodes_eq_empty
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hempty : badRealizedPathCodes (h := h) (s := s) (t := t) tvs = ∅)
    (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) :=
  rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowToVarFunctionalFromSyntax
    (h := h) (s := s) (t := t) tvs
    ((badRealizedPathCodes_eq_empty_iff_realizedCodeRowToVarFunctional
      (h := h) (s := s) (t := t) tvs).mp hempty) hden

/-! ## S2136 cross-term witness classification -/

theorem crossTermRowCode_h2_t2_not_codeRowToVarFunctional :
    ¬ CodeRowToVarFunctional crossTermRowCode_h2_t2 := by
  intro hfun
  have huniq : CodeRowVarUnique crossTermRowCode_h2_t2 :=
    codeRowVarUnique_of_codeRowToVarFunctional hfun
  exact (codeRowCollision_iff_not_codeRowVarUnique crossTermRowCode_h2_t2).mp
    crossTermRowCode_h2_t2_rowCollision huniq

theorem crossTermRowCode_h2_t2_mem_badRealizedPathCodes :
    crossTermRowCode_h2_t2 ∈
      badRealizedPathCodes (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 :=
  (mem_badRealizedPathCodes (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2
    crossTermRowCode_h2_t2).mpr
    ⟨crossTermRowCode_h2_t2_mem_realized,
      crossTermRowCode_h2_t2_not_codeRowToVarFunctional⟩

theorem crossTermRowCode_h2_t2_not_mem_goodRealizedPathCodes :
    crossTermRowCode_h2_t2 ∉
      goodRealizedPathCodes (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 := by
  intro hgoodMem
  exact crossTermRowCode_h2_t2_not_codeRowToVarFunctional
    ((mem_goodRealizedPathCodes (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2
      crossTermRowCode_h2_t2).mp hgoodMem).2

/-- Pivot pin: the S2136 counterexample is bad, and if the bad side is empty in
any finite square full-matching instance, the existing row-collision denominator
control theorem applies. -/
theorem gateA_realizedCodePathSplit_pivot_consequence :
    crossTermRowCode_h2_t2 ∈
        badRealizedPathCodes (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 ∧
      ∀ {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool))),
        badRealizedPathCodes (h := h) (s := s) (t := t) tvs = ∅ ->
        0 < h ^ (t / h) ->
        (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
          h ^ (t / h) :=
  ⟨crossTermRowCode_h2_t2_mem_badRealizedPathCodes,
    fun tvs hempty hden =>
      rowCollisionRealizedBadPathCodes_card_lt_denominator_of_badRealizedPathCodes_eq_empty
        tvs hempty hden⟩

end PHPFullMatchingGateARealizedCodePathSplit
end PvNP
