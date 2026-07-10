import PvNP.PHPFullMatchingGateANaturalInvariant

/-!
# Gate-A canonical row discipline

Finite square full-matching realized-code bookkeeping only.  This module derives
the S2134 row-to-variable functionality surface from a syntactic cross-term
row-variable compatibility discipline, and records bounded no-go obstructions for
weaker local row-uniqueness hypotheses.

No PHP switching lemma, Frege/PHP lower bound, rectangular `p > h` result,
NP/circuit lower bound, arbitrary AC0 result, or P-vs-NP claim is stated or
proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateACanonicalRowDiscipline

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingDistribution
open PHPFullMatchingGateAInvariant
open PHPFullMatchingGateANaturalInvariant
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeObstruction
open PHPFullMatchingRealizedCodeParametricObstruction
open PHPFullMatchingRealizedCodeSplit
open PHPFullMatchingRowUniqueStrict
open PHPFullMatchingStageRows
open PHPMatchingDistribution
open PHPSearchFloor
open RestrictedPHPFloor
open SwitchingEncodeConstruct

/-! ## Syntactic and collision-free disciplines -/

/-- Cross-term row-variable compatibility: any two literal entries in any two
terms with the same PHP row use the same PHP column. -/
def PHPDNFTermPairRowVarCompatible {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ tv₁ ∈ tvs, ∀ tv₂ ∈ tvs, ∀ e₁ ∈ tv₁, ∀ e₂ ∈ tv₂,
    e₁.1 = e₂.1 -> e₁.2.1 = e₂.2.1

/-- Every canonical code extracted from a bad full-matching point is free of
explicit same-row/different-column collisions. -/
def CanonicalMatchingCodeRowCollisionFree {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ P ∈ fullMatchingSpace h s, ∀ hbad : canonicalDepthBad h tvs t P,
    ¬ CodeRowCollision (canonicalDepthBadCode tvs t P hbad)

/-- Every realized canonical bad-path code is free of explicit
same-row/different-column collisions. -/
def RealizedCodeRowCollisionFree {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ c : BadPathCode h tvs t,
    c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ->
      ¬ CodeRowCollision c

/-- Canonical bad-path row compatibility: every canonical code extracted from a
bad full-matching point satisfies row-to-variable functionality. -/
abbrev CanonicalPathRowCompatible {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs

/-- Realized-code row-to-variable functionality candidate from syntax.  This is
the named S2135 surface for the existing S2134 realized functionality predicate. -/
abbrev RealizedCodeRowToVarFunctionalFromSyntax {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs

/-! ## Positive implications -/

theorem codeRowToVarFunctional_of_codeRowVarUnique {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    {c : BadPathCode h tvs t} :
    CodeRowVarUnique c -> CodeRowToVarFunctional c := by
  intro huniq k l hrow
  exact codeStageVar_eq_of_codeRowVarUnique_row_eq huniq hrow

theorem realizedCodeRowToVarFunctional_of_realizedCodeRowVarUnique {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} :
    RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs ->
      RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  intro huniq c hc
  exact codeRowToVarFunctional_of_codeRowVarUnique (huniq c hc)

theorem realizedCodeRowVarUnique_of_realizedCodeRowCollisionFree {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} :
    RealizedCodeRowCollisionFree (h := h) (s := s) (t := t) tvs ->
      RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs := by
  intro hfree c hc
  by_contra hnot
  exact hfree c hc ((codeRowCollision_iff_not_codeRowVarUnique c).mpr hnot)

theorem realizedCodeRowToVarFunctional_of_realizedCodeRowCollisionFree {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} :
    RealizedCodeRowCollisionFree (h := h) (s := s) (t := t) tvs ->
      RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  intro hfree
  exact realizedCodeRowToVarFunctional_of_realizedCodeRowVarUnique
    (realizedCodeRowVarUnique_of_realizedCodeRowCollisionFree hfree)

theorem canonicalMatchingCodeRowToVarFunctional_of_canonicalCodeRowCollisionFree
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))} :
    CanonicalMatchingCodeRowCollisionFree (h := h) (s := s) (t := t) tvs ->
      CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  intro hfree P hP hbad
  apply codeRowToVarFunctional_of_codeRowVarUnique
  by_contra hnot
  exact hfree P hP hbad ((codeRowCollision_iff_not_codeRowVarUnique
    (canonicalDepthBadCode tvs t P hbad)).mpr hnot)

theorem canonicalMatchingCodeRowToVarFunctional_of_canonicalPathRowCompatible
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))} :
    CanonicalPathRowCompatible (h := h) (s := s) (t := t) tvs ->
      CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs :=
  id

theorem realizedCodeRowVarUnique_of_canonicalPathRowCompatible
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))} :
    CanonicalPathRowCompatible (h := h) (s := s) (t := t) tvs ->
      RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs :=
  realizedCodeRowVarUnique_of_canonicalMatchingCodeRowToVarFunctional

theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_canonicalPathRowCompatible
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hcompat : CanonicalPathRowCompatible (h := h) (s := s) (t := t) tvs)
    (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) :=
  rowCollisionRealizedBadPathCodes_card_lt_denominator_of_canonicalMatchingCodeRowToVarFunctional
    (h := h) (s := s) (t := t) tvs hcompat hden

theorem realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctionalFromSyntax
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))} :
    RealizedCodeRowToVarFunctionalFromSyntax (h := h) (s := s) (t := t) tvs ->
      RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs :=
  realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional

theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowToVarFunctionalFromSyntax
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hfun : RealizedCodeRowToVarFunctionalFromSyntax (h := h) (s := s) (t := t) tvs)
    (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) :=
  rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowVarUnique
    (h := h) (s := s) (t := t) tvs
    (realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctionalFromSyntax hfun) hden

theorem rowVarCapacityOne_of_termPairRowVarCompatible {h : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hcompat : PHPDNFTermPairRowVarCompatible tvs) :
    PHPDNFRowVarCapacityOne tvs := by
  intro e₁ he₁ e₂ he₂ hrow
  rw [List.mem_join] at he₁ he₂
  rcases he₁ with ⟨tv₁, htv₁, he₁tv⟩
  rcases he₂ with ⟨tv₂, htv₂, he₂tv⟩
  exact hcompat tv₁ htv₁ tv₂ htv₂ e₁ he₁tv e₂ he₂tv hrow

theorem canonicalMatchingCodeRowToVarFunctional_of_termPairRowVarCompatible
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))}
    (hcompat : PHPDNFTermPairRowVarCompatible tvs) :
    CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  intro P _hP hbad k l hrow
  exact codeStageVar_eq_of_globalRowVarUnique_row_eq
    (rowVarCapacityOne_of_termPairRowVarCompatible hcompat)
    (canonicalDepthBadCode tvs t P hbad) hrow

theorem realizedCodeRowToVarFunctional_of_termPairRowVarCompatible
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))}
    (hcompat : PHPDNFTermPairRowVarCompatible tvs) :
    RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs :=
  realizedCodeRowToVarFunctional_of_rowVarCapacityOne
    (rowVarCapacityOne_of_termPairRowVarCompatible hcompat)

theorem realizedCodeRowVarUnique_of_termPairRowVarCompatible
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))}
    (hcompat : PHPDNFTermPairRowVarCompatible tvs) :
    RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs :=
  realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional
    (realizedCodeRowToVarFunctional_of_termPairRowVarCompatible
      (h := h) (s := s) (t := t) hcompat)

theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_termPairRowVarCompatible
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hcompat : PHPDNFTermPairRowVarCompatible tvs) (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) :=
  rowCollisionRealizedBadPathCodes_card_lt_denominator_of_rowVarCapacityOne
    (h := h) (s := s) (t := t) tvs
    (rowVarCapacityOne_of_termPairRowVarCompatible hcompat) hden

/-! ## No-go obstructions for weaker local disciplines -/

theorem fullRowTvs_not_termPairRowVarCompatible {h : Nat} (hh : 2 <= h) :
    ¬ PHPDNFTermPairRowVarCompatible (fullRowTvs h) := by
  intro hcompat
  exact fullRowTvs_not_rowVarCapacityOne (h := h) hh
    (rowVarCapacityOne_of_termPairRowVarCompatible hcompat)

theorem crossTermRowTvs_h2_not_termPairRowVarCompatible :
    ¬ PHPDNFTermPairRowVarCompatible crossTermRowTvs_h2 := by
  intro hcompat
  have hEq := hcompat
    [((0 : Fin 2), (0 : Fin 2), true)] (by simp [crossTermRowTvs_h2])
    [((0 : Fin 2), (1 : Fin 2), true)] (by simp [crossTermRowTvs_h2])
    ((0 : Fin 2), (0 : Fin 2), true) (by simp)
    ((0 : Fin 2), (1 : Fin 2), true) (by simp) rfl
  exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hEq

theorem crossTermRowTvs_h2_not_realizedCodeRowToVarFunctional :
    ¬ RealizedCodeRowToVarFunctional (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 := by
  intro hfun
  exact crossTermRowTvs_h2_not_realizedCodeRowVarUnique
    (realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional hfun)

theorem crossTermRowTvs_h2_not_canonicalMatchingCodeRowToVarFunctional :
    ¬ CanonicalMatchingCodeRowToVarFunctional (h := 2) (s := 1) (t := 2)
      crossTermRowTvs_h2 := by
  intro hcan
  exact crossTermRowTvs_h2_not_realizedCodeRowVarUnique
    (realizedCodeRowVarUnique_of_canonicalMatchingCodeRowToVarFunctional hcan)

theorem fullRowTvs_not_canonicalPathRowCompatible {h : Nat} (hh : 2 <= h) :
    ¬ CanonicalPathRowCompatible (h := h) (s := h - 1) (t := h) (fullRowTvs h) :=
  fullRowTvs_not_canonicalMatchingCodeRowToVarFunctional (h := h) hh

theorem crossTermRowTvs_h2_not_canonicalPathRowCompatible :
    ¬ CanonicalPathRowCompatible (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 :=
  crossTermRowTvs_h2_not_canonicalMatchingCodeRowToVarFunctional

theorem fullRowTvs_not_canonicalMatchingCodeRowCollisionFree {h : Nat} (hh : 2 <= h) :
    ¬ CanonicalMatchingCodeRowCollisionFree (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
  intro hfree
  exact fullRowTvs_not_canonicalMatchingCodeRowToVarFunctional (h := h) hh
    (canonicalMatchingCodeRowToVarFunctional_of_canonicalCodeRowCollisionFree hfree)

theorem fullRowTvs_not_realizedCodeRowCollisionFree {h : Nat} (hh : 2 <= h) :
    ¬ RealizedCodeRowCollisionFree (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
  intro hfree
  exact fullRowTvs_not_realizedCodeRowVarUnique (h := h) hh
    (realizedCodeRowVarUnique_of_realizedCodeRowCollisionFree hfree)

theorem crossTermRowTvs_h2_not_canonicalMatchingCodeRowCollisionFree :
    ¬ CanonicalMatchingCodeRowCollisionFree (h := 2) (s := 1) (t := 2)
      crossTermRowTvs_h2 := by
  intro hfree
  exact crossTermRowTvs_h2_not_canonicalMatchingCodeRowToVarFunctional
    (canonicalMatchingCodeRowToVarFunctional_of_canonicalCodeRowCollisionFree hfree)

theorem crossTermRowTvs_h2_not_realizedCodeRowCollisionFree :
    ¬ RealizedCodeRowCollisionFree (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 := by
  intro hfree
  exact crossTermRowTvs_h2_not_realizedCodeRowVarUnique
    (realizedCodeRowVarUnique_of_realizedCodeRowCollisionFree hfree)

theorem fullRowTvs_not_realizedCodeRowToVarFunctionalFromSyntax {h : Nat} (hh : 2 <= h) :
    ¬ RealizedCodeRowToVarFunctionalFromSyntax (h := h) (s := h - 1) (t := h)
      (fullRowTvs h) :=
  fullRowTvs_not_realizedCodeRowToVarFunctional (h := h) hh

theorem crossTermRowTvs_h2_not_realizedCodeRowToVarFunctionalFromSyntax :
    ¬ RealizedCodeRowToVarFunctionalFromSyntax (h := 2) (s := 1) (t := 2)
      crossTermRowTvs_h2 :=
  crossTermRowTvs_h2_not_realizedCodeRowToVarFunctional

theorem termRowVarUnique_not_implies_realizedCodeRowToVarFunctional_h2_s1_t2 :
    PHPDNFTermRowVarUnique crossTermRowTvs_h2 ∧
      ¬ RealizedCodeRowToVarFunctional (h := 2) (s := 1) (t := 2)
        crossTermRowTvs_h2 :=
  ⟨crossTermRowTvs_h2_termRowVarUnique,
    crossTermRowTvs_h2_not_realizedCodeRowToVarFunctional⟩

theorem termRowVarUnique_not_implies_canonicalMatchingCodeRowToVarFunctional_h2_s1_t2 :
    PHPDNFTermRowVarUnique crossTermRowTvs_h2 ∧
      ¬ CanonicalMatchingCodeRowToVarFunctional (h := 2) (s := 1) (t := 2)
        crossTermRowTvs_h2 :=
  ⟨crossTermRowTvs_h2_termRowVarUnique,
    crossTermRowTvs_h2_not_canonicalMatchingCodeRowToVarFunctional⟩

end PHPFullMatchingGateACanonicalRowDiscipline
end PvNP
