import PvNP.PHPFullMatchingGateAInvariant

/-!
# Gate-A natural row-variable invariants

Finite square full-matching realized-code bookkeeping only.  This module relates
whole-DNF and canonical-code row-to-variable functional disciplines to the
S2133 realized-code row-variable invariant.  It also records bounded finite
obstructions showing that these disciplines are genuine extra hypotheses.

No PHP switching lemma, Frege/PHP lower bound, rectangular `p > h` result,
NP/circuit lower bound, arbitrary AC0 result, or P-vs-NP claim is stated or
proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateANaturalInvariant

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingDistribution
open PHPFullMatchingGateAInvariant
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeObstruction
open PHPFullMatchingRealizedCodeParametricObstruction
open PHPFullMatchingRealizedCodeSplit
open PHPFullMatchingRowUniqueStrict
open PHPFullMatchingStageRows
open PHPMatchingDistribution
open PHPSearchFloor
open RestrictedPHPFloor
open SwitchingLemmaStatement
open SwitchingEncodeConstruct
open BoundedDepthCanonicalDT
open BoundedDepthDecisionTree
open SwitchingTermCanonicalDT

/-! ## Natural row-to-variable disciplines -/

/-- Whole-DNF per-row PHP variable capacity one: across the joined DNF
literal-value list, same-row entries use the same PHP column. -/
abbrev PHPDNFRowVarCapacityOne {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  PHPDNFGlobalRowVarUnique tvs

/-- Per-term row-variable uniqueness: inside each PHP term, same-row entries use
the same PHP column. -/
def PHPDNFTermRowVarUnique {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ tv ∈ tvs, ∀ e₁ ∈ tv, ∀ e₂ ∈ tv, e₁.1 = e₂.1 -> e₁.2.1 = e₂.2.1

/-- A code-local row-to-variable functionality condition: equal decoded stage
rows force the same stored PHP variable. -/
def CodeRowToVarFunctional {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) : Prop :=
  ∀ k l : Fin t,
    codeStageRow c k = codeStageRow c l ->
      ((c k).1 : Fin (Nat.succ (h * h))) = ((c l).1 : Fin (Nat.succ (h * h)))

/-- Every realized canonical bad-path code satisfies row-to-variable
functionality. -/
def RealizedCodeRowToVarFunctional {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ c : BadPathCode h tvs t,
    c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ->
      CodeRowToVarFunctional c

/-- Every canonical code extracted from a bad full-matching point satisfies
row-to-variable functionality. -/
def CanonicalMatchingCodeRowToVarFunctional {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ P ∈ fullMatchingSpace h s, ∀ hbad : canonicalDepthBad h tvs t P,
    CodeRowToVarFunctional (canonicalDepthBadCode tvs t P hbad)

/-! ## Positive implications -/

/-- Row-to-variable functionality implies code-local row-variable uniqueness. -/
theorem codeRowVarUnique_of_codeRowToVarFunctional {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    {c : BadPathCode h tvs t} :
    CodeRowToVarFunctional c -> CodeRowVarUnique c := by
  intro hfun k l hrow
  have hvar := hfun k l hrow
  have hphp : phpVar h h (codeStageRow c k) (codeStageEntry c k).2.1 =
      phpVar h h (codeStageRow c l) (codeStageEntry c l).2.1 := by
    simpa [codeStageEntry_var_eq c k, codeStageEntry_var_eq c l] using hvar
  exact (phpVar_inj hphp).2

theorem realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} :
    RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs ->
      RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs := by
  intro hfun c hc
  exact codeRowVarUnique_of_codeRowToVarFunctional (hfun c hc)

theorem realizedCodeRowToVarFunctional_of_rowVarCapacityOne {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hcap : PHPDNFRowVarCapacityOne tvs) :
    RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  intro c _hc k l hrow
  exact codeStageVar_eq_of_globalRowVarUnique_row_eq hcap c hrow

theorem realizedCodeRowVarUnique_of_rowVarCapacityOne {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hcap : PHPDNFRowVarCapacityOne tvs) :
    RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs :=
  realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional
    (realizedCodeRowToVarFunctional_of_rowVarCapacityOne (h := h) (s := s) (t := t) hcap)

theorem realizedCodeRowToVarFunctional_of_canonicalMatchingCodeRowToVarFunctional
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))}
    (hcan : CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs) :
    RealizedCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs := by
  classical
  intro c hc
  have hreal := (mem_realizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mp hc
  rcases hreal with ⟨P, hP⟩
  rw [canonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨hspace, hbad, henc⟩ := hP
  have hcEq : canonicalDepthBadCode tvs t P hbad = c := by
    unfold canonicalDepthBadEncoding at henc
    rw [dif_pos hbad] at henc
    exact Option.some.inj henc
  simpa [hcEq] using hcan P hspace hbad

theorem realizedCodeRowVarUnique_of_canonicalMatchingCodeRowToVarFunctional
    {h s t : Nat} {tvs : List (List (Fin h × Fin h × Bool))}
    (hcan : CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs) :
    RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs :=
  realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional
    (realizedCodeRowToVarFunctional_of_canonicalMatchingCodeRowToVarFunctional hcan)

theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_rowVarCapacityOne
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hcap : PHPDNFRowVarCapacityOne tvs) (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) :=
  rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowVarUnique
    (h := h) (s := s) (t := t) tvs
    (realizedCodeRowVarUnique_of_rowVarCapacityOne (h := h) (s := s) (t := t) hcap) hden

theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_canonicalMatchingCodeRowToVarFunctional
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hcan : CanonicalMatchingCodeRowToVarFunctional (h := h) (s := s) (t := t) tvs)
    (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) :=
  rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowVarUnique
    (h := h) (s := s) (t := t) tvs
    (realizedCodeRowVarUnique_of_canonicalMatchingCodeRowToVarFunctional hcan) hden

/-! ## S2132 full-row tests -/

theorem fullRowTvs_not_rowVarCapacityOne {h : Nat} (hh : 2 <= h) :
    ¬ PHPDNFRowVarCapacityOne (fullRowTvs h) := by
  classical
  intro hcap
  let r : Fin h := ⟨0, by omega⟩
  let c0 : Fin h := ⟨0, by omega⟩
  let c1 : Fin h := ⟨1, by omega⟩
  have hm0 : (r, c0, true) ∈ (fullRowTvs h).join := by
    rw [List.mem_join]
    exact ⟨fullRowTerm h r, by rw [mem_fullRowTvs_iff]; exact ⟨r, rfl⟩, by
      unfold fullRowTerm; rw [List.mem_ofFn]; exact ⟨c0, rfl⟩⟩
  have hm1 : (r, c1, true) ∈ (fullRowTvs h).join := by
    rw [List.mem_join]
    exact ⟨fullRowTerm h r, by rw [mem_fullRowTvs_iff]; exact ⟨r, rfl⟩, by
      unfold fullRowTerm; rw [List.mem_ofFn]; exact ⟨c1, rfl⟩⟩
  have hEq := hcap (r, c0, true) hm0 (r, c1, true) hm1 rfl
  have hNe : c0 ≠ c1 := by
    intro hc
    exact Nat.zero_ne_one (Fin.ext_iff.mp hc)
  exact hNe hEq

theorem fullRowTvs_not_termRowVarUnique {h : Nat} (hh : 2 <= h) :
    ¬ PHPDNFTermRowVarUnique (fullRowTvs h) := by
  classical
  intro huniq
  let r : Fin h := ⟨0, by omega⟩
  let c0 : Fin h := ⟨0, by omega⟩
  let c1 : Fin h := ⟨1, by omega⟩
  have htv : fullRowTerm h r ∈ fullRowTvs h := by
    rw [mem_fullRowTvs_iff]
    exact ⟨r, rfl⟩
  have hm0 : (r, c0, true) ∈ fullRowTerm h r := by
    unfold fullRowTerm; rw [List.mem_ofFn]; exact ⟨c0, rfl⟩
  have hm1 : (r, c1, true) ∈ fullRowTerm h r := by
    unfold fullRowTerm; rw [List.mem_ofFn]; exact ⟨c1, rfl⟩
  have hEq := huniq (fullRowTerm h r) htv (r, c0, true) hm0 (r, c1, true) hm1 rfl
  have hNe : c0 ≠ c1 := by
    intro hc
    exact Nat.zero_ne_one (Fin.ext_iff.mp hc)
  exact hNe hEq

theorem fullRowTvs_not_realizedCodeRowToVarFunctional {h : Nat} (hh : 2 <= h) :
    ¬ RealizedCodeRowToVarFunctional (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
  intro hfun
  exact fullRowTvs_not_realizedCodeRowVarUnique (h := h) hh
    (realizedCodeRowVarUnique_of_realizedCodeRowToVarFunctional hfun)

theorem fullRowTvs_not_canonicalMatchingCodeRowToVarFunctional {h : Nat} (hh : 2 <= h) :
    ¬ CanonicalMatchingCodeRowToVarFunctional (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
  intro hcan
  exact fullRowTvs_not_realizedCodeRowVarUnique (h := h) hh
    (realizedCodeRowVarUnique_of_canonicalMatchingCodeRowToVarFunctional hcan)

/-! ## Per-term no-go witness -/

/-- Two singleton terms in the same row but different columns. -/
def crossTermRowTvs_h2 : List (List (Fin 2 × Fin 2 × Bool)) :=
  [[((0 : Fin 2), (0 : Fin 2), true)], [((0 : Fin 2), (1 : Fin 2), true)]]

noncomputable def crossTermRowCode_h2_t2 : BadPathCode 2 crossTermRowTvs_h2 2 := by
  intro k
  by_cases _hk : k.1 = 0
  · exact (⟨phpVar 2 2 (0 : Fin 2) (0 : Fin 2), by decide⟩, false)
  · exact (⟨phpVar 2 2 (0 : Fin 2) (1 : Fin 2), by decide⟩, true)

def crossTermRowP_row0Free_h2_s1 : Finset (Fin 2) × Equiv.Perm (Fin 2) :=
  ({1}, Equiv.refl (Fin 2))

theorem crossTermRowTvs_h2_termRowVarUnique :
    PHPDNFTermRowVarUnique crossTermRowTvs_h2 := by
  intro tv htv e₁ he₁ e₂ he₂ hrow
  simp [crossTermRowTvs_h2] at htv
  rcases htv with rfl | htv
  · simp at he₁ he₂
    subst e₁; subst e₂
    rfl
  · rcases htv with rfl | hfalse
    · simp at he₁ he₂
      subst e₁; subst e₂
      rfl

theorem crossTermRowP_row0Free_h2_s1_mem :
    crossTermRowP_row0Free_h2_s1 ∈ fullMatchingSpace 2 1 := by
  unfold fullMatchingSpace crossTermRowP_row0Free_h2_s1
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · unfold subsetSpace
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by decide⟩
  · unfold permSpace
    exact Finset.mem_univ _

theorem crossTermRow_dnfRestrict_row0Free :
    dnfRestrict (fullRestrictionOf crossTermRowP_row0Free_h2_s1)
        (phpDNFAsDNF 2 crossTermRowTvs_h2) =
      [[phpLit 2 ((0 : Fin 2), (0 : Fin 2), true)],
       [phpLit 2 ((0 : Fin 2), (1 : Fin 2), true)]] := by
  decide

theorem crossTermRowP_row0Free_h2_t2_bad :
    canonicalDepthBad 2 crossTermRowTvs_h2 2 crossTermRowP_row0Free_h2_s1 := by
  show 2 <= dtDepth (canonicalRestrictedDNFTree 2 crossTermRowTvs_h2
    crossTermRowP_row0Free_h2_s1)
  unfold canonicalRestrictedDNFTree
  rw [crossTermRow_dnfRestrict_row0Free, termCanonicalDT_cons_cons, dtDepth_node]
  simp [queryTerm_cons, queryTerm_nil, termCanonicalDT_cons_cons, dtDepth_node,
    termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]

theorem crossTermRowP_row0Free_h2_t2_encoding :
    (canonicalDepthBadEncoding 2 crossTermRowTvs_h2 2
      crossTermRowP_row0Free_h2_s1).2 = some crossTermRowCode_h2_t2 := by
  unfold canonicalDepthBadEncoding
  rw [dif_pos crossTermRowP_row0Free_h2_t2_bad]
  change some (canonicalDepthBadCode crossTermRowTvs_h2 2
      crossTermRowP_row0Free_h2_s1 crossTermRowP_row0Free_h2_t2_bad) =
    some crossTermRowCode_h2_t2
  congr
  funext k
  by_cases hk : k.1 = 0
  · have hk' : k = (0 : Fin 2) := Fin.ext hk
    subst hk'
    simp [canonicalDepthBadCode, crossTermRowCode_h2_t2,
      canonicalRestrictedDNFTree, crossTermRow_dnfRestrict_row0Free,
      termCanonicalDT_cons_cons, queryTerm_cons, queryTerm_nil, deepestPath,
      dtDepth_node, termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]
  · have hk' : k = (1 : Fin 2) := Fin.ext (by omega)
    subst hk'
    simp [canonicalDepthBadCode, crossTermRowCode_h2_t2,
      canonicalRestrictedDNFTree, crossTermRow_dnfRestrict_row0Free,
      termCanonicalDT_cons_cons, queryTerm_cons, queryTerm_nil, deepestPath,
      dtDepth_node, termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]

theorem crossTermRowCode_h2_t2_mem_realized :
    crossTermRowCode_h2_t2 ∈
      realizedBadPathCodes (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 := by
  rw [mem_realizedBadPathCodes]
  exact ⟨crossTermRowP_row0Free_h2_s1,
    Finset.mem_filter.mpr ⟨crossTermRowP_row0Free_h2_s1_mem,
      crossTermRowP_row0Free_h2_t2_bad,
      crossTermRowP_row0Free_h2_t2_encoding⟩⟩

theorem crossTermRowCode_h2_t2_rowCollision :
    CodeRowCollision crossTermRowCode_h2_t2 := by
  let c := crossTermRowCode_h2_t2
  have hvar0 : phpVar 2 2 (codeStageRow c 0) (codeStageEntry c 0).2.1 =
      phpVar 2 2 (0 : Fin 2) (0 : Fin 2) := by
    rw [codeStageEntry_var_eq c 0]
    simp [c, crossTermRowCode_h2_t2]
  have hvar1 : phpVar 2 2 (codeStageRow c 1) (codeStageEntry c 1).2.1 =
      phpVar 2 2 (0 : Fin 2) (1 : Fin 2) := by
    rw [codeStageEntry_var_eq c 1]
    simp [c, crossTermRowCode_h2_t2]
  have hrow0 : codeStageRow c 0 = (0 : Fin 2) := (phpVar_inj hvar0).1
  have hrow1 : codeStageRow c 1 = (0 : Fin 2) := (phpVar_inj hvar1).1
  have hcol0 : (codeStageEntry c 0).2.1 = (0 : Fin 2) := (phpVar_inj hvar0).2
  have hcol1 : (codeStageEntry c 1).2.1 = (1 : Fin 2) := (phpVar_inj hvar1).2
  refine ⟨0, 1, ?_, ?_⟩
  · rw [hrow0, hrow1]
  · intro hcol
    have : (0 : Fin 2) = (1 : Fin 2) := by
      rw [← hcol0, hcol, hcol1]
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) this

theorem crossTermRowTvs_h2_not_realizedCodeRowVarUnique :
    ¬ RealizedCodeRowVarUnique (h := 2) (s := 1) (t := 2) crossTermRowTvs_h2 := by
  intro huniq
  have hcu := huniq crossTermRowCode_h2_t2 crossTermRowCode_h2_t2_mem_realized
  exact (codeRowCollision_iff_not_codeRowVarUnique crossTermRowCode_h2_t2).mp
    crossTermRowCode_h2_t2_rowCollision hcu

end PHPFullMatchingGateANaturalInvariant
end PvNP
