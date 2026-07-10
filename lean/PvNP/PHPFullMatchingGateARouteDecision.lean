import PvNP.PHPFullMatchingGateACanonicalRowDiscipline

/-!
# Gate-A route-decision local discipline

Finite square full-matching realized-code/list-support bookkeeping only.  This
module packages the S2135 canonical row-discipline route against the S2134
natural local row discipline, and records the bounded `h = 2, s = 1, t = 2`
obstructions separating local per-term simplicity/row-uniqueness from global
row-to-variable compatibility.

No PHP switching lemma, Frege/PHP lower bound, rectangular `p > h` result,
NP/circuit lower bound, arbitrary AC0 result, or P-vs-NP claim is stated or
proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateARouteDecision

open PHPFullMatchingCanonicalDT
open PHPFullMatchingGateANaturalInvariant
open PHPFullMatchingGateACanonicalRowDiscipline
open SwitchingEncodeConstruct

/-! ## Route-decision predicates -/

/-- Natural local Gate-A row discipline: the realized PHP DNF is syntactically
simple and every individual PHP term is row-variable unique. -/
def PHPDNFNaturalLocalRowDiscipline {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  SimpleDNF (phpDNFAsDNF h tvs) ∧ PHPDNFTermRowVarUnique tvs

/-- The S2135 term-pair compatibility route is exactly whole-DNF row capacity
one, phrased either over pairs of source terms or over the joined source list. -/
theorem termPairRowVarCompatible_iff_rowVarCapacityOne {h : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} :
    PHPDNFTermPairRowVarCompatible tvs ↔ PHPDNFRowVarCapacityOne tvs := by
  constructor
  · exact rowVarCapacityOne_of_termPairRowVarCompatible
  · intro hcap tv₁ htv₁ tv₂ htv₂ e₁ he₁ e₂ he₂ hrow
    exact hcap e₁ (by rw [List.mem_join]; exact ⟨tv₁, htv₁, he₁⟩)
      e₂ (by rw [List.mem_join]; exact ⟨tv₂, htv₂, he₂⟩) hrow

/-! ## The bounded `h = 2` local witness -/

theorem crossTermRowTvs_h2_simple :
    SimpleDNF (phpDNFAsDNF 2 crossTermRowTvs_h2) := by
  simp [SimpleDNF, SimpleTerm, phpDNFAsDNF, phpTermAsTerm, phpLit,
    crossTermRowTvs_h2]

theorem crossTermRowTvs_h2_naturalLocalRowDiscipline :
    PHPDNFNaturalLocalRowDiscipline crossTermRowTvs_h2 :=
  ⟨crossTermRowTvs_h2_simple, crossTermRowTvs_h2_termRowVarUnique⟩

/-! ## Natural-local route obstructions -/

theorem naturalLocalRowDiscipline_not_implies_realizedCodeRowToVarFunctional_h2_s1_t2 :
    ∃ tvs : List (List (Fin 2 × Fin 2 × Bool)),
      PHPDNFNaturalLocalRowDiscipline tvs ∧
        ¬ RealizedCodeRowToVarFunctional (h := 2) (s := 1) (t := 2) tvs :=
  ⟨crossTermRowTvs_h2, crossTermRowTvs_h2_naturalLocalRowDiscipline,
    crossTermRowTvs_h2_not_realizedCodeRowToVarFunctional⟩

theorem naturalLocalRowDiscipline_not_implies_canonicalPathRowCompatible_h2_s1_t2 :
    ∃ tvs : List (List (Fin 2 × Fin 2 × Bool)),
      PHPDNFNaturalLocalRowDiscipline tvs ∧
        ¬ CanonicalPathRowCompatible (h := 2) (s := 1) (t := 2) tvs :=
  ⟨crossTermRowTvs_h2, crossTermRowTvs_h2_naturalLocalRowDiscipline,
    crossTermRowTvs_h2_not_canonicalPathRowCompatible⟩

theorem naturalLocalRowDiscipline_not_implies_termPairRowVarCompatible_h2 :
    ∃ tvs : List (List (Fin 2 × Fin 2 × Bool)),
      PHPDNFNaturalLocalRowDiscipline tvs ∧ ¬ PHPDNFTermPairRowVarCompatible tvs :=
  ⟨crossTermRowTvs_h2, crossTermRowTvs_h2_naturalLocalRowDiscipline,
    crossTermRowTvs_h2_not_termPairRowVarCompatible⟩

theorem naturalLocalRowDiscipline_not_implies_rowVarCapacityOne_h2 :
    ∃ tvs : List (List (Fin 2 × Fin 2 × Bool)),
      PHPDNFNaturalLocalRowDiscipline tvs ∧ ¬ PHPDNFRowVarCapacityOne tvs := by
  refine ⟨crossTermRowTvs_h2, crossTermRowTvs_h2_naturalLocalRowDiscipline, ?_⟩
  intro hcap
  exact crossTermRowTvs_h2_not_termPairRowVarCompatible
    ((termPairRowVarCompatible_iff_rowVarCapacityOne).mpr hcap)

end PHPFullMatchingGateARouteDecision
end PvNP
