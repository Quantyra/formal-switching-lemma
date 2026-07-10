import PvNP.PHPFullMatchingGateARealizedCodePathSplit

/-!
# Gate-A bad realized-code conflict signatures

Finite square full-matching/list-support bookkeeping only.  This module extracts a
canonical same-row/different-column conflict signature from every S2137 bad
realized code, identifies the S2137 bad class with the S2131 row-collision class,
and transfers the concrete two-by-two denominator obstruction to the bad side.

No natural-syntax theorem, general compression/charging theorem, PHP switching
lemma, rectangular `p > h` result, Frege/PHP lower bound, NP/circuit lower bound,
arbitrary AC0 result, or P-vs-NP claim is stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateABadConflictSignature

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingGateACanonicalRowDiscipline
open PHPFullMatchingGateARealizedCodePathSplit
open PHPFullMatchingGateANaturalInvariant
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeObstruction
open PHPFullMatchingRealizedCodeSplit
open PHPFullMatchingRowUniqueStrict
open PHPFullMatchingStageRows
open SwitchingEncodeConstruct

/-! ## Conflict signatures -/

/-- A code-local conflict signature is a pair of stages with the same recovered
row and different decoded PHP columns. -/
def CodeRowConflictSignature {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) : Type :=
  { kl : Fin t × Fin t //
    codeStageRow c kl.1 = codeStageRow c kl.2 ∧
      (codeStageEntry c kl.1).2.1 ≠ (codeStageEntry c kl.2).2.1 }

/-- Every S2137 bad realized code carries an S2131 row collision. -/
theorem codeRowCollision_of_badRealizedCode {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {c : BadPathCode h tvs t}
    (hbad : BadRealizedCode (h := h) (s := s) (t := t) tvs c) :
    CodeRowCollision c :=
  (codeRowCollision_iff_not_codeRowVarUnique c).mpr <| by
    intro huniq
    exact hbad.2 (codeRowToVarFunctional_of_codeRowVarUnique huniq)

/-- Choose the canonical conflict-signature representative from a row collision. -/
noncomputable def codeRowConflictSignatureOfCollision {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {c : BadPathCode h tvs t}
    (hcoll : CodeRowCollision c) : CodeRowConflictSignature c := by
  classical
  refine ⟨(Classical.choose hcoll, Classical.choose (Classical.choose_spec hcoll)), ?_⟩
  exact Classical.choose_spec (Classical.choose_spec hcoll)

/-- The canonical conflict signature attached to a bad realized code. -/
noncomputable def badRealizedCodeConflictSignature {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {c : BadPathCode h tvs t}
    (hbad : BadRealizedCode (h := h) (s := s) (t := t) tvs c) :
    CodeRowConflictSignature c :=
  codeRowConflictSignatureOfCollision (codeRowCollision_of_badRealizedCode hbad)

/-- The canonical bad-realized-code signature really names equal recovered rows
with different decoded PHP columns. -/
theorem badRealizedCodeConflictSignature_spec {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {c : BadPathCode h tvs t}
    (hbad : BadRealizedCode (h := h) (s := s) (t := t) tvs c) :
    codeStageRow c (badRealizedCodeConflictSignature hbad).1.1 =
        codeStageRow c (badRealizedCodeConflictSignature hbad).1.2 ∧
      (codeStageEntry c (badRealizedCodeConflictSignature hbad).1.1).2.1 ≠
        (codeStageEntry c (badRealizedCodeConflictSignature hbad).1.2).2.1 :=
  (badRealizedCodeConflictSignature hbad).2

/-! ## Bad realized codes are exactly row-collision realized codes -/

/-- The S2137 bad realized-code class is exactly the S2131 row-collision realized
code class, for every finite square full-matching/list-support instance. -/
theorem badRealizedPathCodes_eq_rowCollisionRealizedBadPathCodes {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    badRealizedPathCodes (h := h) (s := s) (t := t) tvs =
      rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs := by
  classical
  ext c
  constructor
  · intro hc
    have hbad := (mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mp hc
    exact (mem_rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mpr
      ⟨hbad.1, codeRowCollision_of_badRealizedCode hbad⟩
  · intro hc
    have hcoll := (mem_rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mp hc
    exact (mem_badRealizedPathCodes (h := h) (s := s) (t := t) tvs c).mpr
      ⟨hcoll.1, by
        intro hfun
        exact (codeRowCollision_iff_not_codeRowVarUnique c).mp hcoll.2
          (codeRowVarUnique_of_codeRowToVarFunctional hfun)⟩

/-- Cardinality form of the bad equals row-collision realized-code equivalence. -/
theorem badRealizedPathCodes_card_eq_rowCollisionRealizedBadPathCodes_card {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    (badRealizedPathCodes (h := h) (s := s) (t := t) tvs).card =
      (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card :=
  congrArg Finset.card
    (badRealizedPathCodes_eq_rowCollisionRealizedBadPathCodes
      (h := h) (s := s) (t := t) tvs)

/-! ## Two-by-two bad-side denominator obstruction -/

/-- The S2127 denominator is no larger than the S2137 bad realized-code count in
the concrete two-by-two witness. -/
theorem twoRowsTwoCols_denominator_le_badRealizedPathCodes_card :
    2 ^ (2 / 2) <=
      (badRealizedPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card := by
  simpa [badRealizedPathCodes_eq_rowCollisionRealizedBadPathCodes
    (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2] using
    twoRowsTwoCols_denominator_le_rowCollisionRealizedBadPathCodes_card

/-- Therefore no finite-square bad-side theorem can force this concrete bad
realized-code count below the displayed S2127 denominator. -/
theorem twoRowsTwoCols_not_badRealizedPathCodes_card_lt_denominator :
    ¬ (badRealizedPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card < 2 ^ (2 / 2) := by
  exact not_lt_of_ge twoRowsTwoCols_denominator_le_badRealizedPathCodes_card

/-- Direct obstruction form for the S2137 bad-side denominator route in the
concrete two-by-two witness. -/
theorem twoRowsTwoCols_bad_route_nontrivial_impossible :
    ¬ ((badRealizedPathCodes (h := 2) (s := 1) (t := 2)
          twoRowsTwoColsTvs_h2).card *
        (2 - 1) ^ (2 / 2) < 2 ^ (2 / 2)) := by
  have hden := twoRowsTwoCols_denominator_le_badRealizedPathCodes_card
  exact not_lt_of_ge (by simpa using hden)

end PHPFullMatchingGateABadConflictSignature
end PvNP
