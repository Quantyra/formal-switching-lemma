import PvNP.PHPFullMatchingRealizedCodeParametricObstruction

/-!
# Gate-A row-variable invariant for realized full-matching codes

This module isolates a code-local invariant: every realized canonical bad-path
code is row-variable-unique.  Under that invariant, the row-collision realized
code class is empty.  The S2132 full-row family violates the invariant for every
`h >= 2`.

Finite square full-matching realized-code bookkeeping only.  No PHP switching
lemma, Frege/PHP lower bound, rectangular `p > h` result, NP/circuit lower
bound, arbitrary AC0 result, or P-vs-NP claim is stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateAInvariant

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeSplit
open PHPFullMatchingRealizedCodeParametricObstruction

/-! ## Code-local Gate-A invariant -/

/-- Every realized canonical bad-path code is code-local row-variable-unique.
The parameter `s` is part of the realized-code space but not of the local code
predicate. -/
def RealizedCodeRowVarUnique {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ c : BadPathCode h tvs t,
    c ∈ realizedBadPathCodes (h := h) (s := s) (t := t) tvs ->
      CodeRowVarUnique c

/-- Under the realized-code row-variable invariant, no realized code can be a
row-collision code. -/
theorem rowCollisionRealizedBadPathCodes_eq_empty_of_realizedCodeRowVarUnique
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hinv : RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs) :
    rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hcmem := (mem_rowCollisionRealizedBadPathCodes
    (h := h) (s := s) (t := t) tvs c).mp hc
  have huniq : CodeRowVarUnique c := hinv c hcmem.1
  exact (codeRowCollision_iff_not_codeRowVarUnique c).mp hcmem.2 huniq

/-- Cardinal form of row-collision emptiness under the realized-code
row-variable invariant. -/
theorem rowCollisionRealizedBadPathCodes_card_eq_zero_of_realizedCodeRowVarUnique
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hinv : RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card = 0 := by
  rw [rowCollisionRealizedBadPathCodes_eq_empty_of_realizedCodeRowVarUnique
    (h := h) (s := s) (t := t) tvs hinv]
  rfl

/-- Finite denominator-control corollary: under the realized-code row-variable
invariant, the row-collision numerator is strictly below any positive displayed
denominator. -/
theorem rowCollisionRealizedBadPathCodes_card_lt_denominator_of_realizedCodeRowVarUnique
    {h s t : Nat} (tvs : List (List (Fin h × Fin h × Bool)))
    (hinv : RealizedCodeRowVarUnique (h := h) (s := s) (t := t) tvs)
    (hden : 0 < h ^ (t / h)) :
    (rowCollisionRealizedBadPathCodes (h := h) (s := s) (t := t) tvs).card <
      h ^ (t / h) := by
  rw [rowCollisionRealizedBadPathCodes_card_eq_zero_of_realizedCodeRowVarUnique
    (h := h) (s := s) (t := t) tvs hinv]
  exact hden

/-! ## S2132 full-row family violates the invariant -/

/-- The S2132 full-row SimpleDNF family violates the realized-code
row-variable invariant for every `h >= 2`. -/
theorem fullRowTvs_not_realizedCodeRowVarUnique {h : Nat} (hh : 2 <= h) :
    ¬ RealizedCodeRowVarUnique (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
  intro hinv
  have hzero : (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
      (fullRowTvs h)).card = 0 :=
    rowCollisionRealizedBadPathCodes_card_eq_zero_of_realizedCodeRowVarUnique
      (h := h) (s := h - 1) (t := h) (fullRowTvs h) hinv
  have hge : h <= (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
      (fullRowTvs h)).card :=
    fullRowTvs_rowCollisionRealizedBadPathCodes_card_ge_h (h := h) hh
  omega

end PHPFullMatchingGateAInvariant
end PvNP
