import PvNP.PHPFullMatchingStageRows

/-!
# Code-factor bounds for S2125 full-matching bad paths

This module quantifies the all-`BadPathCode` factor left by the S2125
simple-DNF structural replacement.  It proves the exact cardinality of the
current code type, a coarser support-length bound in terms of the PHP DNF input
data, and the resulting finite `EventProbLe` wrappers.

The conclusion is deliberately bounded.  The all-code factor is exposed as
`(2 * support)^t`, while the S2125 row-free decay is only at `q = t / h`.  Thus
any nontrivial bound from this route must make
`(2 * support)^t * (h - s)^(t / h) < h^(t / h)`.  The obstruction lemmas below
record that if `(h - s)^(t / h) >= 1`, nontriviality forces
`(2 * support)^t < h^(t / h)`; otherwise the current all-`BadPathCode` factor
already kills this particular bound.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingCodeFactor

open PHPFullMatchingCanonicalDT
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingStageRows
open PHPFullMatchingProbability
open PHPFullMatchingDistribution
open RestrictedPHPFloor
open SwitchingEncodeConstruct

/-! ## Generic probability monotonicity -/

/-- Increase the numerator of a finite probability upper bound. -/
theorem eventProbLe_mono_num {alpha : Type _} (space : Finset alpha)
    (event : alpha -> Prop) [DecidablePred event] {num num' den : Nat}
    (hnum : num <= num') (hprob : EventProbLe space event num den) :
    EventProbLe space event num' den := by
  unfold EventProbLe at *
  exact Nat.le_trans hprob (Nat.mul_le_mul_right space.card hnum)

/-! ## Bad-path code cardinality -/

/-- The PHP DNF variable support has cardinality at most the total number of PHP
literal occurrences in the input DNF data. -/
theorem phpDNFVarSet_card_le_join_length {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    (phpDNFVarSet h tvs).card <= tvs.join.length := by
  classical
  unfold phpDNFVarSet
  change ((tvs.join.map (fun e => phpVar h h e.1 e.2.1)).toFinset).card <=
    tvs.join.length
  calc
    ((tvs.join.map (fun e => phpVar h h e.1 e.2.1)).toFinset).card <=
        (tvs.join.map (fun e => phpVar h h e.1 e.2.1)).length := by
      exact List.toFinset_card_le _
    _ = tvs.join.length := by
      rw [List.map_join, List.length_join, List.length_join, List.map_map]
      congr 1
      apply List.map_congr_left
      intro tv
      simp

/-- Exact cardinality of the current all-code space: each of the `t` stages
chooses one original PHP DNF variable-support element and one branch direction. -/
theorem badPathCode_card_support {h t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Fintype.card (BadPathCode h tvs t) =
      (2 * (phpDNFVarSet h tvs).card) ^ t := by
  classical
  unfold BadPathCode
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  have hsub : Fintype.card {v : Fin (Nat.succ (h * h)) // v ∈ phpDNFVarSet h tvs} =
      (phpDNFVarSet h tvs).card := by
    exact Fintype.card_ofFinset (phpDNFVarSet h tvs) (by intro x; rfl)
  rw [hsub]
  rw [Nat.mul_comm]

/-- If the PHP DNF variable support has size at most `m`, then the all-code
space has size at most `(2*m)^t`. -/
theorem badPathCode_card_le_of_support_card_le {h t m : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hm : (phpDNFVarSet h tvs).card <= m) :
    Fintype.card (BadPathCode h tvs t) <= (2 * m) ^ t := by
  rw [badPathCode_card_support]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hm) _

/-- Coarser input-data bound: the all-code space is at most `(2*L)^t`, where
`L = tvs.join.length` is the total literal-occurrence count of the PHP DNF data. -/
theorem badPathCode_card_le_join_length {h t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Fintype.card (BadPathCode h tvs t) <= (2 * tvs.join.length) ^ t := by
  exact badPathCode_card_le_of_support_card_le tvs
    (phpDNFVarSet_card_le_join_length tvs)

/-! ## Combined S2125 bounds with the code factor made explicit -/

/-- S2125 simple-DNF geometric bound with an explicit support-size cap `m` for
the current all-`BadPathCode` factor. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_support_bound
    {h s t m : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (hm : (phpDNFVarSet h tvs).card <= m) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
      ((2 * m) ^ t * (h - s) ^ (t / h)) (h ^ (t / h)) := by
  refine eventProbLe_mono_num (fullMatchingSpace h s) (canonicalDepthBad h tvs t) ?_
    (canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h
      (h := h) (s := s) (t := t) tvs hsimple)
  exact Nat.mul_le_mul_right _ (badPathCode_card_le_of_support_card_le tvs hm)

/-- Fully input-data-expanded S2125 simple-DNF geometric bound using only the
literal-occurrence count `tvs.join.length` to bound the current all-code factor. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_join_length
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs)) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
      ((2 * tvs.join.length) ^ t * (h - s) ^ (t / h)) (h ^ (t / h)) := by
  exact canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_support_bound
    (h := h) (s := s) (t := t) (m := tvs.join.length) tvs hsimple
    (phpDNFVarSet_card_le_join_length tvs)

/-- Nontriviality certificate for the support-bound version: the finite
probability bound is below one exactly when the displayed numerator is below the
displayed denominator. -/
theorem canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_support_bound_nontrivial
    {h s t m : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (hm : (phpDNFVarSet h tvs).card <= m)
    (hstrict : (2 * m) ^ t * (h - s) ^ (t / h) < h ^ (t / h)) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t)
        ((2 * m) ^ t * (h - s) ^ (t / h)) (h ^ (t / h)) ∧
      ((2 * m) ^ t * (h - s) ^ (t / h) < h ^ (t / h)) := by
  exact ⟨canonicalDepthBad_eventProbLe_geometric_of_simple_realized_div_h_support_bound
    (h := h) (s := s) (t := t) (m := m) tvs hsimple hm, hstrict⟩

/-! ## Formal obstruction exposed by the all-code factor -/

/-- In any regime where the row-free factor is at least one, a nontrivial bound
from the current all-code estimate forces the code factor alone below the
denominator.  This pinpoints the obstruction caused by counting all
`BadPathCode` values. -/
theorem codeFactor_nontrivial_requires_code_factor_lt_denominator {h s t m : Nat}
    (hfree : 1 <= (h - s) ^ (t / h))
    (hnum : (2 * m) ^ t * (h - s) ^ (t / h) < h ^ (t / h)) :
    (2 * m) ^ t < h ^ (t / h) := by
  calc
    (2 * m) ^ t = (2 * m) ^ t * 1 := by rw [Nat.mul_one]
    _ <= (2 * m) ^ t * (h - s) ^ (t / h) := by
      exact Nat.mul_le_mul_left _ hfree
    _ < h ^ (t / h) := hnum

/-- If the S2125 denominator is already no larger than the all-code factor, then
the current input-data-expanded route cannot produce a below-one bound whenever
the row-free factor is at least one.  A sharper encoding, realized-code count,
exact row growth, or different ambient space is then needed for this route. -/
theorem codeFactor_nontrivial_impossible_of_denominator_le_code_factor {h s t m : Nat}
    (hfree : 1 <= (h - s) ^ (t / h))
    (hbig : h ^ (t / h) <= (2 * m) ^ t) :
    ¬ ((2 * m) ^ t * (h - s) ^ (t / h) < h ^ (t / h)) := by
  intro hnum
  exact not_lt_of_ge hbig
    (codeFactor_nontrivial_requires_code_factor_lt_denominator hfree hnum)

end PHPFullMatchingCodeFactor
end PvNP
