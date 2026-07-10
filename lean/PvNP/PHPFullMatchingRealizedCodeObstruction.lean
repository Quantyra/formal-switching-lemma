import PvNP.PHPFullMatchingRealizedCodeCount

/-!
# Realized-code count obstruction

This module records a concrete finite obstruction for the S2127 realized-code
replacement route.  Even for a simple PHP DNF over the square full-matching
space, the number of realized canonical bad-path codes can already meet the
displayed denominator `h^(t/h)`.

The scope remains finite counting over `fullMatchingSpace h s`.  No PHP
switching lemma, Frege/PHP lower bound, NP/circuit lower bound, arbitrary AC0
statement, rectangular `p > h` result, or P-vs-NP claim is stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingRealizedCodeObstruction

open PHPFullMatchingCanonicalDT
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingStageRows
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingDistribution
open PHPMatchingDistribution
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open RestrictedPHPFloor
open SwitchingEncodeConstruct

/-! ## A two-row, two-column SimpleDNF witness -/

/-- Two width-2 row terms over the `2 x 2` PHP square. -/
def twoRowsTwoColsTvs_h2 : List (List (Fin 2 × Fin 2 × Bool)) :=
  [[(0, 0, true), (0, 1, true)], [(1, 0, true), (1, 1, true)]]

/-- The obstruction witness is a syntactically simple DNF: each term has no
repeated variable. -/
theorem twoRowsTwoColsTvs_h2_simple :
    SimpleDNF (phpDNFAsDNF 2 twoRowsTwoColsTvs_h2) := by
  simp [SimpleDNF, SimpleTerm, phpDNFAsDNF, phpTermAsTerm, phpLit,
    twoRowsTwoColsTvs_h2]
  decide

/-- The realized path code obtained when row `0` is left free: both queried
variables are taken along the true branch of the row-0 term. -/
noncomputable def twoRowsTwoColsCode_row0_h2_t2 :
    BadPathCode 2 twoRowsTwoColsTvs_h2 2 := by
  intro k
  by_cases _hstage : k.1 = 0
  · exact (⟨phpVar 2 2 (0 : Fin 2) (0 : Fin 2), by decide⟩, true)
  · exact (⟨phpVar 2 2 (0 : Fin 2) (1 : Fin 2), by decide⟩, true)

/-- The realized path code obtained when row `1` is left free: both queried
variables are taken along the true branch of the row-1 term. -/
noncomputable def twoRowsTwoColsCode_row1_h2_t2 :
    BadPathCode 2 twoRowsTwoColsTvs_h2 2 := by
  intro k
  by_cases _hstage : k.1 = 0
  · exact (⟨phpVar 2 2 (1 : Fin 2) (0 : Fin 2), by decide⟩, true)
  · exact (⟨phpVar 2 2 (1 : Fin 2) (1 : Fin 2), by decide⟩, true)

/-- Matching point leaving row `0` free and fixing row `1` along the identity. -/
def twoRowsTwoColsP_row0Free_h2_s1 : Finset (Fin 2) × Equiv.Perm (Fin 2) :=
  ({1}, Equiv.refl (Fin 2))

/-- Matching point leaving row `1` free and fixing row `0` along the identity. -/
def twoRowsTwoColsP_row1Free_h2_s1 : Finset (Fin 2) × Equiv.Perm (Fin 2) :=
  ({0}, Equiv.refl (Fin 2))

theorem twoRowsTwoColsP_row0Free_h2_s1_mem :
    twoRowsTwoColsP_row0Free_h2_s1 ∈ fullMatchingSpace 2 1 := by
  unfold fullMatchingSpace twoRowsTwoColsP_row0Free_h2_s1
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · unfold subsetSpace
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by decide⟩
  · unfold permSpace
    exact Finset.mem_univ _

theorem twoRowsTwoColsP_row1Free_h2_s1_mem :
    twoRowsTwoColsP_row1Free_h2_s1 ∈ fullMatchingSpace 2 1 := by
  unfold fullMatchingSpace twoRowsTwoColsP_row1Free_h2_s1
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · unfold subsetSpace
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by decide⟩
  · unfold permSpace
    exact Finset.mem_univ _

theorem twoRowsTwoCols_dnfRestrict_row0Free :
    dnfRestrict (fullRestrictionOf twoRowsTwoColsP_row0Free_h2_s1)
        (phpDNFAsDNF 2 twoRowsTwoColsTvs_h2) =
      [[phpLit 2 ((0 : Fin 2), (0 : Fin 2), true),
        phpLit 2 ((0 : Fin 2), (1 : Fin 2), true)]] := by
  decide

theorem twoRowsTwoCols_dnfRestrict_row1Free :
    dnfRestrict (fullRestrictionOf twoRowsTwoColsP_row1Free_h2_s1)
        (phpDNFAsDNF 2 twoRowsTwoColsTvs_h2) =
      [[phpLit 2 ((1 : Fin 2), (0 : Fin 2), true),
        phpLit 2 ((1 : Fin 2), (1 : Fin 2), true)]] := by
  decide

theorem twoRowsTwoColsP_row0Free_h2_t2_bad :
    canonicalDepthBad 2 twoRowsTwoColsTvs_h2 2 twoRowsTwoColsP_row0Free_h2_s1 := by
  show 2 <= dtDepth (canonicalRestrictedDNFTree 2 twoRowsTwoColsTvs_h2
    twoRowsTwoColsP_row0Free_h2_s1)
  unfold canonicalRestrictedDNFTree
  rw [twoRowsTwoCols_dnfRestrict_row0Free, termCanonicalDT_cons_cons, dtDepth_node]
  simp [queryTerm_cons, queryTerm_nil, termCanonicalDT_cons_cons, dtDepth_node,
    termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]

theorem twoRowsTwoColsP_row1Free_h2_t2_bad :
    canonicalDepthBad 2 twoRowsTwoColsTvs_h2 2 twoRowsTwoColsP_row1Free_h2_s1 := by
  show 2 <= dtDepth (canonicalRestrictedDNFTree 2 twoRowsTwoColsTvs_h2
    twoRowsTwoColsP_row1Free_h2_s1)
  unfold canonicalRestrictedDNFTree
  rw [twoRowsTwoCols_dnfRestrict_row1Free, termCanonicalDT_cons_cons, dtDepth_node]
  simp [queryTerm_cons, queryTerm_nil, termCanonicalDT_cons_cons, dtDepth_node,
    termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]

theorem twoRowsTwoColsP_row0Free_h2_t2_encoding :
    (canonicalDepthBadEncoding 2 twoRowsTwoColsTvs_h2 2
      twoRowsTwoColsP_row0Free_h2_s1).2 =
      some twoRowsTwoColsCode_row0_h2_t2 := by
  unfold canonicalDepthBadEncoding
  rw [dif_pos twoRowsTwoColsP_row0Free_h2_t2_bad]
  change some (canonicalDepthBadCode twoRowsTwoColsTvs_h2 2
      twoRowsTwoColsP_row0Free_h2_s1 twoRowsTwoColsP_row0Free_h2_t2_bad) =
    some twoRowsTwoColsCode_row0_h2_t2
  congr
  funext k
  by_cases hk : k.1 = 0
  · have hk' : k = (0 : Fin 2) := Fin.ext hk
    subst hk'
    simp [canonicalDepthBadCode, twoRowsTwoColsCode_row0_h2_t2,
      canonicalRestrictedDNFTree, twoRowsTwoCols_dnfRestrict_row0Free,
      termCanonicalDT_cons_cons, queryTerm_cons, queryTerm_nil, deepestPath,
      dtDepth_node, termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]
  · have hk' : k = (1 : Fin 2) := Fin.ext (by omega)
    subst hk'
    simp [canonicalDepthBadCode, twoRowsTwoColsCode_row0_h2_t2,
      canonicalRestrictedDNFTree, twoRowsTwoCols_dnfRestrict_row0Free,
      termCanonicalDT_cons_cons, queryTerm_cons, queryTerm_nil, deepestPath,
      dtDepth_node, termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]

theorem twoRowsTwoColsP_row1Free_h2_t2_encoding :
    (canonicalDepthBadEncoding 2 twoRowsTwoColsTvs_h2 2
      twoRowsTwoColsP_row1Free_h2_s1).2 =
      some twoRowsTwoColsCode_row1_h2_t2 := by
  unfold canonicalDepthBadEncoding
  rw [dif_pos twoRowsTwoColsP_row1Free_h2_t2_bad]
  change some (canonicalDepthBadCode twoRowsTwoColsTvs_h2 2
      twoRowsTwoColsP_row1Free_h2_s1 twoRowsTwoColsP_row1Free_h2_t2_bad) =
    some twoRowsTwoColsCode_row1_h2_t2
  congr
  funext k
  by_cases hk : k.1 = 0
  · have hk' : k = (0 : Fin 2) := Fin.ext hk
    subst hk'
    simp [canonicalDepthBadCode, twoRowsTwoColsCode_row1_h2_t2,
      canonicalRestrictedDNFTree, twoRowsTwoCols_dnfRestrict_row1Free,
      termCanonicalDT_cons_cons, queryTerm_cons, queryTerm_nil, deepestPath,
      dtDepth_node, termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]
  · have hk' : k = (1 : Fin 2) := Fin.ext (by omega)
    subst hk'
    simp [canonicalDepthBadCode, twoRowsTwoColsCode_row1_h2_t2,
      canonicalRestrictedDNFTree, twoRowsTwoCols_dnfRestrict_row1Free,
      termCanonicalDT_cons_cons, queryTerm_cons, queryTerm_nil, deepestPath,
      dtDepth_node, termCanonicalDT, assignVar, assignTerm, phpLit, phpVar]

/-- The row-0 code is realized by selecting the other row in the matching
restriction. -/
theorem twoRowsTwoColsCode_row0_h2_t2_mem_realized :
    twoRowsTwoColsCode_row0_h2_t2 ∈
      realizedBadPathCodes (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2 := by
  rw [mem_realizedBadPathCodes]
  exact ⟨twoRowsTwoColsP_row0Free_h2_s1,
    Finset.mem_filter.mpr ⟨twoRowsTwoColsP_row0Free_h2_s1_mem,
      twoRowsTwoColsP_row0Free_h2_t2_bad,
      twoRowsTwoColsP_row0Free_h2_t2_encoding⟩⟩

/-- The row-1 code is realized by selecting the other row in the matching
restriction. -/
theorem twoRowsTwoColsCode_row1_h2_t2_mem_realized :
    twoRowsTwoColsCode_row1_h2_t2 ∈
      realizedBadPathCodes (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2 := by
  rw [mem_realizedBadPathCodes]
  exact ⟨twoRowsTwoColsP_row1Free_h2_s1,
    Finset.mem_filter.mpr ⟨twoRowsTwoColsP_row1Free_h2_s1_mem,
      twoRowsTwoColsP_row1Free_h2_t2_bad,
      twoRowsTwoColsP_row1Free_h2_t2_encoding⟩⟩

/-- The two displayed realized codes are distinct. -/
theorem twoRowsTwoColsCode_row0_ne_row1_h2_t2 :
    twoRowsTwoColsCode_row0_h2_t2 ≠ twoRowsTwoColsCode_row1_h2_t2 := by
  intro hcode
  have hstage := congrFun hcode (0 : Fin 2)
  have hvar := congrArg (fun x => ((x.1 : {v // v ∈ phpDNFVarSet 2 twoRowsTwoColsTvs_h2}) :
      Fin (Nat.succ (2 * 2)))) hstage
  simp [twoRowsTwoColsCode_row0_h2_t2, twoRowsTwoColsCode_row1_h2_t2] at hvar
  have hneq : phpVar 2 2 (0 : Fin 2) (0 : Fin 2) ≠
      phpVar 2 2 (1 : Fin 2) (0 : Fin 2) := by
    decide
  exact hneq hvar

/-- At least two canonical bad-path codes are realized in the two-row witness. -/
theorem twoRowsTwoCols_realizedBadPathCodes_card_ge_two :
    2 <=
      (realizedBadPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card := by
  classical
  let R := realizedBadPathCodes (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2
  let A : Finset (BadPathCode 2 twoRowsTwoColsTvs_h2 2) :=
    {twoRowsTwoColsCode_row0_h2_t2, twoRowsTwoColsCode_row1_h2_t2}
  have hsubset : A ⊆ R := by
    intro c hc
    simp [A] at hc
    rcases hc with hc | hc
    · simpa [R, hc] using twoRowsTwoColsCode_row0_h2_t2_mem_realized
    · simpa [R, hc] using twoRowsTwoColsCode_row1_h2_t2_mem_realized
  have hcard : A.card = 2 := by
    simp [A, twoRowsTwoColsCode_row0_ne_row1_h2_t2]
  calc
    2 = A.card := hcard.symm
    _ <= R.card := Finset.card_le_card hsubset

/-- The S2127 denominator is already no larger than the realized-code count in
this simple-DNF witness: `2^(2/2) <= card(realizedBadPathCodes)`. -/
theorem twoRowsTwoCols_denominator_le_realizedBadPathCodes_card :
    2 ^ (2 / 2) <=
      (realizedBadPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card := by
  simpa using twoRowsTwoCols_realizedBadPathCodes_card_ge_two

/-- Therefore no SimpleDNF-only theorem can force the realized-code count below
the displayed S2127 denominator. -/
theorem twoRowsTwoCols_not_realizedBadPathCodes_card_lt_denominator :
    ¬ (realizedBadPathCodes (h := 2) (s := 1) (t := 2)
        twoRowsTwoColsTvs_h2).card < 2 ^ (2 / 2) := by
  exact not_lt_of_ge twoRowsTwoCols_denominator_le_realizedBadPathCodes_card

/-- Directly applying the S2127 obstruction: for this simple-DNF witness, the
realized-code numerator is not strictly below the displayed denominator. -/
theorem twoRowsTwoCols_realizedCode_route_nontrivial_impossible :
    ¬ ((realizedBadPathCodes (h := 2) (s := 1) (t := 2)
          twoRowsTwoColsTvs_h2).card *
        (2 - 1) ^ (2 / 2) < 2 ^ (2 / 2)) := by
  exact realizedCode_nontrivial_impossible_of_denominator_le_realized_card
    (h := 2) (s := 1) (t := 2) twoRowsTwoColsTvs_h2
    (by decide)
    twoRowsTwoCols_denominator_le_realizedBadPathCodes_card

end PHPFullMatchingRealizedCodeObstruction
end PvNP
