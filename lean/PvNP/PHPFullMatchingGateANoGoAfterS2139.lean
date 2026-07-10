import PvNP.PHPRectMatchingInjectionObstruction

/-!
# Gate A no-go route decision after S2139

This module packages the post-S2139 route decision for the current
realized-code/row-collision denominator target.  It states only bounded
square full-row and rectangular `3 × 2` full-row targets and proves that these
targets are impossible on the named SimpleDNF witness families already
constructed in S2132 and S2139.

No global Gate A impossibility theorem is stated.  No PHP switching lemma,
natural-syntax theorem, arbitrary DNF compression theorem, Frege/PHP lower
bound, NP/circuit lower bound, arbitrary AC0 theorem, or P-vs-NP claim is
stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingGateANoGoAfterS2139

open PHPFullMatchingRealizedCodeParametricObstruction
open PHPFullMatchingCanonicalDT
open PHPFullMatchingRealizedCodeSplit
open PHPRectMatchingInjectionObstruction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement

/-! ## Bounded route targets for the current row-collision route -/

/-- Square full-row SimpleDNF denominator-saving target for the current
realized-code/row-collision route. -/
def SquareSimpleDNFRowCollisionDenominatorSavingTarget : Prop :=
  ∀ h : Nat, 2 ≤ h → SimpleDNF (phpDNFAsDNF h (fullRowTvs h)) →
    (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
      (fullRowTvs h)).card < h ^ (h / h)

/-- Rectangular `3 × 2` full-row SimpleDNF denominator-saving target for the
current realized-code/row-collision route. -/
def RectThreeTwoSimpleDNFRowCollisionDenominatorSavingTarget : Prop :=
  SimpleDNF (rectPHPDNFAsDNF 3 2 rectThreeTwoFullRowTvs) →
    (rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
      rectThreeTwoFullRowTvs).card < 3 ^ (2 / 2)

/-- Square full-row SimpleDNF nontrivial-numerator target for the current
realized-code/row-collision route. -/
def SquareSimpleDNFRowCollisionNontrivialTarget : Prop :=
  ∀ h : Nat, 2 ≤ h → SimpleDNF (phpDNFAsDNF h (fullRowTvs h)) →
    (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
      (fullRowTvs h)).card * (h - (h - 1)) ^ (h / h) < h ^ (h / h)

/-- Rectangular `3 × 2` full-row SimpleDNF nontrivial-numerator target for the
current realized-code/row-collision route. -/
def RectThreeTwoSimpleDNFRowCollisionNontrivialTarget : Prop :=
  SimpleDNF (rectPHPDNFAsDNF 3 2 rectThreeTwoFullRowTvs) →
    (rectRowCollisionRealizedBadPathCodes (p := 3) (h := 2) (s := 2) (t := 2)
      rectThreeTwoFullRowTvs).card * (3 - 2) ^ (2 / 2) < 3 ^ (2 / 2)

/-! ## No-go theorems from the S2132/S2139 obstructions -/

/-- The current square full-row SimpleDNF denominator-saving target is false. -/
theorem not_squareSimpleDNF_rowCollision_denominatorSavingTarget :
    ¬ SquareSimpleDNFRowCollisionDenominatorSavingTarget := by
  intro htarget
  exact fullRowTvs_not_rowCollisionRealizedBadPathCodes_card_lt_denominator
    (h := 2) (by decide) (htarget 2 (by decide) (fullRowTvs_simple 2))

/-- The current rectangular `3 × 2` full-row SimpleDNF denominator-saving target
is false. -/
theorem not_rectThreeTwoSimpleDNF_rowCollision_denominatorSavingTarget :
    ¬ RectThreeTwoSimpleDNFRowCollisionDenominatorSavingTarget := by
  intro htarget
  exact rectThreeTwo_not_rowCollisionRealizedBadPathCodes_card_lt_denominator
    (htarget (by simpa [rectThreeTwoFullRowTvs] using rectFullRowTvs_simple 3 2))

/-- The current square full-row SimpleDNF nontrivial-numerator target is false. -/
theorem not_squareSimpleDNF_rowCollision_nontrivialTarget :
    ¬ SquareSimpleDNFRowCollisionNontrivialTarget := by
  intro htarget
  exact fullRowTvs_rowCollision_route_nontrivial_impossible
    (h := 2) (by decide) (htarget 2 (by decide) (fullRowTvs_simple 2))

/-- The current rectangular `3 × 2` full-row SimpleDNF nontrivial-numerator target
is false. -/
theorem not_rectThreeTwoSimpleDNF_rowCollision_nontrivialTarget :
    ¬ RectThreeTwoSimpleDNFRowCollisionNontrivialTarget := by
  intro htarget
  exact rectThreeTwo_rectangular_route_nontrivial_impossible
    (htarget (by simpa [rectThreeTwoFullRowTvs] using rectFullRowTvs_simple 3 2))

/-- Combined route-decision no-go packet: the current square and rectangular
denominator-saving and nontrivial-numerator targets all fail.  This is only a
no-go packet for the named full-row witness targets, not a global Gate A
impossibility theorem. -/
theorem currentSimpleDNF_rowCollision_route_no_go :
    ¬ SquareSimpleDNFRowCollisionDenominatorSavingTarget ∧
      ¬ RectThreeTwoSimpleDNFRowCollisionDenominatorSavingTarget ∧
      ¬ SquareSimpleDNFRowCollisionNontrivialTarget ∧
      ¬ RectThreeTwoSimpleDNFRowCollisionNontrivialTarget := by
  exact ⟨not_squareSimpleDNF_rowCollision_denominatorSavingTarget,
    not_rectThreeTwoSimpleDNF_rowCollision_denominatorSavingTarget,
    not_squareSimpleDNF_rowCollision_nontrivialTarget,
    not_rectThreeTwoSimpleDNF_rowCollision_nontrivialTarget⟩

end PHPFullMatchingGateANoGoAfterS2139
end PvNP
