import PvNP.FormulaSyntacticDNFNormalization
import PvNP.SwitchingClose2

/-!
# S2232-A1: honest normalization bridge for the term switching statement

This module records the first normalization-facing bridge from arbitrary DNFs to
the already-proved simple-DNF term switching lemma.  The structural facts below
are fully proved: normalization preserves restricted DNF semantics, always
produces simple restricted DNFs, and does not increase restricted width.

The remaining card/depth monotonicity needed to transfer `badSetTerm D s ℓ` to
`badSetTerm (normalizeDNF D) s ℓ` is isolated as a named `Prop`.  This file does
not assert that residual and therefore does **not** prove the general term
switching lemma outright.

Boundary: term-form switching bookkeeping only.  No `SwitchingLemma`, AC0,
Frege/PHP, lower-bound, P-vs-NP, or release claim.
-/

namespace PvNP
namespace SwitchingNormalize

open CNFModel
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingEncodeConstruct
open FormulaSyntacticDNFNormalization

/-! ## Structural normalization facts that survive restriction -/

/-- Normalizing a restricted DNF preserves its pointwise Boolean semantics. -/
theorem dnfEval_normalizeDNF_dnfRestrict {n : Nat} (a : Assignment n)
    (ρ : Restriction n) (D : DNF n) :
    dnfEval a (normalizeDNF (dnfRestrict ρ D)) = dnfEval a (dnfRestrict ρ D) :=
  dnfEval_normalizeDNF a (dnfRestrict ρ D)

/-- Every normalized restricted DNF is simple, with no hypothesis on the source. -/
theorem simpleDNF_normalizeDNF_dnfRestrict {n : Nat}
    (ρ : Restriction n) (D : DNF n) :
    SimpleDNF (normalizeDNF (dnfRestrict ρ D)) :=
  simpleDNF_normalizeDNF (dnfRestrict ρ D)

/-- Restricting and then normalizing never increases width relative to the
original DNF. -/
theorem widthDNF_normalizeDNF_dnfRestrict_le {n : Nat}
    (ρ : Restriction n) (D : DNF n) :
    widthDNF (normalizeDNF (dnfRestrict ρ D)) ≤ widthDNF D :=
  Nat.le_trans (widthDNF_normalizeDNF_le (dnfRestrict ρ D))
    (widthDNF_dnfRestrict_le ρ D)

/-! ## Honest residual for the missing card/depth bridge -/

/-- The exact missing bridge for transferring the arbitrary-DNF bad set to the
normalized simple-DNF bad set.

This is intentionally a `Prop`, not an axiom and not an inhabited theorem.  The
naive monotonicity can fail if normalization shortens the term-canonical decision
tree depth; this residual names precisely the counting fact needed before one may
turn the simple-DNF theorem into the general term theorem. -/
def NormalizeBadSetCardBridge (n : Nat) : Prop :=
  ∀ (D : DNF n) (s ℓ : Nat),
    (badSetTerm D s ℓ).card ≤ (badSetTerm (normalizeDNF D) s ℓ).card

/-- If the missing normalization bad-set cardinality bridge is supplied, then the
proved simple-DNF term switching lemma yields the arbitrary-DNF term statement. -/
theorem switchingLemmaTerm_of_simple_with_normalizeBridge {n : Nat}
    (h : SwitchingLemmaTermSimple n) (hbridge : NormalizeBadSetCardBridge n) :
    SwitchingLemmaTerm n := by
  intro D w s ℓ hw
  have hbad : (badSetTerm D s ℓ).card ≤
      (badSetTerm (normalizeDNF D) s ℓ).card :=
    hbridge D s ℓ
  have hsimple : SimpleDNF (normalizeDNF D) :=
    simpleDNF_normalizeDNF D
  have hwidth : widthDNF (normalizeDNF D) ≤ w :=
    Nat.le_trans (widthDNF_normalizeDNF_le D) hw
  exact Nat.le_trans hbad (h (normalizeDNF D) w s ℓ hsimple hwidth)

/-- Closed reduction from the named residual to the general term switching
statement, using the already-proved simple-DNF capstone.  This theorem is
conditional on `NormalizeBadSetCardBridge`; it does not inhabit that bridge. -/
theorem switchingLemmaTerm_proved_of_normalizeBridge {n : Nat}
    (hbridge : NormalizeBadSetCardBridge n) : SwitchingLemmaTerm n :=
  switchingLemmaTerm_of_simple_with_normalizeBridge
    (SwitchingClose2.switchingLemmaTermSimple_proved (n := n)) hbridge

end SwitchingNormalize
end PvNP
