import PvNP.SwitchingEncodeConstruct

/-!
# Canonical-vs-term-canonical switching bridge

This module isolates the depth-domination bridge needed to transfer the already
stated term-canonical switching lemma back to the original `canonicalDT` bad set.

The full structural domination

`dtDepth (canonicalDT D) ≤ dtDepth (termCanonicalDT D)`

is intentionally left as the named residual `CanonicalTermDepthDomination`; it is
not assumed globally and neither `SwitchingLemma` nor `SwitchingLemmaTerm` is
inhabited here.  What is proved is the exact conditional bridge: any future proof
of the domination residual gives the bad-set inclusion and hence converts a term
switching lemma into the original statement.
-/

namespace PvNP
namespace SwitchingCanonicalBridge

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct

/-! ## The residual domination target -/

/-- Residual depth-domination target for the canonical and term-canonical trees.

This is a `Prop` only; it is not an axiom and is not inhabited in this module. -/
def CanonicalTermDepthDomination (n : Nat) : Prop :=
  ∀ (D : DNF n), dtDepth (canonicalDT D) ≤ dtDepth (termCanonicalDT D)

/-! ## Small structural facts that are fully proved -/

/-- The domination target is closed for the empty DNF. -/
theorem dtDepth_canonicalDT_le_termCanonicalDT_nil {n : Nat} :
    dtDepth (canonicalDT ([] : DNF n)) ≤
      dtDepth (termCanonicalDT ([] : DNF n)) := by
  simp [canonicalDT, termCanonicalDT]

/-- The domination target is closed when the first term is empty. -/
theorem dtDepth_canonicalDT_le_termCanonicalDT_cons_nil {n : Nat}
    (D : DNF n) :
    dtDepth (canonicalDT ([] :: D)) ≤ dtDepth (termCanonicalDT ([] :: D)) := by
  simp [canonicalDT, termCanonicalDT]

/-- Exact depth unfolding for the original canonical tree at a nonempty first
term. -/
theorem dtDepth_canonicalDT_cons_cons {n : Nat}
    (l : Literal n) (t : Term n) (D : DNF n) :
    dtDepth (canonicalDT ((l :: t) :: D)) =
      1 + max
        (dtDepth (canonicalDT (assignVar l.var false ((l :: t) :: D))))
        (dtDepth (canonicalDT (assignVar l.var true ((l :: t) :: D)))) := by
  rw [canonicalDT, dtDepth_node]

/-- Exact depth unfolding for the term-canonical tree at a nonempty first term. -/
theorem dtDepth_termCanonicalDT_cons_cons {n : Nat}
    (l : Literal n) (t : Term n) (D : DNF n) :
    dtDepth (termCanonicalDT ((l :: t) :: D)) =
      1 + max
        (dtDepth (queryTerm t (assignVar l.var false ((l :: t) :: D))))
        (dtDepth (queryTerm t (assignVar l.var true ((l :: t) :: D)))) := by
  rw [termCanonicalDT_cons_cons, dtDepth_node]

/-! ## Conditional bad-set and switching-statement bridge -/

open Classical in
/-- Under depth domination, every original-canonical bad restriction is also
term-canonical bad. -/
theorem badSet_subset_badSetTerm_of_depthDomination {n : Nat}
    (hdom : CanonicalTermDepthDomination n) (D : DNF n) (s ℓ : Nat) :
    badSet D s ℓ ⊆ badSetTerm D s ℓ := by
  intro ρ hρ
  have hbad := (mem_badSet ρ).mp hρ
  exact (mem_badSetTerm ρ).mpr
    ⟨hbad.1, Nat.le_trans hbad.2 (hdom (dnfRestrict ρ D))⟩

/-- Conditional conversion from the term-canonical switching lemma to the original
canonical statement.  This does not inhabit either switching lemma by itself; it
requires both a term-canonical proof and the residual depth-domination proof. -/
theorem switchingLemma_of_switchingLemmaTerm_of_depthDomination {n : Nat}
    (hdom : CanonicalTermDepthDomination n)
    (hterm : SwitchingLemmaTerm n) : SwitchingLemma n := by
  intro D w s ℓ hw
  exact Nat.le_trans
    (Finset.card_le_card (badSet_subset_badSetTerm_of_depthDomination hdom D s ℓ))
    (hterm D w s ℓ hw)

end SwitchingCanonicalBridge
end PvNP
