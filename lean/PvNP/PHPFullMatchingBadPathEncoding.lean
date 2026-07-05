import PvNP.PHPFullMatchingCanonicalDT
import PvNP.SwitchingCardLemma
import PvNP.SwitchingDeepPath

/-!
# First conservative bad-path encoding over full matching space

This module proves the first bad-path certificate/counting theorem for the
restricted PHP DNF canonical decision tree over the full square matching space.

The result is intentionally conservative.  A bad matching point whose restricted
canonical tree has depth at least `t` carries the first `t` entries of a deepest
path, with every queried variable certified to lie in the original PHP DNF
variable support.  The counting theorem then injects bad matching points into
the full matching space paired with an optional path code.

HONEST SCOPE STATEMENT: this is a first encoding/counting skeleton only.  Since
the encoded object still keeps the original matching point as its first
coordinate, it is not a switching lemma and it gives no geometric
collapse-probability improvement over the matching space.  The remaining
mathematical blocker is to replace this conservative encoding by a compressed
bad-set encoding/counting argument, then prove the corresponding geometric
probability bound.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingBadPathEncoding

open CNFModel
open BoundedDepthDecisionTree
open PHPFullMatchingCanonicalDT
open PHPFullMatchingDistribution
open PHPFullMatchingProbability
open SwitchingCardLemma

/-! ## Bad event and path-code type -/

/-- The depth-`t` bad event for the restricted PHP DNF canonical tree. -/
def canonicalDepthBad (h : Nat)
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) : Prop :=
  t <= dtDepth (canonicalRestrictedDNFTree h tvs P)

instance instDecidableCanonicalDepthBad {h : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} {t : Nat}
    {P : Finset (Fin h) × Equiv.Perm (Fin h)} :
    Decidable (canonicalDepthBad h tvs t P) := by
  unfold canonicalDepthBad
  infer_instance

instance instDecidablePredCanonicalDepthBad {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat) :
    DecidablePred (canonicalDepthBad h tvs t) := by
  intro P
  infer_instance

/-- A bad-path code records `t` query/direction pairs, with every query
certified to be a variable appearing in the original PHP DNF. -/
def BadPathCode (h : Nat)
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat) : Type :=
  Fin t -> {v : Fin (Nat.succ (h * h)) // v ∈ phpDNFVarSet h tvs} × Bool

noncomputable instance instFintypeBadPathCode {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat) :
    Fintype (BadPathCode h tvs t) := by
  classical
  unfold BadPathCode
  infer_instance

noncomputable instance instDecidableEqBadPathCode {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat) :
    DecidableEq (BadPathCode h tvs t) := by
  classical
  infer_instance

/-! ## Deepest-path support containment -/

/-- If every decision node of a tree queries inside `S`, then every variable
on its deepest path is also inside `S`. -/
theorem deepestPath_treeVarsIn {n : Nat} {S : Finset (Fin n)} :
    forall (T : DTree n), TreeVarsIn T S ->
      forall vd, vd ∈ deepestPath T -> vd.1 ∈ S
  | .leaf _, _hT, vd, hvd => by
      simp [deepestPath] at hvd
  | .node v t0 t1, hT, vd, hvd => by
      simp only [TreeVarsIn] at hT
      rcases hT with ⟨hv, ht0, ht1⟩
      unfold deepestPath at hvd
      by_cases hdepth : dtDepth t0 <= dtDepth t1
      · simp [hdepth] at hvd
        rcases hvd with hhead | htail
        · cases hhead
          exact hv
        · exact deepestPath_treeVarsIn t1 ht1 vd htail
      · simp [hdepth] at hvd
        rcases hvd with hhead | htail
        · cases hhead
          exact hv
        · exact deepestPath_treeVarsIn t0 ht0 vd htail

/-! ## Canonical bad-path extraction -/

/-- Extract the first `t` entries of a deepest path from a bad matching point,
with each query certified to belong to the original PHP DNF support. -/
noncomputable def canonicalDepthBadCode {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P) :
    BadPathCode h tvs t := by
  intro i
  let T := canonicalRestrictedDNFTree h tvs P
  have hlen : i.1 < (deepestPath T).length := by
    rw [deepestPath_length]
    exact Nat.lt_of_lt_of_le i.2 hbad
  let vd := (deepestPath T).get ⟨i.1, hlen⟩
  have hvdmem : vd ∈ deepestPath T := by
    exact List.get_mem (deepestPath T) i.1 hlen
  have hv : vd.1 ∈ phpDNFVarSet h tvs := by
    exact deepestPath_treeVarsIn T
      (treeVarsIn_canonicalRestrictedDNFTree P tvs) vd hvdmem
  exact (⟨vd.1, hv⟩, vd.2)

/-- Every bad matching point has a certified bad-path code. -/
theorem canonicalDepthBad_pathCode_exists {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P) :
    Nonempty (BadPathCode h tvs t) :=
  ⟨canonicalDepthBadCode tvs t P hbad⟩

/-! ## Conservative full-matching-space counting -/

/-- Conservative encoder: bad points carry a concrete path code; nonbad points
are assigned `none`.  The first coordinate is deliberately the original
matching point, so the count below is only a skeleton, not a compression. -/
noncomputable def canonicalDepthBadEncoding (h : Nat)
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    (Finset (Fin h) × Equiv.Perm (Fin h)) ×
      Option (BadPathCode h tvs t) :=
  if hbad : canonicalDepthBad h tvs t P then
    (P, some (canonicalDepthBadCode tvs t P hbad))
  else
    (P, none)

theorem canonicalDepthBadEncoding_fst {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    (canonicalDepthBadEncoding h tvs t P).1 = P := by
  unfold canonicalDepthBadEncoding
  by_cases hbad : canonicalDepthBad h tvs t P <;> simp [hbad]

/-- The conservative encoder is injective on any bad subset because it keeps the
original matching point as its first coordinate. -/
theorem canonicalDepthBadEncoding_injective_on {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    Set.InjOn (canonicalDepthBadEncoding h tvs t)
      ↑((fullMatchingSpace h s).filter (canonicalDepthBad h tvs t)) := by
  intro P _hP Q _hQ henc
  calc
    P = (canonicalDepthBadEncoding h tvs t P).1 := by
      exact (canonicalDepthBadEncoding_fst tvs t P).symm
    _ = (canonicalDepthBadEncoding h tvs t Q).1 := by
      exact congrArg Prod.fst henc
    _ = Q := by
      exact canonicalDepthBadEncoding_fst tvs t Q

/-- First conservative bad-path counting theorem over the full matching space.

This bounds the depth-`t` bad event by the full matching space times the optional
path-code type.  It is a finite counting theorem for `canonicalRestrictedDNFTree`
over `fullMatchingSpace`, but it is not yet the geometric switching-lemma
counting step because the encoding retains the original matching point. -/
theorem canonicalDepthBad_count_le_space_mul_optional_pathCode {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      (fullMatchingSpace h s).card *
        Fintype.card (Option (BadPathCode h tvs t)) := by
  unfold eventCount
  exact card_le_mul_of_injOn
    ((fullMatchingSpace h s).filter (canonicalDepthBad h tvs t))
    (fullMatchingSpace h s)
    (canonicalDepthBadEncoding h tvs t)
    (by
      intro P hP
      rw [canonicalDepthBadEncoding_fst]
      exact (Finset.mem_filter.mp hP).1)
    (canonicalDepthBadEncoding_injective_on (h := h) (s := s) (t := t) tvs)

end PHPFullMatchingBadPathEncoding
end PvNP
