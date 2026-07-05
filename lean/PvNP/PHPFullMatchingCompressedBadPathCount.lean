import PvNP.PHPFullMatchingBadPathEncoding

/-!
# Compressed bad-path count scaffold over full matching space

This module is the first successor scaffold after the conservative
`PHPFullMatchingBadPathEncoding` count.  It proves that variables queried by the
restricted canonical DNF tree are not merely in the original PHP DNF support:
they are free under the concrete full matching restriction.  It also exposes a
conditional compressed-count interface: once a later encoder maps bad points into
a genuinely smaller target with path codes and is proved injective, the finite
bad-event count follows from the existing cardinality backbone.

HONEST SCOPE STATEMENT: this is deterministic/free-variable infrastructure plus
a conditional finite-counting scaffold only.  It does not construct the final
compressed encoder, does not bound matching-space fibers, does not prove a
geometric collapse-probability bound, and is not a PHP switching lemma.  It also
does not prove any Frege/PHP lower bound, NP/circuit lower bound, or P-vs-NP
claim.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingCompressedBadPathCount

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open PHPMatchingDistribution
open PHPFullMatchingDistribution
open PHPFullMatchingCanonicalDT
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingProbability
open SwitchingCardLemma

/-! ## Restricted DNF variables are free -/

/-- Every literal surviving a DNF term restriction has a free variable under the
restriction. -/
theorem termRestrict_mem_free {n : Nat} (rho : Restriction n) :
    forall (t t' : Term n), termRestrict rho t = some t' ->
      forall l, l ∈ t' -> rho l.var = none
  | [], t', h, l, hl => by
      simp only [termRestrict, Option.some.injEq] at h
      subst h
      exact absurd hl (List.not_mem_nil l)
  | m :: t, t', h, l, hl => by
      simp only [termRestrict] at h
      cases hrho : rho m.var with
      | none =>
          simp only [hrho] at h
          cases hrec : termRestrict rho t with
          | some t'' =>
              simp only [hrec, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hl with hhead | htail
              · subst hhead
                exact hrho
              · exact termRestrict_mem_free rho t t'' hrec l htail
          | none =>
              simp only [hrec] at h
              exact absurd h (by simp)
      | some b =>
          simp only [hrho] at h
          by_cases hb : b = m.sign
          · simp only [if_pos hb] at h
            exact termRestrict_mem_free rho t t' h l hl
          · simp only [if_neg hb] at h
            exact absurd h (by simp)

/-- Every literal variable in a restricted DNF is free under the restriction. -/
theorem dnfVarsIn_dnfRestrict_free {n : Nat}
    (rho : Restriction n) (D : DNF n) :
    DNFVarsIn (dnfRestrict rho D)
      ((Finset.univ : Finset (Fin n)).filter (fun v => rho v = none)) := by
  intro t ht l hl
  unfold dnfRestrict at ht
  rw [List.mem_filterMap] at ht
  obtain ⟨t0, _ht0, hres⟩ := ht
  have hfree := termRestrict_mem_free rho t0 t hres l hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ l.var, hfree⟩

/-! ## Canonical restricted PHP DNF trees query only free variables -/

/-- Every variable queried by the restricted canonical PHP DNF tree is free under
the full matching restriction used to build that tree. -/
theorem treeVarsIn_free_canonicalRestrictedDNFTree {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool))) :
    TreeVarsIn (canonicalRestrictedDNFTree h tvs P)
      ((Finset.univ : Finset (Fin (Nat.succ (h * h)))).filter
        (fun v => fullRestrictionOf P v = none)) := by
  unfold canonicalRestrictedDNFTree
  exact treeVarsIn_termCanonicalDT
    (dnfRestrict (fullRestrictionOf P) (phpDNFAsDNF h tvs))
    (dnfVarsIn_dnfRestrict_free (fullRestrictionOf P) (phpDNFAsDNF h tvs))

/-- Every variable on the deepest path of the restricted canonical PHP DNF tree
is free under the full matching restriction used to build that tree. -/
theorem deepestPath_canonicalRestrictedDNFTree_free {h : Nat}
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (tvs : List (List (Fin h × Fin h × Bool)))
    (vd : Fin (Nat.succ (h * h)) × Bool)
    (hvd : vd ∈ deepestPath (canonicalRestrictedDNFTree h tvs P)) :
    fullRestrictionOf P vd.1 = none := by
  have hvset := deepestPath_treeVarsIn (canonicalRestrictedDNFTree h tvs P)
    (treeVarsIn_free_canonicalRestrictedDNFTree P tvs) vd hvd
  exact (Finset.mem_filter.mp hvset).2

/-- A bad-path code with both original-support and free-variable certificates.
This type is still `P`-dependent, so it is certification infrastructure, not the
final compressed code space. -/
def FreeBadPathCode (h : Nat)
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) : Type :=
  Fin t -> {v : Fin (Nat.succ (h * h)) //
    v ∈ phpDNFVarSet h tvs ∧ fullRestrictionOf P v = none} × Bool

noncomputable instance instFintypeFreeBadPathCode {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    Fintype (FreeBadPathCode h tvs t P) := by
  classical
  unfold FreeBadPathCode
  infer_instance

noncomputable instance instDecidableEqFreeBadPathCode {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) :
    DecidableEq (FreeBadPathCode h tvs t P) := by
  classical
  infer_instance

/-- Extract a deepest-path code whose queried variables are certified both to
come from the original PHP DNF support and to be free under `fullRestrictionOf P`.
-/
noncomputable def canonicalDepthBadFreeCode {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P) :
    FreeBadPathCode h tvs t P := by
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
  have hfree : fullRestrictionOf P vd.1 = none := by
    exact deepestPath_canonicalRestrictedDNFTree_free P tvs vd hvdmem
  exact (⟨vd.1, ⟨hv, hfree⟩⟩, vd.2)

/-- Every bad matching point has a free-variable-certified path code. -/
theorem canonicalDepthBad_freePathCode_exists {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) (t : Nat)
    (P : Finset (Fin h) × Equiv.Perm (Fin h))
    (hbad : canonicalDepthBad h tvs t P) :
    Nonempty (FreeBadPathCode h tvs t P) :=
  ⟨canonicalDepthBadFreeCode tvs t P hbad⟩

/-! ## Matching-space row-free multiplicity scaffold -/

/-- A full matching point leaves all rows in `rows` free.  Since
`fullRestrictionOf P (phpVar h h i j) = none` iff `i ∉ P.1`, this is the
row-level event consumed by later path-code fiber bounds. -/
def fullRowsFree {h : Nat} (rows : Finset (Fin h))
    (P : Finset (Fin h) × Equiv.Perm (Fin h)) : Prop :=
  forall i, i ∈ rows -> i ∉ P.1

instance instDecidablePredFullRowsFree {h : Nat} (rows : Finset (Fin h)) :
    DecidablePred (fullRowsFree rows) := by
  intro P
  unfold fullRowsFree
  infer_instance

/-- Exact count of full matching points that leave a specified set of rows free.
The subset component must be an `s`-subset of the complement of `rows`, and the
permutation component is arbitrary.  This is a row-level multiplicity scaffold,
not yet a path-code fiber theorem. -/
theorem fullRowsFree_count (h s : Nat) (rows : Finset (Fin h)) :
    eventCount (fullMatchingSpace h s) (fullRowsFree rows) =
      Nat.choose (h - rows.card) s * Fintype.card (Equiv.Perm (Fin h)) := by
  have hfilter :
      (fullMatchingSpace h s).filter (fullRowsFree rows) =
        (((Finset.univ : Finset (Fin h)) \ rows).powersetCard s).product
          (permSpace h) := by
    ext P
    constructor
    · intro hP
      have hmem := (Finset.mem_filter.mp hP).1
      have hfree := (Finset.mem_filter.mp hP).2
      have hprod : P.1 ∈ subsetSpace h s ∧ P.2 ∈ permSpace h := by
        change P ∈ subsetSpace h s ×ˢ permSpace h at hmem
        exact Finset.mem_product.mp hmem
      have hSinfo : P.1 ⊆ (Finset.univ : Finset (Fin h)) ∧ P.1.card = s := by
        exact Finset.mem_powersetCard.mp (by simpa [subsetSpace] using hprod.1)
      have hsubsetComp : P.1 ⊆ (Finset.univ : Finset (Fin h)) \ rows := by
        intro i hi
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ i, fun hrow => hfree i hrow hi⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨hsubsetComp, hSinfo.2⟩, hprod.2⟩
    · intro hP
      have hprod : P.1 ∈ (((Finset.univ : Finset (Fin h)) \ rows).powersetCard s) ∧
          P.2 ∈ permSpace h := by
        change P ∈ (((Finset.univ : Finset (Fin h)) \ rows).powersetCard s) ×ˢ
          permSpace h at hP
        exact Finset.mem_product.mp hP
      let hS := hprod.1
      let hperm := hprod.2
      have hS' := Finset.mem_powersetCard.mp hS
      have hSsubset : P.1 ⊆ (Finset.univ : Finset (Fin h)) := by
        intro i _
        exact Finset.mem_univ i
      have hSspace : P.1 ∈ subsetSpace h s := by
        exact Finset.mem_powersetCard.mpr ⟨hSsubset, hS'.2⟩
      have hmem : P ∈ fullMatchingSpace h s := by
        exact Finset.mem_product.mpr ⟨by simpa [subsetSpace] using hSspace, hperm⟩
      have hfree : fullRowsFree rows P := by
        intro i hirow hiS
        have hiComp := hS'.1 hiS
        exact (Finset.mem_sdiff.mp hiComp).2 hirow
      exact Finset.mem_filter.mpr ⟨by simpa [fullMatchingSpace] using hmem, hfree⟩
  unfold eventCount
  have hrows : rows ⊆ (Finset.univ : Finset (Fin h)) := by
    intro i _
    exact Finset.mem_univ i
  rw [hfilter]
  calc
    ((((Finset.univ : Finset (Fin h)) \ rows).powersetCard s).product
        (permSpace h)).card
        = (((Finset.univ : Finset (Fin h)) \ rows).powersetCard s).card *
            (permSpace h).card := by
          exact Finset.card_product _ _
    _ = Nat.choose (h - rows.card) s *
          Fintype.card (Equiv.Perm (Fin h)) := by
          rw [Finset.card_powersetCard, card_permSpace, Finset.card_sdiff hrows]
          simp

/-! ## Conditional compressed-target counting scaffold -/

/-- Conditional compressed-count scaffold: if a later encoder maps bad matching
points into a target `Target` paired with the S2119 path-code type and is
injective on the bad set, then the bad-event count is bounded by
`Target.card * card BadPathCode`.  This theorem deliberately leaves the actual
compressed target and injectivity proof to later work. -/
theorem canonicalDepthBad_count_le_target_mul_pathCode_of_injOn {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    {beta : Type} [DecidableEq beta]
    (Target : Finset beta)
    (encode : Finset (Fin h) × Equiv.Perm (Fin h) ->
      beta × BadPathCode h tvs t)
    (hmem : forall P, P ∈
      (fullMatchingSpace h s).filter (canonicalDepthBad h tvs t) ->
      (encode P).1 ∈ Target)
    (hinj : Set.InjOn encode
      ↑((fullMatchingSpace h s).filter (canonicalDepthBad h tvs t))) :
    eventCount (fullMatchingSpace h s) (canonicalDepthBad h tvs t) <=
      Target.card * Fintype.card (BadPathCode h tvs t) := by
  classical
  unfold eventCount
  exact card_le_mul_of_injOn
    ((fullMatchingSpace h s).filter (canonicalDepthBad h tvs t))
    Target encode hmem hinj

end PHPFullMatchingCompressedBadPathCount
end PvNP
