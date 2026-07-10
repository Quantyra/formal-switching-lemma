import PvNP.PHPFullMatchingRealizedCodeSplit

/-!
# Parametric row-collision obstruction for full-matching realized codes

Finite square full-matching realized-code bookkeeping only.  This module builds,
for each row of the square `h × h` family, one realized canonical bad-path code
and injects rows into the row-collision realized-code set.

No PHP switching lemma, Frege/PHP lower bound, rectangular `p > h` result,
NP/circuit lower bound, arbitrary AC0 result, or P-vs-NP claim is stated or
proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingRealizedCodeParametricObstruction

open CNFModel
open BoundedDepthCanonicalDT
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingCompressedBadPathCount
open PHPFullMatchingDistribution
open PHPFullMatchingProbability
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeSplit
open PHPFullMatchingStageRows
open PHPRestrictedDepthFloor
open PHPMatchingDistribution
open PHPSearchFloor
open RestrictedPHPFloor
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT

/-! ## The full-row DNF family -/

/-- The positive row term containing all columns of a row. -/
def fullRowTerm (h : Nat) (r : Fin h) : List (Fin h × Fin h × Bool) :=
  List.ofFn (fun c : Fin h => (r, c, true))

/-- The DNF with one full positive row term for every row. -/
def fullRowTvs (h : Nat) : List (List (Fin h × Fin h × Bool)) :=
  List.ofFn (fun r : Fin h => fullRowTerm h r)

/-- The full-matching point fixing every row except `r`, along the identity
permutation. -/
def fullRowP (h : Nat) (r : Fin h) : Finset (Fin h) × Equiv.Perm (Fin h) :=
  (Finset.univ.erase r, Equiv.refl (Fin h))

@[simp] theorem fullRowTerm_length (h : Nat) (r : Fin h) :
    (fullRowTerm h r).length = h := by
  simp [fullRowTerm]

@[simp] theorem fullRowTvs_length (h : Nat) :
    (fullRowTvs h).length = h := by
  simp [fullRowTvs]

theorem mem_fullRowTvs_iff {h : Nat} {tv : List (Fin h × Fin h × Bool)} :
    tv ∈ fullRowTvs h ↔ ∃ r : Fin h, tv = fullRowTerm h r := by
  classical
  unfold fullRowTvs
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem fullRowP_mem_fullMatchingSpace {h : Nat} (_hh : 1 <= h) (r : Fin h) :
    fullRowP h r ∈ fullMatchingSpace h (h - 1) := by
  classical
  unfold fullRowP fullMatchingSpace subsetSpace permSpace
  refine Finset.mem_product.mpr ⟨?_, by simp⟩
  rw [Finset.mem_powersetCard]
  constructor
  · intro x hx
    simp at hx ⊢
  · simp [Finset.card_erase_of_mem]

/-! ## Generic depth lower bounds for the term-canonical head block -/

theorem dtDepth_queryTerm_ge_length {n : Nat} :
    ∀ (vars : Term n) (D : DNF n), vars.length <= dtDepth (queryTerm vars D)
  | [], D => by simp
  | l :: vs, D => by
      rw [queryTerm_cons]
      have ih := dtDepth_queryTerm_ge_length vs (assignVar l.var false D)
      simp only [List.length_cons, dtDepth_node]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.succ_le_succ (Nat.le_trans ih (Nat.le_max_left _ _))

theorem dtDepth_termCanonicalDT_cons_ge_length {n : Nat}
    (t : Term n) (D : DNF n) :
    t.length <= dtDepth (termCanonicalDT (t :: D)) := by
  cases t with
  | nil => simp [termCanonicalDT]
  | cons l vs =>
      rw [termCanonicalDT_cons_cons]
      have hq := dtDepth_queryTerm_ge_length vs
        (assignVar l.var false ((l :: vs) :: D))
      simp only [List.length_cons, dtDepth_node]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.succ_le_succ (Nat.le_trans hq (Nat.le_max_left _ _))

/-! ## Restriction of the full-row family -/

theorem termRestrict_eq_self_of_forall_none {n : Nat} (ρ : Restriction n) :
    ∀ t : Term n, (∀ l ∈ t, ρ l.var = none) -> termRestrict ρ t = some t
  | [], _ => by simp [termRestrict]
  | l :: t, hfree => by
      have hl : ρ l.var = none := hfree l (by simp)
      have ht : termRestrict ρ t = some t :=
        termRestrict_eq_self_of_forall_none ρ t (by
          intro m hm
          exact hfree m (by simp [hm]))
      simp [termRestrict, hl, ht]

theorem termRestrict_eq_none_of_mem_false {n : Nat} (ρ : Restriction n) :
    ∀ t : Term n, ∀ l ∈ t, ∀ b, ρ l.var = some b -> b ≠ l.sign ->
      termRestrict ρ t = none
  | [], l, hl, _b, _hρ, _hne => by simp at hl
  | m :: t, l, hl, b, hρ, hne => by
      rcases List.mem_cons.mp hl with rfl | hlt
      · simp [termRestrict, hρ, hne]
      · by_cases hmρ : ρ m.var = none
        · have ih := termRestrict_eq_none_of_mem_false ρ t l hlt b hρ hne
          simp [termRestrict, hmρ, ih]
        · rcases hsome : ρ m.var with _ | bm
          · exact False.elim (hmρ hsome)
          · by_cases hbm : bm = m.sign
            · have ih := termRestrict_eq_none_of_mem_false ρ t l hlt b hρ hne
              simp [termRestrict, hsome, hbm, ih]
            · simp [termRestrict, hsome, hbm]

theorem termRestrict_fullRowTerm_self {h : Nat} (r : Fin h) :
    termRestrict (fullRestrictionOf (fullRowP h r))
      (phpTermAsTerm h (fullRowTerm h r)) =
        some (phpTermAsTerm h (fullRowTerm h r)) := by
  classical
  apply termRestrict_eq_self_of_forall_none
  intro l hl
  unfold phpTermAsTerm at hl
  rw [List.mem_map] at hl
  rcases hl with ⟨e, he, rfl⟩
  unfold phpLit
  rw [fullRestrictionOf_phpVar_eq_none_iff]
  unfold fullRowTerm at he
  rw [List.mem_ofFn] at he
  rcases he with ⟨c, rfl⟩
  simp [phpLit, fullRowP]

theorem termRestrict_fullRowTerm_ne_none {h : Nat} (hh : 2 <= h)
    {r i : Fin h} (hri : i ≠ r) :
    termRestrict (fullRestrictionOf (fullRowP h r))
      (phpTermAsTerm h (fullRowTerm h i)) = none := by
  have hi : i ∈ (Finset.univ.erase r : Finset (Fin h)) := by
    simp [hri]
  classical
  obtain ⟨c, hci⟩ : ∃ c : Fin h, c ≠ i := by
    exact Fintype.exists_ne_of_one_lt_card (by simpa using hh) i
  apply termRestrict_eq_none_of_mem_false
    (l := phpLit h (i, c, true)) (b := false)
  · unfold phpTermAsTerm fullRowTerm
    rw [List.mem_map]
    refine ⟨(i, c, true), ?_, rfl⟩
    rw [List.mem_ofFn]
    exact ⟨c, rfl⟩
  · unfold phpLit fullRestrictionOf fullRowP matchingRestriction
    rw [dif_pos (phpVar_lt (p := h) (h := h) i c)]
    rw [pigeonOf_phpVar, holeOf_phpVar]
    simp [hi, hci]
  · simp [phpLit]

theorem filterMap_ofFn_eq_nil {α β : Type} {n : Nat} (G : Fin n → β) (F : β → Option α)
    (hF : ∀ i : Fin n, F (G i) = none) :
    List.filterMap F (List.ofFn G) = [] := by
  induction n generalizing α β with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      simpa [List.filterMap_cons, hF 0] using
        ih (fun i : Fin n => G i.succ) F (by intro i; exact hF i.succ)

theorem filterMap_ofFn_eq_singleton {α β : Type} {n : Nat} (G : Fin n → β) (F : β → Option α)
    (r : Fin n) (a : α) (hr : F (G r) = some a)
    (hne : ∀ i : Fin n, i ≠ r → F (G i) = none) :
    List.filterMap F (List.ofFn G) = [a] := by
  induction n generalizing α β a with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [List.ofFn_succ]
      by_cases hz : r = 0
      · subst r
        have htail : List.filterMap F (List.ofFn (fun i : Fin n => G i.succ)) = [] :=
          filterMap_ofFn_eq_nil (fun i : Fin n => G i.succ) F (by
            intro i
            exact hne i.succ (Fin.succ_ne_zero i))
        simpa [List.filterMap_cons, hr] using congrArg (fun xs => xs) htail
      · rcases Fin.exists_succ_eq_of_ne_zero hz with ⟨r0, rfl⟩
        have hhead : F (G 0) = none := hne 0 (Ne.symm (Fin.succ_ne_zero r0))
        have htail : List.filterMap F (List.ofFn (fun i : Fin n => G i.succ)) = [a] :=
          ih (fun i : Fin n => G i.succ) F r0 a hr (by
            intro i hi
            exact hne i.succ (by
              intro hs
              exact hi (Fin.succ_injective n hs)))
        simpa [List.filterMap_cons, hhead] using htail

theorem dnfRestrict_fullRowTvs_eq_singleton {h : Nat} (hh : 2 <= h)
    (r : Fin h) :
    dnfRestrict (fullRestrictionOf (fullRowP h r))
        (phpDNFAsDNF h (fullRowTvs h)) =
      [phpTermAsTerm h (fullRowTerm h r)] := by
  classical
  unfold dnfRestrict phpDNFAsDNF fullRowTvs
  rw [List.map_ofFn]
  simpa [Function.comp_def] using
    filterMap_ofFn_eq_singleton
      (G := fun i : Fin h => phpTermAsTerm h (fullRowTerm h i))
      (F := termRestrict (fullRestrictionOf (fullRowP h r)))
      r (phpTermAsTerm h (fullRowTerm h r))
      (termRestrict_fullRowTerm_self (h := h) r)
      (by
        intro i hi
        exact termRestrict_fullRowTerm_ne_none (h := h) hh hi)

theorem fullRowP_canonicalDepthBad {h : Nat} (hh : 2 <= h) (r : Fin h) :
    canonicalDepthBad h (fullRowTvs h) h (fullRowP h r) := by
  unfold canonicalDepthBad canonicalRestrictedDNFTree
  rw [dnfRestrict_fullRowTvs_eq_singleton (h := h) hh r]
  have hlen : (phpTermAsTerm h (fullRowTerm h r)).length = h := by
    simp [phpTermAsTerm, fullRowTerm]
  simpa [hlen] using
    dtDepth_termCanonicalDT_cons_ge_length
      (t := phpTermAsTerm h (fullRowTerm h r)) ([])

/-! ## Realized codes for each free row -/

noncomputable def fullRowCode (h : Nat) (r : Fin h) (hh : 2 <= h) :
    BadPathCode h (fullRowTvs h) h :=
  canonicalDepthBadCode (fullRowTvs h) h (fullRowP h r)
    (fullRowP_canonicalDepthBad (h := h) hh r)

theorem fullRowCode_mem_realized {h : Nat} (hh : 2 <= h) (r : Fin h) :
    fullRowCode h r hh ∈
      realizedBadPathCodes (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
  classical
  rw [mem_realizedBadPathCodes]
  refine ⟨fullRowP h r, ?_⟩
  unfold canonicalDepthBadCodeFiber
  rw [Finset.mem_filter]
  refine ⟨fullRowP_mem_fullMatchingSpace (h := h) (Nat.le_trans (by decide) hh) r,
    fullRowP_canonicalDepthBad (h := h) hh r, ?_⟩
  unfold canonicalDepthBadEncoding fullRowCode
  rw [dif_pos (fullRowP_canonicalDepthBad (h := h) hh r)]

theorem fullRowCode_injective {h : Nat} (hh : 2 <= h) :
    Function.Injective (fun r : Fin h => fullRowCode h r hh) := by
  classical
  intro r r' hcode
  let k : Fin h := ⟨0, by omega⟩
  have hfree : codeStageRow (fullRowCode h r hh) k ∉ (fullRowP h r).1 :=
    codeStageRow_free_of_encoding_eq_some (fullRowTvs h) (fullRowCode h r hh)
      (fullRowP h r) (fullRowP_canonicalDepthBad (h := h) hh r) (by
        unfold canonicalDepthBadEncoding fullRowCode
        rw [dif_pos (fullRowP_canonicalDepthBad (h := h) hh r)]) k
  have hfree'_tmp : codeStageRow (fullRowCode h r' hh) k ∉ (fullRowP h r').1 :=
    codeStageRow_free_of_encoding_eq_some (fullRowTvs h) (fullRowCode h r' hh)
      (fullRowP h r') (fullRowP_canonicalDepthBad (h := h) hh r') (by
        unfold canonicalDepthBadEncoding fullRowCode
        rw [dif_pos (fullRowP_canonicalDepthBad (h := h) hh r')]) k
  have hfree' : codeStageRow (fullRowCode h r hh) k ∉ (fullRowP h r').1 := by
    simpa [hcode] using hfree'_tmp
  have hr : codeStageRow (fullRowCode h r hh) k = r := by
    simpa [fullRowP] using hfree
  have hr' : codeStageRow (fullRowCode h r hh) k = r' := by
    simpa [fullRowP] using hfree'
  exact hr.symm.trans hr'

theorem fullRowTvs_simple (h : Nat) :
    SimpleDNF (phpDNFAsDNF h (fullRowTvs h)) := by
  classical
  intro t ht
  rw [phpDNFAsDNF, List.mem_map] at ht
  rcases ht with ⟨tv, htv, rfl⟩
  rw [mem_fullRowTvs_iff] at htv
  rcases htv with ⟨r, rfl⟩
  unfold SimpleTerm phpTermAsTerm fullRowTerm phpLit
  simpa [List.map_map, Function.comp_def, phpLit, fullRowTerm] using
    (List.nodup_ofFn.mpr (by
      intro a b hab
      exact (phpVar_inj hab).2) :
      (List.ofFn fun c : Fin h => phpVar h h r c).Nodup)

/-! ## Parametric cardinal obstruction -/

theorem fullRowTvs_rowCollisionRealizedBadPathCodes_card_ge_h {h : Nat}
    (hh : 2 <= h) :
    h <= (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
      (fullRowTvs h)).card := by
  classical
  have heq : realizedBadPathCodes (h := h) (s := h - 1) (t := h) (fullRowTvs h) =
      rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h) (fullRowTvs h) := by
    exact realizedBadPathCodes_eq_rowCollisionRealizedBadPathCodes_of_simple_of_h_lt_s_add_t
      (h := h) (s := h - 1) (t := h) (fullRowTvs h) (fullRowTvs_simple h) (by omega)
  rw [← heq]
  simpa using Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := realizedBadPathCodes (h := h) (s := h - 1) (t := h) (fullRowTvs h))
    (f := fun r : Fin h => fullRowCode h r hh)
    (by intro r _; exact fullRowCode_mem_realized (h := h) hh r)
    (by intro a _ b _ hab; exact fullRowCode_injective (h := h) hh hab)

theorem fullRowTvs_denominator_le_rowCollisionRealizedBadPathCodes_card {h : Nat}
    (hh : 2 <= h) :
    h ^ (h / h) <= (rowCollisionRealizedBadPathCodes (h := h)
      (s := h - 1) (t := h) (fullRowTvs h)).card := by
  have hdiv : h / h = 1 := Nat.div_self (by omega)
  rw [hdiv, Nat.pow_one]
  exact fullRowTvs_rowCollisionRealizedBadPathCodes_card_ge_h (h := h) hh

theorem fullRowTvs_not_rowCollisionRealizedBadPathCodes_card_lt_denominator {h : Nat}
    (hh : 2 <= h) :
    ¬ (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
        (fullRowTvs h)).card < h ^ (h / h) := by
  exact not_lt_of_ge
    (fullRowTvs_denominator_le_rowCollisionRealizedBadPathCodes_card (h := h) hh)

theorem fullRowTvs_rowCollision_route_nontrivial_impossible {h : Nat}
    (hh : 2 <= h) :
    ¬ (rowCollisionRealizedBadPathCodes (h := h) (s := h - 1) (t := h)
        (fullRowTvs h)).card * (h - (h - 1)) ^ (h / h) < h ^ (h / h) := by
  have hone : (h - (h - 1)) ^ (h / h) = 1 := by
    have hbase : h - (h - 1) = 1 := by omega
    simp [hbase]
  simpa [hone] using
    fullRowTvs_not_rowCollisionRealizedBadPathCodes_card_lt_denominator (h := h) hh

end PHPFullMatchingRealizedCodeParametricObstruction
end PvNP
