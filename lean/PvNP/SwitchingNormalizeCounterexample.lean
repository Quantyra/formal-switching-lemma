import PvNP.SwitchingNormalize

/-!
# S2233-A1': finite counterexample to the naive normalize card bridge

This module pins a one-variable duplicate-literal DNF where DNF normalization
shortens the term-canonical decision-tree depth and therefore strictly shrinks
the term bad set at `(s, ℓ) = (2, 1)`.

Boundary: this is only a counterexample to the naive
`NormalizeBadSetCardBridge`.  It is not a proof of `SwitchingLemma`, term
inhabitation beyond the named counterexample, AC0, Frege/PHP, any lower bound, or
P ≠ NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP

open CNFModel
open BoundedDepthCanonicalDT
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open SwitchingLemmaStatement
open SwitchingEncodeConstruct
open SwitchingTermCanonicalDT
open FormulaSyntacticDNFNormalization

/-- The unique positive literal on `Fin 1`. -/
def x1 : Literal 1 := ⟨0, true⟩

/-- A one-term DNF with a duplicated occurrence of `x1`. -/
def Ddup : DNF 1 := [[x1, x1]]

/-- The all-free restriction on one variable. -/
def rhoFree1 : Restriction 1 := fun _ => none

theorem normalizeDNF_Ddup : normalizeDNF Ddup = [[x1]] := by
  decide

theorem dnfRestrict_rhoFree1_Ddup : dnfRestrict rhoFree1 Ddup = Ddup := by
  decide

theorem dnfRestrict_rhoFree1_normalizeDNF_Ddup :
    dnfRestrict rhoFree1 (normalizeDNF Ddup) = [[x1]] := by
  decide

theorem dtDepth_termCanonicalDT_dnfRestrict_Ddup :
    dtDepth (termCanonicalDT (dnfRestrict rhoFree1 Ddup)) = 2 := by
  simp [Ddup, x1, rhoFree1, dnfRestrict, termRestrict, termCanonicalDT,
    queryTerm, assignVar, assignTerm]

theorem dtDepth_termCanonicalDT_dnfRestrict_normalizeDNF_Ddup :
    dtDepth (termCanonicalDT (dnfRestrict rhoFree1 (normalizeDNF Ddup))) = 1 := by
  simp [Ddup, x1, rhoFree1, normalizeDNF, dedupTerm, termContradictoryB,
    literalComplementary, dnfRestrict, termRestrict, termCanonicalDT, queryTerm,
    assignVar, assignTerm]

theorem stars_eq_one_iff_rhoFree1 (ρ : Restriction 1) :
    stars ρ = 1 ↔ ρ = rhoFree1 := by
  constructor
  · intro h
    funext v
    have hv : v = 0 := Subsingleton.elim v 0
    subst hv
    simp [rhoFree1]
    by_contra hnone
    have hfilter_empty :
        (({0} : Finset (Fin 1)).filter (fun v : Fin 1 => ρ v = none)) = ∅ := by
      ext w
      have hw : w = 0 := Subsingleton.elim w 0
      subst hw
      simp [hnone]
    simp [stars, hfilter_empty] at h
  · intro h
    subst h
    simp [stars, rhoFree1]

theorem rhoFree1_mem_badSetTerm_Ddup_2_1 :
    rhoFree1 ∈ badSetTerm Ddup 2 1 := by
  rw [mem_badSetTerm]
  exact ⟨by simp [stars, rhoFree1], by
    rw [dtDepth_termCanonicalDT_dnfRestrict_Ddup]⟩

theorem rhoFree1_not_mem_badSetTerm_normalizeDNF_Ddup_2_1 :
    rhoFree1 ∉ badSetTerm (normalizeDNF Ddup) 2 1 := by
  rw [mem_badSetTerm]
  intro h
  rw [dtDepth_termCanonicalDT_dnfRestrict_normalizeDNF_Ddup] at h
  omega

theorem badSetTerm_Ddup_2_1_eq_singleton :
    badSetTerm Ddup 2 1 = {rhoFree1} := by
  ext ρ
  rw [mem_badSetTerm, Finset.mem_singleton]
  constructor
  · intro h
    exact (stars_eq_one_iff_rhoFree1 ρ).mp h.1
  · intro h
    subst h
    exact ⟨by simp [stars, rhoFree1], by
      rw [dtDepth_termCanonicalDT_dnfRestrict_Ddup]⟩

theorem badSetTerm_normalizeDNF_Ddup_2_1_eq_empty :
    badSetTerm (normalizeDNF Ddup) 2 1 = ∅ := by
  ext ρ
  rw [mem_badSetTerm]
  simp only [Finset.not_mem_empty, iff_false]
  intro h
  have hρ : ρ = rhoFree1 := (stars_eq_one_iff_rhoFree1 ρ).mp h.1
  subst hρ
  rw [dtDepth_termCanonicalDT_dnfRestrict_normalizeDNF_Ddup] at h
  omega

theorem badSetTerm_Ddup_card_gt_normalized_2_1 :
    (badSetTerm Ddup 2 1).card >
      (badSetTerm (normalizeDNF Ddup) 2 1).card := by
  rw [badSetTerm_Ddup_2_1_eq_singleton,
    badSetTerm_normalizeDNF_Ddup_2_1_eq_empty]
  simp

theorem not_normalizeBadSetCardBridge_one :
    ¬ SwitchingNormalize.NormalizeBadSetCardBridge 1 := by
  intro h
  have hle := h Ddup 2 1
  have hgt := badSetTerm_Ddup_card_gt_normalized_2_1
  exact Nat.not_lt_of_ge hle hgt

end PvNP
