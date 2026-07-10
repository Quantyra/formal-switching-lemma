import PvNP.PHPFullMatchingRealizedCodeObstruction
import PvNP.PHPFullMatchingStageRowObstruction

/-!
# Strict row-variable-unique realized-code obstruction

This module adds an extra whole-DNF PHP row-variable-uniqueness hypothesis:
across the joined DNF literal-value list, any two entries with the same row must
use the same PHP column.  Under this extra finite hypothesis, realized simple-DNF
bad-path codes in the `2 x 2`, `s = 1`, `t = 2` full-matching square are
impossible: the two queried variables would force two distinct recovered rows,
but `fullMatchingSpace 2 1` leaves only one row free.  The earlier whole-DNF
row-uniqueness hypothesis, requiring equality of row/column/sign triples, remains
available as a stronger corollary.  The same row-variable hypothesis also gives
a parametric finite row-capacity obstruction: if a realized code has `t`
distinct recovered rows and a matching point selects `s` rows disjoint from all
of them, then `s + t <= h`; hence no realized code exists when `h < s + t`.

The scope is only this full-square finite realized-code diagnostic.  No PHP
switching lemma, Frege/PHP lower bound, NP/circuit lower bound, AC0 lower bound,
or P-vs-NP claim is stated or proved here.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFullMatchingRowUniqueStrict

open PHPFullMatchingBadPathEncoding
open PHPFullMatchingCanonicalDT
open PHPFullMatchingCompressedBadPathCount
open PHPFullMatchingDistribution
open PHPFullMatchingProbability
open PHPFullMatchingRealizedCodeCount
open PHPFullMatchingRealizedCodeObstruction
open PHPFullMatchingStageRows
open PHPMatchingDistribution
open PHPSearchFloor
open RestrictedPHPFloor
open SwitchingEncodeConstruct

/-! ## Whole-DNF row-variable uniqueness -/

/-- Whole-DNF PHP row-variable uniqueness: across the joined DNF literal-value
list, any two entries with the same row use the same PHP column.  Sign equality
is intentionally not required. -/
def PHPDNFGlobalRowVarUnique {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ e₁ ∈ tvs.join, ∀ e₂ ∈ tvs.join, e₁.1 = e₂.1 -> e₁.2.1 = e₂.2.1

/-- Whole-DNF PHP row uniqueness: across the joined DNF literal-value list, any
two entries with the same row are the same row/column/sign triple.  This is
stronger than `SimpleDNF`, which is term-local after translation to ordinary DNF
syntax. -/
def PHPDNFGlobalRowUnique {h : Nat}
    (tvs : List (List (Fin h × Fin h × Bool))) : Prop :=
  ∀ e₁ ∈ tvs.join, ∀ e₂ ∈ tvs.join, e₁.1 = e₂.1 -> e₁ = e₂

/-- Whole-DNF row uniqueness is stronger than the row-variable condition needed
below. -/
theorem globalRowVarUnique_of_globalRowUnique {h : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))} :
    PHPDNFGlobalRowUnique tvs -> PHPDNFGlobalRowVarUnique tvs := by
  intro huniq e₁ he₁ e₂ he₂ hrow
  exact congrArg (fun e : Fin h × Fin h × Bool => e.2.1)
    (huniq e₁ he₁ e₂ he₂ hrow)

/-- The S2128 two-row/two-column witness is simple but not globally
row-variable-unique: row `0` occurs with two different columns. -/
theorem twoRowsTwoColsTvs_h2_not_globalRowVarUnique :
    ¬ PHPDNFGlobalRowVarUnique twoRowsTwoColsTvs_h2 := by
  intro huniq
  have hEq := huniq ((0 : Fin 2), (0 : Fin 2), true) (by simp [twoRowsTwoColsTvs_h2])
    ((0 : Fin 2), (1 : Fin 2), true) (by simp [twoRowsTwoColsTvs_h2]) rfl
  have hNe : (0 : Fin 2) ≠ (1 : Fin 2) := by
    decide
  exact hNe hEq

/-- The S2128 two-row/two-column witness is simple but not globally row-unique:
row `0` occurs with two different columns. -/
theorem twoRowsTwoColsTvs_h2_not_globalRowUnique :
    ¬ PHPDNFGlobalRowUnique twoRowsTwoColsTvs_h2 := by
  intro huniq
  have hEq := huniq ((0 : Fin 2), (0 : Fin 2), true) (by simp [twoRowsTwoColsTvs_h2])
    ((0 : Fin 2), (1 : Fin 2), true) (by simp [twoRowsTwoColsTvs_h2]) rfl
  have hNe : ((0 : Fin 2), (0 : Fin 2), true) ≠ ((0 : Fin 2), (1 : Fin 2), true) := by
    decide
  exact hNe hEq

/-! ## Global row-variable uniqueness forces injective stage rows -/

private theorem codeStageSupportEntry_exists {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) :
    ∃ e : Fin h × Fin h × Bool,
      e ∈ tvs.join ∧ phpVar h h e.1 e.2.1 =
        ((c k).1 : Fin (Nat.succ (h * h))) := by
  have hv : ((c k).1 : Fin (Nat.succ (h * h))) ∈ phpDNFVarSet h tvs :=
    (c k).1.2
  unfold phpDNFVarSet at hv
  rw [List.mem_toFinset] at hv
  exact List.mem_map.mp hv

open Classical in
private noncomputable def codeStageSupportEntry {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) : Fin h × Fin h × Bool :=
  Classical.choose (codeStageSupportEntry_exists c k)

private theorem codeStageSupportEntry_mem_join {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) :
    codeStageSupportEntry c k ∈ tvs.join := by
  unfold codeStageSupportEntry
  exact (Classical.choose_spec (codeStageSupportEntry_exists c k)).1

private theorem codeStageSupportEntry_var_eq {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) :
    phpVar h h (codeStageSupportEntry c k).1 (codeStageSupportEntry c k).2.1 =
      ((c k).1 : Fin (Nat.succ (h * h))) := by
  unfold codeStageSupportEntry
  exact (Classical.choose_spec (codeStageSupportEntry_exists c k)).2

private theorem codeStageSupportEntry_row_eq_codeStageRow {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (c : BadPathCode h tvs t) (k : Fin t) :
    (codeStageSupportEntry c k).1 = codeStageRow c k := by
  have hvar : phpVar h h (codeStageSupportEntry c k).1 (codeStageSupportEntry c k).2.1 =
      phpVar h h (codeStageRow c k) (codeStageEntry c k).2.1 := by
    rw [codeStageSupportEntry_var_eq c k, codeStageEntry_var_eq c k]
  exact (phpVar_inj hvar).1

/-- Under whole-DNF row-variable uniqueness, equal decoded rows force equal stored
code variables. -/
theorem codeStageVar_eq_of_globalRowVarUnique_row_eq {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (huniq : PHPDNFGlobalRowVarUnique tvs)
    (c : BadPathCode h tvs t) {k l : Fin t}
    (hrow : codeStageRow c k = codeStageRow c l) :
    ((c k).1 : Fin (Nat.succ (h * h))) =
      ((c l).1 : Fin (Nat.succ (h * h))) := by
  have hsrow : (codeStageSupportEntry c k).1 = (codeStageSupportEntry c l).1 := by
    rw [codeStageSupportEntry_row_eq_codeStageRow c k,
      codeStageSupportEntry_row_eq_codeStageRow c l, hrow]
  have hcol : (codeStageSupportEntry c k).2.1 = (codeStageSupportEntry c l).2.1 :=
    huniq (codeStageSupportEntry c k) (codeStageSupportEntry_mem_join c k)
      (codeStageSupportEntry c l) (codeStageSupportEntry_mem_join c l) hsrow
  calc
    ((c k).1 : Fin (Nat.succ (h * h)))
        = phpVar h h (codeStageSupportEntry c k).1 (codeStageSupportEntry c k).2.1 := by
          exact (codeStageSupportEntry_var_eq c k).symm
    _ = phpVar h h (codeStageSupportEntry c l).1 (codeStageSupportEntry c l).2.1 := by
          rw [hsrow, hcol]
    _ = ((c l).1 : Fin (Nat.succ (h * h))) := by
          exact codeStageSupportEntry_var_eq c l

/-- Under the stronger whole-DNF row uniqueness, equal decoded rows force equal
stored code variables. -/
theorem codeStageVar_eq_of_globalRowUnique_row_eq {h t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (huniq : PHPDNFGlobalRowUnique tvs)
    (c : BadPathCode h tvs t) {k l : Fin t}
    (hrow : codeStageRow c k = codeStageRow c l) :
    ((c k).1 : Fin (Nat.succ (h * h))) =
      ((c l).1 : Fin (Nat.succ (h * h))) :=
  codeStageVar_eq_of_globalRowVarUnique_row_eq
    (globalRowVarUnique_of_globalRowUnique huniq) c hrow

/-- For realized simple codes, the additional whole-DNF row-variable uniqueness
upgrades the existing variable injectivity to injectivity of recovered stage
rows. -/
theorem codeStageRow_injective_of_realized_simple_globalRowVarUnique {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowVarUnique tvs)
    (c : BadPathCode h tvs t)
    (hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c) :
    Function.Injective (codeStageRow (tvs := tvs) c) := by
  intro k l hrow
  exact codeStageVar_injective_of_realized_simple (h := h) (s := s) (t := t)
    hsimple c hreal (codeStageVar_eq_of_globalRowVarUnique_row_eq huniq c hrow)

/-- For realized simple codes, the stronger whole-DNF row uniqueness upgrades the
existing variable injectivity to injectivity of recovered stage rows. -/
theorem codeStageRow_injective_of_realized_simple_globalRowUnique {h s t : Nat}
    {tvs : List (List (Fin h × Fin h × Bool))}
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowUnique tvs)
    (c : BadPathCode h tvs t)
    (hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c) :
    Function.Injective (codeStageRow (tvs := tvs) c) :=
  codeStageRow_injective_of_realized_simple_globalRowVarUnique hsimple
    (globalRowVarUnique_of_globalRowUnique huniq) c hreal

private theorem codeStageRows_card_eq_two_of_injective_h2
    {tvs : List (List (Fin 2 × Fin 2 × Bool))}
    (c : BadPathCode 2 tvs 2)
    (hinj : Function.Injective (codeStageRow (tvs := tvs) c)) :
    (codeStageRows c).card = 2 := by
  classical
  unfold codeStageRows
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

private theorem finset_fin_two_eq_univ_of_card_two (S : Finset (Fin 2))
    (hcard : S.card = 2) : S = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  simpa [Fintype.card_fin] using hcard

/-- Finite `2 x 2`, `s = 1`, `t = 2` strict realized-code result: with
`SimpleDNF` plus whole-DNF row-variable uniqueness, no canonical bad-path code is
realized. -/
theorem twoByTwo_realizedBadPathCodes_eq_empty_of_globalRowVarUnique
    (tvs : List (List (Fin 2 × Fin 2 × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF 2 tvs))
    (huniq : PHPDNFGlobalRowVarUnique tvs) :
    realizedBadPathCodes (h := 2) (s := 1) (t := 2) tvs = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hreal : canonicalDepthBadCodeFiberNonempty (h := 2) (s := 1) (t := 2) tvs c :=
    (mem_realizedBadPathCodes (h := 2) (s := 1) (t := 2) tvs c).mp hc
  have hinj : Function.Injective (codeStageRow (tvs := tvs) c) :=
    codeStageRow_injective_of_realized_simple_globalRowVarUnique
      (h := 2) (s := 1) (t := 2) hsimple huniq c hreal
  have hrowsCard : (codeStageRows c).card = 2 :=
    codeStageRows_card_eq_two_of_injective_h2 c hinj
  have hrowsUniv : codeStageRows c = Finset.univ :=
    finset_fin_two_eq_univ_of_card_two (codeStageRows c) hrowsCard
  rcases hreal with ⟨P, hP⟩
  rw [canonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨hspace, hbad, henc⟩ := hP
  have hfree : fullRowsFree (codeStageRows c) P :=
    fullRowsFree_codeStageRows_of_encoding_eq_some tvs c P hbad henc
  have hPcard : P.1.card = 1 := by
    unfold fullMatchingSpace subsetSpace at hspace
    have hsubset := (Finset.mem_product.mp hspace).1
    exact (Finset.mem_powersetCard.mp hsubset).2
  have hPnonempty : P.1.Nonempty := by
    rw [Finset.card_eq_one] at hPcard
    rcases hPcard with ⟨r, hr⟩
    exact ⟨r, by simp [hr]⟩
  rcases hPnonempty with ⟨r, hrP⟩
  have hrRows : r ∈ codeStageRows c := by
    rw [hrowsUniv]
    exact Finset.mem_univ r
  exact hfree r hrRows hrP

/-- Finite `2 x 2`, `s = 1`, `t = 2` strict realized-code result under the
stronger whole-DNF row uniqueness. -/
theorem twoByTwo_realizedBadPathCodes_eq_empty_of_globalRowUnique
    (tvs : List (List (Fin 2 × Fin 2 × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF 2 tvs))
    (huniq : PHPDNFGlobalRowUnique tvs) :
    realizedBadPathCodes (h := 2) (s := 1) (t := 2) tvs = ∅ :=
  twoByTwo_realizedBadPathCodes_eq_empty_of_globalRowVarUnique tvs hsimple
    (globalRowVarUnique_of_globalRowUnique huniq)

/-- Cardinality form of the same finite strict result. -/
theorem twoByTwo_realizedBadPathCodes_card_lt_denominator_of_globalRowVarUnique
    (tvs : List (List (Fin 2 × Fin 2 × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF 2 tvs))
    (huniq : PHPDNFGlobalRowVarUnique tvs) :
    (realizedBadPathCodes (h := 2) (s := 1) (t := 2) tvs).card < 2 ^ (2 / 2) := by
  rw [twoByTwo_realizedBadPathCodes_eq_empty_of_globalRowVarUnique tvs hsimple huniq]
  norm_num

/-- Cardinality form under the stronger whole-DNF row uniqueness. -/
theorem twoByTwo_realizedBadPathCodes_card_lt_denominator_of_globalRowUnique
    (tvs : List (List (Fin 2 × Fin 2 × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF 2 tvs))
    (huniq : PHPDNFGlobalRowUnique tvs) :
    (realizedBadPathCodes (h := 2) (s := 1) (t := 2) tvs).card < 2 ^ (2 / 2) :=
  twoByTwo_realizedBadPathCodes_card_lt_denominator_of_globalRowVarUnique tvs hsimple
    (globalRowVarUnique_of_globalRowUnique huniq)

/-! ## Parametric finite row-capacity obstruction -/

/-- Parametric realized-code emptiness under whole-DNF row-variable uniqueness:
the `t` recovered stage rows are distinct, while any realized matching point
selects `s` rows disjoint from them.  Thus realization would force
`s + t <= h`, contradicting `h < s + t`. -/
theorem realizedBadPathCodes_eq_empty_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowVarUnique tvs)
    (hfit : h < s + t) :
    realizedBadPathCodes (h := h) (s := s) (t := t) tvs = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hreal : canonicalDepthBadCodeFiberNonempty (h := h) (s := s) (t := t) tvs c :=
    (mem_realizedBadPathCodes (h := h) (s := s) (t := t) tvs c).mp hc
  have hinj : Function.Injective (codeStageRow (tvs := tvs) c) :=
    codeStageRow_injective_of_realized_simple_globalRowVarUnique
      (h := h) (s := s) (t := t) hsimple huniq c hreal
  have hrowsCard : (codeStageRows c).card = t :=
    PHPFullMatchingStageRowObstruction.codeStageRows_card_eq_of_injective c hinj
  rcases hreal with ⟨P, hP⟩
  rw [canonicalDepthBadCodeFiber, Finset.mem_filter] at hP
  obtain ⟨hspace, hbad, henc⟩ := hP
  have hfree : fullRowsFree (codeStageRows c) P :=
    fullRowsFree_codeStageRows_of_encoding_eq_some tvs c P hbad henc
  have hPcard : P.1.card = s := by
    unfold fullMatchingSpace subsetSpace at hspace
    have hsubset := (Finset.mem_product.mp hspace).1
    exact (Finset.mem_powersetCard.mp hsubset).2
  have hdisj : Disjoint P.1 (codeStageRows c) := by
    rw [Finset.disjoint_left]
    intro r hrP hrRows
    exact hfree r hrRows hrP
  have hcardUnion : (P.1 ∪ codeStageRows c).card = s + t := by
    rw [Finset.card_union_of_disjoint hdisj, hPcard, hrowsCard]
  have hle : s + t <= h := by
    rw [← hcardUnion]
    simpa [Fintype.card_fin] using
      (Finset.card_le_univ (P.1 ∪ codeStageRows c) :
        (P.1 ∪ codeStageRows c).card <= Fintype.card (Fin h))
  exact (Nat.not_lt_of_ge hle) hfit

/-- Parametric realized-code emptiness under the stronger whole-DNF row
uniqueness hypothesis. -/
theorem realizedBadPathCodes_eq_empty_of_simple_globalRowUnique_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowUnique tvs)
    (hfit : h < s + t) :
    realizedBadPathCodes (h := h) (s := s) (t := t) tvs = ∅ :=
  realizedBadPathCodes_eq_empty_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    tvs hsimple (globalRowVarUnique_of_globalRowUnique huniq) hfit

/-- Strict realized-code cardinality consequence of the parametric row-capacity
obstruction under whole-DNF row-variable uniqueness. -/
theorem realizedBadPathCodes_card_lt_denominator_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowVarUnique tvs)
    (hfit : h < s + t) :
    (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card < h ^ (t / h) := by
  rw [realizedBadPathCodes_eq_empty_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    tvs hsimple huniq hfit]
  by_cases hh : h = 0
  · subst h
    simp
  · exact Nat.pow_pos (Nat.pos_of_ne_zero hh)

/-- Strict realized-code cardinality consequence under the stronger whole-DNF row
uniqueness hypothesis. -/
theorem realizedBadPathCodes_card_lt_denominator_of_simple_globalRowUnique_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowUnique tvs)
    (hfit : h < s + t) :
    (realizedBadPathCodes (h := h) (s := s) (t := t) tvs).card < h ^ (t / h) :=
  realizedBadPathCodes_card_lt_denominator_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    tvs hsimple (globalRowVarUnique_of_globalRowUnique huniq) hfit

/-- Zero-numerator `EventProbLe` consequence of the parametric row-capacity
obstruction under whole-DNF row-variable uniqueness. -/
theorem canonicalDepthBad_eventProbLe_zero_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowVarUnique tvs)
    (hfit : h < s + t) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t) 0 (h ^ (t / h)) := by
  have hempty := realizedBadPathCodes_eq_empty_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    tvs hsimple huniq hfit
  have hprob := canonicalDepthBad_eventProbLe_geometric_of_simple_realizedCode_div_h
    (h := h) (s := s) (t := t) tvs hsimple
  simpa [hempty] using hprob

/-- Zero-numerator `EventProbLe` consequence under the stronger whole-DNF row
uniqueness hypothesis. -/
theorem canonicalDepthBad_eventProbLe_zero_of_simple_globalRowUnique_of_h_lt_s_add_t
    {h s t : Nat}
    (tvs : List (List (Fin h × Fin h × Bool)))
    (hsimple : SimpleDNF (phpDNFAsDNF h tvs))
    (huniq : PHPDNFGlobalRowUnique tvs)
    (hfit : h < s + t) :
    EventProbLe (fullMatchingSpace h s) (canonicalDepthBad h tvs t) 0 (h ^ (t / h)) :=
  canonicalDepthBad_eventProbLe_zero_of_simple_globalRowVarUnique_of_h_lt_s_add_t
    tvs hsimple (globalRowVarUnique_of_globalRowUnique huniq) hfit

end PHPFullMatchingRowUniqueStrict
end PvNP
