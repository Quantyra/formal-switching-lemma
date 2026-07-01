import PvNP.TraceSearchConnection

/-!
# Family variable-coverage floor for `PHP(h+1, h)`

The parameterized instantiation of the coverage theorem: for every `h > 0` and
every variable `x_{i0,j0}` of the `(h+1) x h` pigeonhole CNF, the clauses
avoiding that variable are simultaneously satisfiable (assign the other `h`
pigeons injectively to the `h` holes), so EVERY bounded-depth refutation trace
of `phpCNF (h+1) h` must perform `litEM` on EVERY one of the `(h+1)*h`
variables — a growing-family, unconditional structural floor on refutation
traces of the local system: query-order length and trace size at least
`(h+1)*h`.

## HONEST SCOPE STATEMENT (read this)

* This is a variable-coverage floor for refutation traces of the LOCAL
  cut-free bounded-depth Tait system, QUADRATIC in `h` because the formula
  itself has `(h+1)*h` variables (it is linear in formula size).  It is NOT
  the classical exponential AC0-Frege/PHP lower bound, NOT a bound for any
  proof system with cut, NOT an NP/circuit lower bound, and NOT a statement
  about P vs NP.
* NON-VACUITY: the refutation-trace types these floors quantify over are
  nonempty for every `h` — see
  `BDTaitCompleteness.phpCNF_family_refutationTrace_nonempty` (completeness
  of the local system + finite pigeonhole, S2068; that module imports this
  one, so the witness lives downstream).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPFamilyCoverage

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor
open BDTraceToSearchExtraction
open BDVariableCoverage
open PHPCNFCoverage
open PHPSearchFloor

/-! ## The removal assignment -/

/-- Hole for pigeon `k` when pigeon `i0` is removed: the `h` remaining pigeons
map injectively onto the `h` holes by rank. -/
def rankHole {h : Nat} (hh : 0 < h) (i0 k : Fin (h + 1)) : Fin h :=
  if hlt : k.val < i0.val then
    ⟨k.val, by have := i0.isLt; omega⟩
  else
    ⟨k.val - 1, by have := k.isLt; omega⟩

theorem rankHole_inj {h : Nat} (hh : 0 < h) (i0 : Fin (h + 1))
    {k1 k2 : Fin (h + 1)} (h1 : k1 ≠ i0) (h2 : k2 ≠ i0)
    (he : rankHole hh i0 k1 = rankHole hh i0 k2) : k1 = k2 := by
  have hne1 : k1.val ≠ i0.val := fun he' => h1 (Fin.ext he')
  have hne2 : k2.val ≠ i0.val := fun he' => h2 (Fin.ext he')
  have hb1 := k1.isLt
  have hb2 := k2.isLt
  have hv : (rankHole hh i0 k1).val = (rankHole hh i0 k2).val :=
    congrArg Fin.val he
  apply Fin.ext
  simp only [rankHole] at hv
  split_ifs at hv <;> simp at hv <;> omega

/-- Witness assignment for the removal of pigeon `i0`'s variables: every other
pigeon sits in its rank hole; everything else is `false`. -/
def removeVarAssignment {h : Nat} (hh : 0 < h) (i0 : Fin (h + 1)) :
    Assignment (Nat.succ ((h + 1) * h)) :=
  fun w => (finList (h + 1)).any (fun k =>
    decide (k ≠ i0) &&
      decide (w = phpVar (h + 1) h k (rankHole hh i0 k)))

theorem removeVarAssignment_eq_true_iff {h : Nat} (hh : 0 < h)
    (i0 : Fin (h + 1)) (w : Fin (Nat.succ ((h + 1) * h))) :
    removeVarAssignment hh i0 w = true ↔
      ∃ k : Fin (h + 1), k ≠ i0 ∧
        w = phpVar (h + 1) h k (rankHole hh i0 k) := by
  rw [removeVarAssignment, List.any_eq_true]
  constructor
  · rintro ⟨k, _, hb⟩
    rcases Bool.and_eq_true _ _ |>.mp hb with ⟨hk, hw⟩
    exact ⟨k, of_decide_eq_true hk, of_decide_eq_true hw⟩
  · rintro ⟨k, hk, hw⟩
    exact ⟨k, mem_finList _ k, by simp [hk, hw]⟩

theorem removeVarAssignment_true {h : Nat} (hh : 0 < h)
    (i0 k : Fin (h + 1)) (hk : k ≠ i0) :
    removeVarAssignment hh i0 (phpVar (h + 1) h k (rankHole hh i0 k)) =
      true :=
  (removeVarAssignment_eq_true_iff hh i0 _).mpr ⟨k, hk, rfl⟩

/-! ## Clause shape decomposition -/

theorem mem_phpCNF {p h : Nat} {c : Clause (Nat.succ (p * h))}
    (hc : c ∈ phpCNF p h) :
    (∃ i : Fin p, c = phpPigeonClause p h i) ∨
      (∃ (i k : Fin p) (j : Fin h),
        i.val < k.val ∧ c = phpCollisionClause p h i k j) := by
  rw [phpCNF] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_map.mp hc with ⟨i, _, he⟩
    exact Or.inl ⟨i, he.symm⟩
  · rcases List.mem_bind.mp hc with ⟨i, _, hc⟩
    rcases List.mem_bind.mp hc with ⟨k, _, hc⟩
    by_cases hik : i.val < k.val
    · rw [if_pos hik] at hc
      rcases List.mem_map.mp hc with ⟨j, _, he⟩
      exact Or.inr ⟨i, k, j, hik, he.symm⟩
    · rw [if_neg hik] at hc
      exact absurd hc (List.not_mem_nil c)

/-! ## The family coverage theorem -/

/-- **Family per-variable coverage.**  For every `h > 0`, every bounded-depth
refutation trace of `phpCNF (h+1) h` performs `litEM` on every variable
`x_{i0,j0}`. -/
theorem phpCNF_family_refutationTrace_queries_var {h : Nat} (hh : 0 < h)
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)])
    (i0 : Fin (h + 1)) (j0 : Fin h) :
    phpVar (h + 1) h i0 j0 ∈ traceQueryOrder π.proof := by
  apply refutationTrace_queries_var
  refine ⟨removeVarAssignment hh i0, ?_⟩
  intro c hc hno
  rcases mem_phpCNF hc with ⟨i, he⟩ | ⟨i, k, j, hik, he⟩
  · subst he
    by_cases hi : i = i0
    · subst hi
      exfalso
      have hmem : mapsLit (h + 1) h i j0 ∈ phpPigeonClause (h + 1) h i :=
        List.mem_map.mpr ⟨j0, mem_finList h j0, rfl⟩
      exact hno _ hmem rfl
    · refine ⟨mapsLit (h + 1) h i (rankHole hh i0 i),
        List.mem_map.mpr ⟨rankHole hh i0 i, mem_finList h _, rfl⟩, ?_⟩
      simpa [mapsLit, litEval] using removeVarAssignment_true hh i0 i hi
  · subst he
    by_cases hti :
        removeVarAssignment hh i0 (phpVar (h + 1) h i j) = true
    · by_cases htk :
          removeVarAssignment hh i0 (phpVar (h + 1) h k j) = true
      · exfalso
        rcases (removeVarAssignment_eq_true_iff hh i0 _).mp hti with
          ⟨k1, hk1, he1⟩
        rcases (removeVarAssignment_eq_true_iff hh i0 _).mp htk with
          ⟨k2, hk2, he2⟩
        obtain ⟨hie, hje⟩ := phpVar_inj he1
        obtain ⟨hke, hje2⟩ := phpVar_inj he2
        have hkk : k1 = k2 :=
          rankHole_inj hh i0 hk1 hk2 (by rw [← hje, ← hje2])
        have : i = k := by rw [hie, hkk, ← hke]
        rw [this] at hik
        exact Nat.lt_irrefl _ hik
      · refine ⟨notMapsLit (h + 1) h k j, by simp [phpCollisionClause], ?_⟩
        have hf : removeVarAssignment hh i0 (phpVar (h + 1) h k j) = false :=
          Bool.eq_false_iff.mpr htk
        simp [notMapsLit, litEval, hf]
    · refine ⟨notMapsLit (h + 1) h i j, by simp [phpCollisionClause], ?_⟩
      have hf : removeVarAssignment hh i0 (phpVar (h + 1) h i j) = false :=
        Bool.eq_false_iff.mpr hti
      simp [notMapsLit, litEval, hf]

/-! ## Family length and size floors -/

/-- All `p*h` PHP variables of the ambient space, as a duplicate-free list. -/
def allPHPVars (p h : Nat) : List (Fin (Nat.succ (p * h))) :=
  (finList (p * h)).map (fun t => ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩)

theorem allPHPVars_length (p h : Nat) : (allPHPVars p h).length = p * h := by
  rw [allPHPVars, List.length_map, finList_length]

theorem allPHPVars_nodup (p h : Nat) : (allPHPVars p h).Nodup := by
  refine List.Nodup.map ?_ (finList_nodup (p * h))
  intro t1 t2 he
  have hv := congrArg (fun x : Fin (Nat.succ (p * h)) => x.val) he
  exact Fin.ext hv

theorem mem_allPHPVars_val_lt {p h : Nat} {w : Fin (Nat.succ (p * h))}
    (hw : w ∈ allPHPVars p h) : w.val < p * h := by
  rcases List.mem_map.mp hw with ⟨t, _, he⟩
  rw [← he]
  exact t.isLt

/-- **Family query-order length floor.**  Every bounded-depth refutation trace
of `phpCNF (h+1) h` has `litEM` query-order length at least `(h+1)*h`.
(Variable-coverage floor for the LOCAL cut-free Tait trace system, linear in
formula size; not a Frege/PHP bound — see the module header.) -/
theorem phpCNF_family_traceQueryOrder_length {h : Nat} (hh : 0 < h)
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    (h + 1) * h ≤ (traceQueryOrder π.proof).length := by
  have hsub : allPHPVars (h + 1) h ⊆ traceQueryOrder π.proof := by
    intro w hw
    have hv : w.val < (h + 1) * h := mem_allPHPVars_val_lt hw
    have := phpCNF_family_refutationTrace_queries_var hh π
      (pigeonOf w hv) (holeOf w hv)
    rwa [phpVar_pigeonOf_holeOf w hv] at this
  have hsubperm := List.Nodup.subperm (allPHPVars_nodup (h + 1) h) hsub
  have := hsubperm.length_le
  rwa [allPHPVars_length] at this

/-- **Family trace-size floor.**  Every bounded-depth refutation trace of
`phpCNF (h+1) h` has size at least `(h+1)*h`: the refutation must genuinely
touch every variable of the growing family.  (Variable-coverage floor for the
LOCAL cut-free Tait trace system, linear in formula size; not a Frege/PHP
proof-size bound — see the module header.) -/
theorem phpCNF_family_traceSize {h : Nat} (hh : 0 < h)
    (π : BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :
    (h + 1) * h ≤ π.size :=
  Nat.le_trans (phpCNF_family_traceQueryOrder_length hh π)
    (traceQueryOrder_length_le_size π.proof)

end PHPFamilyCoverage
end PvNP
