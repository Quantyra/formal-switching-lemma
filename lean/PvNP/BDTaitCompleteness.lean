import PvNP.PHPFamilyCoverage

/-!
# Completeness of the local bounded-depth Tait system for CNF refutations

Every unsatisfiable CNF admits a bounded-depth refutation trace in the local
system (`bdTait_complete`), by the standard cut-free argument: decompose each
negated clause (a conjunction of negated literals) with `andIntro`, and close
every branch with `litEM` on a complementary literal pair, which must exist
because the accumulated literal sequent is valid.

This discharges the M-C1 proof-adversarial review's NON-VACUITY finding: the
coverage floors of `PHPCNFCoverage`/`PHPFamilyCoverage` quantify over
refutation traces of `phpCNF`, and this module proves those types are
NONEMPTY — concretely at `3 x 2` and for the whole `PHP(h+1, h)` family
(unsatisfiability via the finite pigeonhole principle).

## HONEST SCOPE STATEMENT (read this)

* Completeness of the LOCAL cut-free bounded-depth Tait system for CNF
  refutations (analogous to the existing `resolution_complete` for the
  resolution lane).  Completeness alone proves no hardness; this is NOT a
  lower bound, NOT a Frege/PHP result, NOT an NP/circuit bound, and NOT a
  statement about P vs NP.  The constructed refutations are the naive
  full-decomposition ones; no size or depth optimality is stated.
* Nonemptiness results are stated with `Nonempty` (the construction uses
  classical choice to assemble `andIntro` premise functions).

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace BDTaitCompleteness

open CNFModel
open BoundedDepthFrege
open GraphIndexedBridge
open RestrictedPHPFloor
open PHPCNFCoverage

/-! ## Negated literals and cubes -/

/-- Polarity-flipped literal. -/
def negLit {n : Nat} (l : Literal n) : Literal n := ⟨l.var, !l.sign⟩

theorem litEval_negLit {n : Nat} (a : Assignment n) (l : Literal n) :
    litEval a (negLit l) = !(litEval a l) := by
  cases hs : l.sign <;> simp [negLit, litEval, hs]

/-- A cube: the conjunction of a list of literals. -/
def cubeFormula {n : Nat} (c : List (Literal n)) : BDFormula n :=
  BDFormula.and (c.map BDFormula.lit)

/-- Boolean literal-list membership (avoids typeclass-driven `decide`). -/
private def memB {n : Nat} (lits : List (Literal n)) (x : Literal n) : Bool :=
  lits.any (fun l => decide (l = x))

private theorem memB_eq_true_iff {n : Nat} (lits : List (Literal n))
    (x : Literal n) : memB lits x = true ↔ x ∈ lits := by
  rw [memB, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hd⟩
    rw [← of_decide_eq_true hd]
    exact hl
  · intro hx
    exact ⟨x, hx, by simp⟩

/-! ## Core cut-free completeness induction -/

/-- **Cube-sequent completeness.**  If every assignment satisfies some literal
of the context or fully satisfies some cube, the disjunctive sequent of cube
formulas and context literals is derivable.  Induction on the cube list:
`andIntro` moves one cube into per-literal branches; the base case finds a
complementary literal pair (which must exist in a valid pure-literal sequent)
and closes with `litEM`. -/
theorem tait_cubes_complete {n : Nat} (cubes : List (List (Literal n))) :
    ∀ lits : List (Literal n),
      (∀ a : Assignment n,
        (∃ l ∈ lits, litEval a l = true) ∨
          (∃ c ∈ cubes, ∀ l ∈ c, litEval a l = true)) →
      Nonempty (BDProofTrace
        (cubes.map cubeFormula ++ lits.map BDFormula.lit)) := by
  induction cubes with
  | nil =>
      intro lits H
      have hpair : ∃ v : Fin n,
          (⟨v, true⟩ : Literal n) ∈ lits ∧ (⟨v, false⟩ : Literal n) ∈ lits := by
        by_contra hno
        rcases H (fun v => memB lits ⟨v, false⟩) with
          ⟨l, hl, htrue⟩ | ⟨c, hc, _⟩
        · rcases l with ⟨v, s⟩
          cases s with
          | false =>
              have hfalse : memB lits ⟨v, false⟩ = false := by
                simpa [litEval] using htrue
              rw [(memB_eq_true_iff lits _).mpr hl] at hfalse
              exact Bool.noConfusion hfalse
          | true =>
              have hmem : (⟨v, false⟩ : Literal n) ∈ lits :=
                (memB_eq_true_iff lits _).mp (by simpa [litEval] using htrue)
              exact hno ⟨v, hl, hmem⟩
        · exact absurd hc (List.not_mem_nil c)
      obtain ⟨v, hpos, hneg⟩ := hpair
      exact ⟨BDProofTrace.litEM _ v
        (List.mem_map_of_mem BDFormula.lit hpos)
        (List.mem_map_of_mem BDFormula.lit hneg)⟩
  | cons c0 rest ih =>
      intro lits H
      have hbranch : ∀ l ∈ c0,
          Nonempty (BDProofTrace
            (BDFormula.lit l ::
              (rest.map cubeFormula ++ lits.map BDFormula.lit))) := by
        intro l hl
        have H' : ∀ a : Assignment n,
            (∃ l' ∈ (l :: lits), litEval a l' = true) ∨
              (∃ c ∈ rest, ∀ l' ∈ c, litEval a l' = true) := by
          intro a
          rcases H a with ⟨l', hl', ht⟩ | ⟨c, hc, hall⟩
          · exact Or.inl ⟨l', List.mem_cons_of_mem l hl', ht⟩
          · rcases List.mem_cons.mp hc with hc0 | hcr
            · subst hc0
              exact Or.inl ⟨l, List.mem_cons_self l lits, hall l hl⟩
            · exact Or.inr ⟨c, hcr, hall⟩
        obtain ⟨π⟩ := ih (l :: lits) H'
        refine ⟨BDProofTrace.weaken π ?_⟩
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hf))
        · rcases List.mem_cons.mp hf with hf | hf
          · exact hf ▸ List.mem_cons_self _ _
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hf))
      have hbranch' : ∀ f, f ∈ c0.map BDFormula.lit →
          Nonempty (BDProofTrace
            (f :: (rest.map cubeFormula ++ lits.map BDFormula.lit))) := by
        intro f hf
        rcases List.mem_map.mp hf with ⟨l, hlc, hfl⟩
        subst hfl
        exact hbranch l hlc
      exact ⟨BDProofTrace.andIntro
        (fun f hf => Classical.choice (hbranch' f hf))⟩

/-! ## Assembling the refutation -/

/-- The negation of a CNF-as-formula is the disjunction of negated-literal
cubes. -/
theorem neg_cnfToBD_eq {n : Nat} (C : CNF n) :
    neg (cnfToBD C) =
      BDFormula.or (C.map (fun c => cubeFormula (c.map negLit))) := by
  rw [show neg (cnfToBD C)
        = BDFormula.or ((C.map cnfClauseToBD).attach.map (fun f => neg f.1))
      from by rw [cnfToBD, neg]]
  rw [List.attach_map_val (C.map cnfClauseToBD) (fun f => neg f)]
  rw [List.map_map]
  congr 1
  induction C with
  | nil => rfl
  | cons c C ihc =>
      simp only [List.map_cons, ihc]
      congr 1
      show neg (cnfClauseToBD c) = cubeFormula (List.map negLit c)
      rw [show neg (cnfClauseToBD c)
            = BDFormula.and ((c.map cnfLiteralToBD).attach.map (fun f => neg f.1))
          from by rw [cnfClauseToBD, neg]]
      rw [List.attach_map_val (c.map cnfLiteralToBD) (fun f => neg f)]
      simp only [cubeFormula]
      rw [List.map_map, List.map_map]
      congr 1
      induction c with
      | nil => rfl
      | cons l c ihl =>
          simp only [List.map_cons, ihl]
          congr 1
          show neg (cnfLiteralToBD l) = BDFormula.lit (negLit l)
          simp [cnfLiteralToBD, neg, negLit]

/-- **Completeness of the local bounded-depth Tait system.**  Every
unsatisfiable CNF admits a bounded-depth refutation trace.  Completeness alone
proves no hardness. -/
theorem bdTait_complete {n : Nat} (C : CNF n)
    (hunsat : ∀ a : Assignment n, ¬ cnfSat a C) :
    Nonempty (BDRefutationTrace [cnfToBD C]) := by
  have H : ∀ a : Assignment n,
      (∃ l ∈ ([] : List (Literal n)), litEval a l = true) ∨
        (∃ c ∈ C.map (fun c => c.map negLit),
          ∀ l ∈ c, litEval a l = true) := by
    intro a
    right
    have h1 : ¬ ∀ c, c ∈ C → clauseSat a c := hunsat a
    rcases Classical.not_forall.mp h1 with ⟨c, hc⟩
    rcases Classical.not_imp.mp hc with ⟨hcmem, hcunsat⟩
    refine ⟨c.map negLit, List.mem_map_of_mem _ hcmem, ?_⟩
    intro l' hl'
    rcases List.mem_map.mp hl' with ⟨l, hlc, he⟩
    have hfalse : litEval a l = false := by
      by_contra hne
      exact hcunsat ⟨l, hlc, by
        cases hb : litEval a l
        · exact absurd hb hne
        · rfl⟩
    rw [← he, litEval_negLit, hfalse]
    rfl
  obtain ⟨π⟩ := tait_cubes_complete (C.map (fun c => c.map negLit)) [] H
  have π2 := BDProofTrace.orIntro (Γ := []) π
  refine ⟨⟨?_⟩⟩
  show BDProofTrace [neg (cnfToBD C)]
  rw [neg_cnfToBD_eq]
  have hlist : (C.map (fun c => c.map negLit)).map cubeFormula =
      C.map (fun c => cubeFormula (c.map negLit)) := by
    rw [List.map_map]
    rfl
  rw [← hlist]
  exact π2

/-! ## Unsatisfiability of the PHP family (finite pigeonhole) -/

/-- Pigeon clauses live in the PHP CNF. -/
theorem phpPigeonClause_mem (p h : Nat) (i : Fin p) :
    phpPigeonClause p h i ∈ phpCNF p h :=
  List.mem_append.mpr (Or.inl
    (List.mem_map_of_mem _ (PHPSearchFloor.mem_finList p i)))

/-- Ordered collision clauses live in the PHP CNF. -/
theorem phpCollisionClause_mem (p h : Nat) (i k : Fin p) (j : Fin h)
    (hik : i.val < k.val) :
    phpCollisionClause p h i k j ∈ phpCNF p h := by
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_bind.mpr ⟨i, PHPSearchFloor.mem_finList p i, ?_⟩
  refine List.mem_bind.mpr ⟨k, PHPSearchFloor.mem_finList p k, ?_⟩
  rw [if_pos hik]
  exact List.mem_map_of_mem _ (PHPSearchFloor.mem_finList h j)

/-- **Unsatisfiability of `PHP(h+1, h)`** via the finite pigeonhole principle:
a satisfying assignment yields a hole choice for each of the `h+1` pigeons,
two of which must collide. -/
theorem phpCNF_family_unsat (h : Nat) :
    ∀ a : Assignment (Nat.succ ((h + 1) * h)), ¬ cnfSat a (phpCNF (h + 1) h) := by
  intro a hsat
  have hchoice : ∀ i : Fin (h + 1),
      ∃ j : Fin h, a (phpVar (h + 1) h i j) = true := by
    intro i
    rcases hsat _ (phpPigeonClause_mem (h + 1) h i) with ⟨l, hl, htrue⟩
    rcases List.mem_map.mp hl with ⟨j, _, he⟩
    refine ⟨j, ?_⟩
    rw [← he] at htrue
    simpa [mapsLit, litEval] using htrue
  choose f hf using hchoice
  have hcol : ∀ (i k : Fin (h + 1)) (j : Fin h), i.val < k.val →
      a (phpVar (h + 1) h i j) = true →
      a (phpVar (h + 1) h k j) = true → False := by
    intro i k j hik hti htk
    rcases hsat _ (phpCollisionClause_mem (h + 1) h i k j hik) with
      ⟨l, hl, htrue⟩
    rcases List.mem_cons.mp hl with he | hl2
    · rw [he] at htrue
      rw [show litEval a (notMapsLit (h + 1) h i j) =
          !(a (phpVar (h + 1) h i j)) from by simp [notMapsLit, litEval]] at htrue
      rw [hti] at htrue
      exact Bool.noConfusion htrue
    · rcases List.mem_cons.mp hl2 with he | hnil
      · rw [he] at htrue
        rw [show litEval a (notMapsLit (h + 1) h k j) =
            !(a (phpVar (h + 1) h k j)) from by simp [notMapsLit, litEval]] at htrue
        rw [htk] at htrue
        exact Bool.noConfusion htrue
      · exact absurd hnil (List.not_mem_nil l)
  obtain ⟨i, k, hik, hfe⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases Nat.lt_or_ge i.val k.val with hlt | hge
  · exact hcol i k (f i) hlt (hf i) (by rw [hfe]; exact hf k)
  · have hlt : k.val < i.val := by
      rcases Nat.lt_or_ge k.val i.val with h' | h'
      · exact h'
      · exact absurd (Fin.ext (Nat.le_antisymm h' hge)) hik
    exact hcol k i (f k) hlt (hf k) (by rw [← hfe]; exact hf i)

/-! ## Non-vacuity witnesses for the coverage floors -/

/-- **Family non-vacuity.**  For every `h`, the refutation-trace type that the
family coverage floors quantify over is nonempty. -/
theorem phpCNF_family_refutationTrace_nonempty (h : Nat) :
    Nonempty (BDRefutationTrace [cnfToBD (phpCNF (h + 1) h)]) :=
  bdTait_complete _ (phpCNF_family_unsat h)

/-- **Concrete `3 x 2` non-vacuity.**  The refutation-trace type of
`phpCNF 3 2` is nonempty, so the concrete coverage floors of
`PHPCNFCoverage` and the trace-dependent extraction of
`TraceSearchConnection` are about a nonempty type. -/
theorem phpCNF32_refutationTrace_nonempty :
    Nonempty (BDRefutationTrace [cnfToBD (phpCNF 3 2)]) :=
  phpCNF_family_refutationTrace_nonempty 2

end BDTaitCompleteness
end PvNP
