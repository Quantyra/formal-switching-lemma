import PvNP.FormulaFamilyCollapse

/-!
# Mixed formula-level family collapse: the full GateSpec surface from raw syntax

`FormulaFamilyCollapse` synthesized start views for DNF-shaped children
only, although the bottom-layer gate type `GateSpec` has TWO constructors:
`GateSpec.dnf` (a formula with a semantic DNF view) and `GateSpec.cnf`
(a formula with a semantic CNF view, switched through its dual DNF).
This module completes the synthesis surface:

* `clauseToBD` / `cnfChildToBD` embed a raw CNF (a conjunction of literal
  clauses) as a real `and`-of-`or`s formula with exact semantics
  (`eval_cnfChildToBD`), giving the canonical constructed `CNFView`
  (`cnfChildToBD_cnfView`) — the CNF-side counterpart of
  `dnfToBD_dnfView`.
* `widthDNF_cnfDualDNF`: literal negation preserves clause lengths, so
  the dual-DNF switching width of a CNF child EQUALS the raw list's
  `widthDNF`.  Consequently BOTH child kinds take the SAME uniform
  decidable syntactic hypotheses on their raw list of literal lists
  (`Clause = Term` and `SimpleClause = SimpleTerm` definitionally):
  per-list distinct variables, and `widthDNF` bounded by `w`.
* `RawGate` (`.dnf D` / `.cnf C`) tags a raw child; `toGate` synthesizes
  the matching `GateSpec` constructor with its semantic view CONSTRUCTED
  (`dnfToBD_dnfView` / `cnfChildToBD_cnfView`); `mixedSynthGates` /
  `mixedSynthLayer` assemble the layer.
* Headline `mixedFormulaFamilyCollapse`: the formula-level asymptotic
  family now covers parent-merges of ARBITRARY MIXTURES of embedded DNF
  and CNF children — the full bottom-layer `GateSpec` surface is reachable
  from raw syntax.  `cnfFormulaFamilyCollapse` is the all-CNF-children
  corollary.  The witness exercises a genuinely conjunctive CNF child
  (two clauses) next to a DNF child at the exact boundary `n = 32768`.

## HONEST SCOPE STATEMENT (read this)

* The synthesized class is the PARENT-MERGED EMBEDDED-CHILD class:
  exactly the formulas `p.merge (gs.map RawGate.toBD)` where every child
  is an embedded simple DNF (`or`-of-`and`s) or embedded simple CNF
  (`and`-of-`or`s).  Merged syntax trees have up to three alternation
  levels; bare (unwrapped) DNFs/CNFs and children of any other shape are
  OUTSIDE the class.  The SEMANTIC component of each gate's view (exact
  `eval` equality) is CONSTRUCTED; simplicity remains a hypothesis, but a
  decidable, purely syntactic one on the raw lists (distinct variables
  per clause/term).
* This completes the BOTTOM-LAYER synthesis surface only.  Arbitrary
  layered decomposition of general bounded-depth formulas — depth-`d`
  upfront views for deeper nesting, with a global `t(d,s)` theorem —
  is NOT performed; frozen-form B4 in full remains OPEN.
* "Every stage enters with width budget `>= 1`" is a property of the
  geometric construction (all stage budgets are `2`; the first stage
  enters at `w >= 1`); the certificate records budget lists, not
  entering widths.  Realized widths of automatically re-viewed gates
  remain BUDGET claims; the statement-vs-witness caveat of
  `autoIteratedCollapse` applies unchanged.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma (Gate A rung 4 remains open), NOT an
  NP/circuit lower bound, NOT a statement about P vs NP.

ELABORATION-SAFETY NOTE (no soundness impact): fully symbolic module; the
only large literal (the witness size `32768`) never occurs inside a
`Nat.choose` evaluation.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace MixedFormulaFamilyCollapse

open CNFModel hiding Clause CNF
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open BoundedDepthFregeSwitchingBridge
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open RestrictionComposition
open RefinedSubspace
open GeneratedOneStepDepthReduction
open GeneratedIteratedCollapseFinal
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open FrozenProductSchedule
open FrozenProductScheduleRatio

/-! ## The CNF-child embedding and its canonical constructed view -/

/-- Embed a clause (a disjunction of literals) as a real `or` formula. -/
def clauseToBD {n : Nat} (c : Clause n) : BDFormula n :=
  BDFormula.or (c.map BDFormula.lit)

/-- The clause embedding has exactly the real clause semantics. -/
theorem eval_clauseToBD {n : Nat} (a : Assignment n) (c : Clause n) :
    eval a (clauseToBD c) = clauseEval a c := by
  unfold clauseToBD clauseEval
  rw [eval_or]
  induction c with
  | nil => rfl
  | cons l c ih => simp [eval_lit, ih]

/-- Embed a raw CNF as a real `and`-of-`or`s formula. -/
def cnfChildToBD {n : Nat} (C : CNF n) : BDFormula n :=
  BDFormula.and (C.map clauseToBD)

/-- The CNF embedding has exactly the real CNF semantics. -/
theorem eval_cnfChildToBD {n : Nat} (a : Assignment n) (C : CNF n) :
    eval a (cnfChildToBD C) = cnfEval a C := by
  unfold cnfChildToBD cnfEval
  rw [eval_and]
  induction C with
  | nil => rfl
  | cons c C ih => simp [eval_clauseToBD, ih]

/-- The canonical CONSTRUCTED CNF view of an embedded simple CNF — the
CNF-side counterpart of `dnfToBD_dnfView`. -/
def cnfChildToBD_cnfView {n : Nat} (C : CNF n) (hC : SimpleCNF C) :
    CNFView (cnfChildToBD C) where
  C := C
  sem_eq := fun a => eval_cnfChildToBD a C
  simple := hC

/-- Literal negation preserves clause lengths, so the dual-DNF switching
width of a CNF child equals the raw list's `widthDNF`. -/
theorem widthDNF_cnfDualDNF {n : Nat} (C : CNF n) :
    widthDNF (cnfDualDNF C) = widthDNF C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
      show max (termWidth (clauseDualTerm c)) (widthDNF (cnfDualDNF C)) =
        max (termWidth c) (widthDNF C)
      rw [ih, show termWidth (clauseDualTerm c) = termWidth c from
        List.length_map c negLit]

/-! ## Raw mixed children -/

/-- A raw bottom-layer child: a DNF-shaped or CNF-shaped list of literal
lists.  `Clause = Term` definitionally, so both kinds carry the SAME raw
data shape and the same uniform syntactic hypotheses below. -/
inductive RawGate (n : Nat) where
  | dnf (D : DNF n)
  | cnf (C : CNF n)

namespace RawGate

/-- The underlying raw list of literal lists. -/
def raw {n : Nat} : RawGate n → List (List (Literal n))
  | .dnf D => D
  | .cnf C => C

/-- The real bounded-depth formula of the child. -/
def toBD {n : Nat} : RawGate n → BDFormula n
  | .dnf D => dnfToBD D
  | .cnf C => cnfChildToBD C

/-- Uniform decidable syntactic simplicity of the raw list — exactly what
both view kinds need (`SimpleClause = SimpleTerm` definitionally). -/
abbrev Simple {n : Nat} (g : RawGate n) : Prop := SimpleDNF g.raw

/-- Synthesize the matching `GateSpec` constructor, with the semantic view
CONSTRUCTED in both cases. -/
def toGate {n : Nat} : (g : RawGate n) → Simple g → GateSpec n
  | .dnf D, h => GateSpec.dnf (dnfToBD D) (dnfToBD_dnfView D h)
  | .cnf C, h => GateSpec.cnf (cnfChildToBD C) (cnfChildToBD_cnfView C h)

theorem toGate_formula {n : Nat} (g : RawGate n) (h : Simple g) :
    (toGate g h).formula = g.toBD := by
  cases g <;> rfl

/-- The synthesized gate's switching DNF obeys the raw list's width bound
(for CNF children via `widthDNF_cnfDualDNF`). -/
theorem toGate_width {n : Nat} {w : Nat} (g : RawGate n) (h : Simple g)
    (hw : widthDNF g.raw ≤ w) : widthDNF (toGate g h).theDNF ≤ w := by
  cases g with
  | dnf D => exact hw
  | cnf C =>
      show widthDNF (cnfDualDNF C) ≤ w
      rw [widthDNF_cnfDualDNF]
      exact hw

end RawGate

/-! ## Synthesized mixed layers -/

/-- Synthesize the whole gate list from raw tagged children. -/
def mixedSynthGates {n : Nat} :
    (gs : List (RawGate n)) → (∀ g ∈ gs, RawGate.Simple g) →
      List (GateSpec n)
  | [], _ => []
  | g :: rest, h =>
      RawGate.toGate g (h g (List.mem_cons_self g rest)) ::
        mixedSynthGates rest (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))

theorem mixedSynthGates_length {n : Nat} :
    ∀ (gs : List (RawGate n)) (h : ∀ g ∈ gs, RawGate.Simple g),
      (mixedSynthGates gs h).length = gs.length
  | [], _ => rfl
  | g :: rest, h => by
      show (mixedSynthGates rest
          (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))).length + 1 =
        rest.length + 1
      rw [mixedSynthGates_length rest]

theorem mixedSynthGates_width {n : Nat} (w : Nat) :
    ∀ (gs : List (RawGate n)) (h : ∀ g ∈ gs, RawGate.Simple g),
      (∀ g ∈ gs, widthDNF g.raw ≤ w) →
      ∀ gg ∈ mixedSynthGates gs h, widthDNF gg.theDNF ≤ w
  | [], _, _, _, hgg => nomatch hgg
  | g :: rest, h, hw, gg, hgg => by
      rcases List.mem_cons.mp hgg with hEq | hMem
      · subst hEq
        exact RawGate.toGate_width g (h g (List.mem_cons_self g rest))
          (hw g (List.mem_cons_self g rest))
      · exact mixedSynthGates_width w rest
          (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
          (fun g' hg' => hw g' (List.mem_cons_of_mem g hg')) gg hMem

theorem mixedSynthGates_formulas {n : Nat} :
    ∀ (gs : List (RawGate n)) (h : ∀ g ∈ gs, RawGate.Simple g),
      (mixedSynthGates gs h).map GateSpec.formula = gs.map RawGate.toBD
  | [], _ => rfl
  | g :: rest, h => by
      show GateSpec.formula
          (RawGate.toGate g (h g (List.mem_cons_self g rest))) ::
          (mixedSynthGates rest
            (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))).map
            GateSpec.formula =
        RawGate.toBD g :: rest.map RawGate.toBD
      rw [mixedSynthGates_formulas rest,
        RawGate.toGate_formula g (h g (List.mem_cons_self g rest))]

/-- The synthesized mixed start layer. -/
def mixedSynthLayer {n : Nat} (p : ParentKind) (gs : List (RawGate n))
    (h : ∀ g ∈ gs, RawGate.Simple g) : MinimalLayeredFormula n :=
  { parent := p, gates := mixedSynthGates gs h }

/-- The synthesized mixed layer views exactly the merged embedded formula. -/
theorem mixedSynthLayer_originalFormula {n : Nat} (p : ParentKind)
    (gs : List (RawGate n)) (h : ∀ g ∈ gs, RawGate.Simple g) :
    (mixedSynthLayer p gs h).originalFormula =
      p.merge (gs.map RawGate.toBD) := by
  show p.merge ((mixedSynthGates gs h).map GateSpec.formula) =
    p.merge (gs.map RawGate.toBD)
  rw [mixedSynthGates_formulas]

/-! ## The mixed formula-level family theorem -/

open GeneratedRefinedIteratedCertificate in
/-- **Mixed formula-level asymptotic family collapse (full `GateSpec`
surface from raw syntax).**  For every parent kind `p`, every raw list of
`m >= 1` tagged children (each an embedded simple DNF or embedded simple
CNF, with the SAME uniform decidable syntactic hypotheses: distinct
variables per clause/term and raw `widthDNF <= w`, `w >= 1`), every round
count `k + 1`, and every `n >= 2 * (64*m)^k * (64*m*w)`, the real formula
`p.merge (gs.map RawGate.toBD)` admits a `(k+1)`-stage generated refined
certificate: constant stage gate count `m` and ALL stage budgets `2` (so
every stage enters with width budget `>= 1` — a construction property
following from the budget list plus `hw1`, not a recorded certificate
field); the final conjunct records that the schedule satisfies the
constant tree-budget arithmetic `t(d,s) = m` (a schedule property carried
for interface parity with the frozen-product bridge).

This completes the bottom-layer synthesis surface (`GateSpec.dnf` AND
`GateSpec.cnf` children from raw syntax) for the parent-merged
embedded-child class only; frozen-form B4 in full (depth-`d`
decomposition + global `t(d,s)` theorem) remains OPEN.  Realized widths
of re-viewed gates remain budget claims, and the statement-vs-witness
caveat of `autoIteratedCollapse` applies unchanged.  NOT a Frege/PHP
bound, NOT a PHP switching lemma, NOT NP/circuit, NOT P vs NP. -/
theorem mixedFormulaFamilyCollapse (k w : Nat) {n : Nat} (p : ParentKind)
    (gs : List (RawGate n)) (hgs : ∀ g ∈ gs, RawGate.Simple g)
    (hm : 1 ≤ gs.length) (hw1 : 1 ≤ w)
    (hw : ∀ g ∈ gs, widthDNF g.raw ≤ w)
    (hn : 2 * (64 * gs.length) ^ k * (64 * gs.length * w) ≤ n) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (p.merge (gs.map RawGate.toBD)) (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) gs.length ∧
      cert.stageBudgets = List.replicate (k + 1) 2 ∧
      cert.stageStarCounts =
        (geometricSchedule gs.length (n / (64 * gs.length * w))
          (k + 1)).map stageStars ∧
      TreeBudgetFrom (fun _ _ => gs.length) gs.length (k + 1)
        (geometricSchedule gs.length (n / (64 * gs.length * w)) (k + 1)) := by
  have hlen : (mixedSynthLayer p gs hgs).gates.length = gs.length :=
    mixedSynthGates_length gs hgs
  have hex := geometricFamilyCollapse_universal k w (mixedSynthLayer p gs hgs)
    (by rw [hlen]; exact hm) hw1 (mixedSynthGates_width w gs hgs hw)
    (by rw [hlen]; exact hn)
  rw [hlen, mixedSynthLayer_originalFormula] at hex
  exact hex

/-! ## The all-CNF-children corollary (rung: CNF-child synthesis) -/

private theorem map_toBD_cnf {n : Nat} :
    ∀ Cs : List (CNF n),
      (Cs.map RawGate.cnf).map RawGate.toBD = Cs.map cnfChildToBD
  | [] => rfl
  | C :: Cs => by
      show cnfChildToBD C :: (Cs.map RawGate.cnf).map RawGate.toBD =
        cnfChildToBD C :: Cs.map cnfChildToBD
      rw [map_toBD_cnf Cs]

open GeneratedRefinedIteratedCertificate in
/-- **All-CNF-children formula family.**  The mixed theorem restricted to
CNF children only: every raw list of `m >= 1` simple CNFs with clause
width `<= w` yields the family certificate for the real
`p.merge (Cs.map cnfChildToBD)` formula.  Same scope and caveats as
`mixedFormulaFamilyCollapse`. -/
theorem cnfFormulaFamilyCollapse (k w : Nat) {n : Nat} (p : ParentKind)
    (Cs : List (CNF n)) (hCs : ∀ C ∈ Cs, SimpleCNF C)
    (hm : 1 ≤ Cs.length) (hw1 : 1 ≤ w)
    (hw : ∀ C ∈ Cs, widthDNF C ≤ w)
    (hn : 2 * (64 * Cs.length) ^ k * (64 * Cs.length * w) ≤ n) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (p.merge (Cs.map cnfChildToBD)) (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) Cs.length ∧
      cert.stageBudgets = List.replicate (k + 1) 2 ∧
      cert.stageStarCounts =
        (geometricSchedule Cs.length (n / (64 * Cs.length * w))
          (k + 1)).map stageStars ∧
      TreeBudgetFrom (fun _ _ => Cs.length) Cs.length (k + 1)
        (geometricSchedule Cs.length (n / (64 * Cs.length * w)) (k + 1)) := by
  have hlen : (Cs.map RawGate.cnf).length = Cs.length :=
    List.length_map Cs RawGate.cnf
  have hex := mixedFormulaFamilyCollapse k w p (Cs.map RawGate.cnf)
    (by
      intro g hg
      rcases List.mem_map.mp hg with ⟨C, hC, rfl⟩
      exact hCs C hC)
    (by rw [hlen]; exact hm) hw1
    (by
      intro g hg
      rcases List.mem_map.mp hg with ⟨C, hC, rfl⟩
      exact hw C hC)
    (by rw [hlen]; exact hn)
  rw [hlen, map_toBD_cnf] at hex
  exact hex

/-! ## A mixed witness with a genuinely conjunctive CNF child -/

def mixLit0 : Literal 32768 := ⟨⟨0, by omega⟩, true⟩
def mixLit1 : Literal 32768 := ⟨⟨1, by omega⟩, true⟩
def mixLit2 : Literal 32768 := ⟨⟨2, by omega⟩, true⟩

/-- The witness DNF child: one single-literal term. -/
def mixD : DNF 32768 := [[mixLit0]]

/-- The witness CNF child: TWO single-literal clauses — a genuinely
conjunctive `and`-of-`or`s child. -/
def mixC : CNF 32768 := [[mixLit1], [mixLit2]]

/-- The mixed raw children list: one DNF child and one CNF child. -/
def mixChildren : List (RawGate 32768) :=
  [RawGate.dnf mixD, RawGate.cnf mixC]

theorem mixChildren_simple : ∀ g ∈ mixChildren, RawGate.Simple g := by
  intro g hg
  rcases List.mem_cons.mp hg with hEq | hMem
  · subst hEq
    intro t ht
    simp only [RawGate.raw, mixD, List.mem_singleton] at ht
    subst ht
    unfold SimpleTerm
    decide
  · rcases List.mem_cons.mp hMem with hEq | hNil
    · subst hEq
      intro t ht
      rcases List.mem_cons.mp ht with h1 | h2
      · subst h1
        unfold SimpleTerm
        decide
      · have h3 := List.mem_singleton.mp h2
        subst h3
        unfold SimpleTerm
        decide
    · exact absurd hNil (List.not_mem_nil g)

theorem mixChildren_width : ∀ g ∈ mixChildren, widthDNF g.raw ≤ 1 := by
  intro g hg
  rcases List.mem_cons.mp hg with hEq | hMem
  · subst hEq
    decide
  · rcases List.mem_cons.mp hMem with hEq | hNil
    · subst hEq
      decide
    · exact absurd hNil (List.not_mem_nil g)

open GeneratedRefinedIteratedCertificate in
/-- The mixed family instantiated at the exact boundary
`n = 32768 = 2 * 128 * 128` on one DNF child and one genuinely
conjunctive two-clause CNF child: two rounds, gate counts `[2, 2]`,
budgets `[2, 2]`, star counts `[256, 2]` (entering widths `>= 1` per the
geometric construction).  Single finite instance of
`mixedFormulaFamilyCollapse` exercising BOTH `GateSpec` constructors. -/
theorem mixedFamily_dnfCnf_twoStage :
    ∃ cert : GeneratedRefinedIteratedCertificate 32768
        (freeRestriction 32768)
        (BDFormula.or [dnfToBD mixD, cnfChildToBD mixC]) 2,
      cert.stageGateCounts = [2, 2] ∧
      cert.stageBudgets = [2, 2] ∧
      cert.stageStarCounts = [256, 2] ∧
      TreeBudgetFrom (fun _ _ => 2) 2 2 (geometricSchedule 2 256 2) := by
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    mixedFormulaFamilyCollapse 1 1 ParentKind.or mixChildren
      mixChildren_simple (by decide) (by decide) mixChildren_width
      (by decide)
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc]
    rfl
  · rw [hb]
    rfl
  · rw [hsc]
    rfl
  · exact ht

end MixedFormulaFamilyCollapse
end PvNP
