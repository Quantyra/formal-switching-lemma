import PvNP.FrozenProductScheduleRatio

/-!
# Formula-level family collapse: synthesized start views

Every collapse theorem so far consumed a SUPPLIED `MinimalLayeredFormula`
start view: a hand-built list of `GateSpec`s, each packaging a formula
together with a semantic `DNFView` (DNF, exact semantic equality,
simplicity proof).  This module removes the supplied SEMANTIC ingredient
for the parent-merged embedded-DNF class: from a raw list of simple DNFs
— the only side conditions are decidable syntactic ones (distinct
variables per term, a width bound) — the semantic start view is
CONSTRUCTED (`dnfGate` / `synthGates` / `synthLayer`, with the canonical
`dnfToBD_dnfView` supplying each gate's `eval` equality), and the
universal geometric family theorem then applies to the resulting real
formula `p.merge (Ds.map dnfToBD)` (an `or`/`and` over embedded DNFs).

The headline `formulaFamilyCollapse` therefore quantifies over FORMULAS of
a syntactic class: for every parent kind, every list of `m >= 1` simple
DNFs of width `<= w` (`w >= 1`), every round count `k + 1`, and every
`n >= 2 * (64*m)^k * (64*m*w)`, a `(k+1)`-stage generated refined
certificate exists for the merged formula.  The witness instance exercises
a start DNF of one two-literal term (`witnessDNF`) — realized start
width `2`, above the width-1 realized starts of all prior named witnesses
at the time this module was added.

The coefficient-9 variant `formulaFamilyCollapse_uniform9` repeats the same
synthesized-start-view reduction for the parent-merged embedded-DNF class,
using the existing uniform-9 schedule API.  This is infrastructure only: it
removes a supplied-start-layer obligation within this class, not arbitrary
layered decomposition, not frozen-form B4, not PHP force/switching, and not a
lower-bound or P-vs-NP claim.

## HONEST SCOPE STATEMENT (read this)

* The synthesized class is the PARENT-MERGED EMBEDDED-DNF class: exactly
  the formulas `p.merge (Ds.map dnfToBD)`.  For `and` parents the merged
  syntax tree has THREE alternation levels (and-of-ors-of-ands); bare
  (unwrapped) DNFs and CNF-shaped children are OUTSIDE the class.  These
  formulas present their bottom DNF layer syntactically, so the
  synthesis's content is that the SEMANTIC component of each gate's view
  (the exact `eval` equality) is CONSTRUCTED rather than hypothesized;
  simplicity remains a hypothesis, but a decidable, purely syntactic one
  on the raw DNFs (distinct variables per term), which excludes
  parent-merges of non-simple DNFs from the class.  Arbitrary layered
  decomposition of general bounded-depth formulas (deeper nesting,
  non-DNF-shaped children) is NOT performed; frozen-form B4 in full
  (single upfront depth-`d` view + global `t(d,s)` theorem) remains OPEN.
* "Every stage enters with width budget `>= 1`" is a property of the
  geometric construction (all stage budgets are `2`, so later stages
  enter at `2 - 1 = 1`, and the first stage enters at `w >= 1`); the
  certificate records the budget lists, not entering widths.
* Realized widths of automatically re-viewed gates remain BUDGET claims;
  the statement-vs-witness caveat of `autoIteratedCollapse` applies
  unchanged.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT a PHP switching lemma (Gate A rung 4 remains open), NOT an
  NP/circuit lower bound, NOT a statement about P vs NP.

ELABORATION-SAFETY NOTE (no soundness impact): fully symbolic module; the
only large literal (the witness size `16384`) never occurs inside a
`Nat.choose` evaluation.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaFamilyCollapse

open CNFModel
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

/-! ## Synthesized gates and layers from raw simple DNFs -/

/-- The canonical gate for a simple DNF: the embedded formula together with
its constructed (not supplied) semantic view. -/
def dnfGate {n : Nat} (D : DNF n) (hD : SimpleDNF D) : GateSpec n :=
  GateSpec.dnf (dnfToBD D) (dnfToBD_dnfView D hD)

theorem dnfGate_formula {n : Nat} (D : DNF n) (hD : SimpleDNF D) :
    (dnfGate D hD).formula = dnfToBD D := rfl

theorem dnfGate_theDNF {n : Nat} (D : DNF n) (hD : SimpleDNF D) :
    (dnfGate D hD).theDNF = D := rfl

/-- Synthesize the whole gate list from a raw list of simple DNFs. -/
def synthGates {n : Nat} :
    (Ds : List (DNF n)) → (∀ D ∈ Ds, SimpleDNF D) → List (GateSpec n)
  | [], _ => []
  | D :: rest, h =>
      dnfGate D (h D (List.mem_cons_self D rest)) ::
        synthGates rest (fun D' hD' => h D' (List.mem_cons_of_mem D hD'))

theorem synthGates_length {n : Nat} :
    ∀ (Ds : List (DNF n)) (h : ∀ D ∈ Ds, SimpleDNF D),
      (synthGates Ds h).length = Ds.length
  | [], _ => rfl
  | D :: rest, h => by
      show (synthGates rest
          (fun D' hD' => h D' (List.mem_cons_of_mem D hD'))).length + 1 =
        rest.length + 1
      rw [synthGates_length rest]

theorem synthGates_width {n : Nat} (w : Nat) :
    ∀ (Ds : List (DNF n)) (h : ∀ D ∈ Ds, SimpleDNF D),
      (∀ D ∈ Ds, widthDNF D ≤ w) →
      ∀ g ∈ synthGates Ds h, widthDNF g.theDNF ≤ w
  | [], _, _, _, hg => nomatch hg
  | D :: rest, h, hw, g, hg => by
      rcases List.mem_cons.mp hg with hEq | hMem
      · subst hEq
        exact hw D (List.mem_cons_self D rest)
      · exact synthGates_width w rest
          (fun D' hD' => h D' (List.mem_cons_of_mem D hD'))
          (fun D' hD' => hw D' (List.mem_cons_of_mem D hD')) g hMem

theorem synthGates_formulas {n : Nat} :
    ∀ (Ds : List (DNF n)) (h : ∀ D ∈ Ds, SimpleDNF D),
      (synthGates Ds h).map GateSpec.formula = Ds.map dnfToBD
  | [], _ => rfl
  | D :: rest, h => by
      show GateSpec.formula
          (dnfGate D (h D (List.mem_cons_self D rest))) ::
          (synthGates rest
            (fun D' hD' => h D' (List.mem_cons_of_mem D hD'))).map
            GateSpec.formula =
        dnfToBD D :: rest.map dnfToBD
      rw [synthGates_formulas rest]
      rfl

/-- The synthesized start layer for a parent kind over raw simple DNFs. -/
def synthLayer {n : Nat} (p : ParentKind) (Ds : List (DNF n))
    (h : ∀ D ∈ Ds, SimpleDNF D) : MinimalLayeredFormula n :=
  { parent := p, gates := synthGates Ds h }

/-- The synthesized layer views exactly the merged embedded formula. -/
theorem synthLayer_originalFormula {n : Nat} (p : ParentKind)
    (Ds : List (DNF n)) (h : ∀ D ∈ Ds, SimpleDNF D) :
    (synthLayer p Ds h).originalFormula = p.merge (Ds.map dnfToBD) := by
  show p.merge ((synthGates Ds h).map GateSpec.formula) =
    p.merge (Ds.map dnfToBD)
  rw [synthGates_formulas]

/-! ## The formula-level family theorem -/

open GeneratedRefinedIteratedCertificate in
/-- **Formula-level asymptotic family collapse (synthesized start view).**
For every parent kind `p`, every raw list of `m >= 1` simple DNFs of width
`<= w` (`w >= 1`), every round count `k + 1`, and every
`n >= 2 * (64*m)^k * (64*m*w)`, the real formula `p.merge (Ds.map dnfToBD)`
admits a `(k+1)`-stage generated refined certificate: constant stage gate
count `m` and ALL stage budgets `2` (so every stage enters with width
budget `>= 1` — a construction property following from the budget list
plus `hw1`, not a recorded certificate field); the final conjunct records
that the schedule satisfies the constant tree-budget arithmetic
`t(d,s) = m` (a schedule property carried for interface parity with the
frozen-product bridge).  The start view's SEMANTICS are SYNTHESIZED — no
semantic side condition is taken; the only hypotheses beyond the entry
bound are the decidable syntactic simplicity and width conditions on the
raw DNFs.

This closes the supplied-start-view gap for the parent-merged
embedded-DNF class only (whose bottom DNF layer is already syntactically
present — no layered decomposition is performed); frozen-form B4 in full
remains OPEN.  Realized widths of re-viewed gates remain budget claims,
and the statement-vs-witness caveat of `autoIteratedCollapse` applies
unchanged.  NOT a Frege/PHP bound, NOT a PHP switching lemma, NOT
NP/circuit, NOT P vs NP. -/
theorem formulaFamilyCollapse (k w : Nat) {n : Nat} (p : ParentKind)
    (Ds : List (DNF n)) (hDs : ∀ D ∈ Ds, SimpleDNF D)
    (hm : 1 ≤ Ds.length) (hw1 : 1 ≤ w)
    (hw : ∀ D ∈ Ds, widthDNF D ≤ w)
    (hn : 2 * (64 * Ds.length) ^ k * (64 * Ds.length * w) ≤ n) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (p.merge (Ds.map dnfToBD)) (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) Ds.length ∧
      cert.stageBudgets = List.replicate (k + 1) 2 ∧
      cert.stageStarCounts =
        (geometricSchedule Ds.length (n / (64 * Ds.length * w))
          (k + 1)).map stageStars ∧
      TreeBudgetFrom (fun _ _ => Ds.length) Ds.length (k + 1)
        (geometricSchedule Ds.length (n / (64 * Ds.length * w)) (k + 1)) := by
  have hlen : (synthLayer p Ds hDs).gates.length = Ds.length :=
    synthGates_length Ds hDs
  have hex := geometricFamilyCollapse_universal k w (synthLayer p Ds hDs)
    (by rw [hlen]; exact hm) hw1 (synthGates_width w Ds hDs hw)
    (by rw [hlen]; exact hn)
  rw [hlen, synthLayer_originalFormula] at hex
  exact hex

open GeneratedRefinedIteratedCertificate in
/-- **Coefficient-9 formula-level family collapse (synthesized start view).**
Same parent-merged embedded-DNF class as `formulaFamilyCollapse`, but using
the uniform-9 geometric schedule.  The start layer is synthesized from raw
simple DNFs (`dnfGate`/`synthGates`/`synthLayer`) and the supplied-layer
uniform-9 theorem is then applied to that constructed layer.  Infrastructure
only: not arbitrary layered decomposition, not frozen-form B4, not PHP force
or switching, and not a lower-bound / P-vs-NP claim. -/
theorem formulaFamilyCollapse_uniform9 (k w : Nat) {n : Nat} (p : ParentKind)
    (Ds : List (DNF n)) (hDs : ∀ D ∈ Ds, SimpleDNF D)
    (hm : 1 ≤ Ds.length) (hw1 : 1 ≤ w)
    (hw : ∀ D ∈ Ds, widthDNF D ≤ w)
    (hn : 2 * (9 * Ds.length) ^ k * (9 * Ds.length * w) ≤ n) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (p.merge (Ds.map dnfToBD)) (k + 1),
      cert.stageGateCounts = List.replicate (k + 1) Ds.length ∧
      cert.stageBudgets = List.replicate (k + 1) 2 ∧
      cert.stageStarCounts =
        (geometricSchedule9 Ds.length (n / (9 * Ds.length * w))
          (k + 1)).map stageStars ∧
      TreeBudgetFrom (fun _ _ => Ds.length) Ds.length (k + 1)
        (geometricSchedule9 Ds.length (n / (9 * Ds.length * w)) (k + 1)) := by
  have hlen : (synthLayer p Ds hDs).gates.length = Ds.length :=
    synthGates_length Ds hDs
  have hex := geometricFamilyCollapse_universal9 k w (synthLayer p Ds hDs)
    (by rw [hlen]; exact hm) hw1 (synthGates_width w Ds hDs hw)
    (by rw [hlen]; exact hn)
  rw [hlen, synthLayer_originalFormula] at hex
  exact hex

/-! ## A realized width-2 witness instance -/

def twoLit0 : Literal 16384 := ⟨⟨0, by omega⟩, true⟩
def twoLit1 : Literal 16384 := ⟨⟨1, by omega⟩, true⟩

/-- The witness formula's single DNF: one conjunction of two distinct
literals — realized start width `2`. -/
def witnessDNF : DNF 16384 := [[twoLit0, twoLit1]]

theorem witnessDNFs_simple : ∀ D ∈ [witnessDNF], SimpleDNF D := by
  intro D hD
  simp only [List.mem_singleton] at hD
  subst hD
  intro t ht
  simp only [witnessDNF, List.mem_singleton] at ht
  subst ht
  unfold SimpleTerm
  decide

theorem witnessDNFs_width : ∀ D ∈ [witnessDNF], widthDNF D ≤ 2 := by
  intro D hD
  simp only [List.mem_singleton] at hD
  subst hD
  decide

/-- The witness gate's DNF (a single two-literal term) has realized width
exactly `2`; via `dnfGate_theDNF` the synthesized start gate's switching
DNF therefore has realized width `2` — above the width-1 realized starts
of all prior named witnesses (`familyGate`, `pairGate0/1`,
`seventeenGate`, and the demo/instance literals) at the time this module
was added. -/
theorem witnessDNF_width_realized : widthDNF witnessDNF = 2 := by
  decide

open GeneratedRefinedIteratedCertificate in
/-- The formula-level family instantiated at the exact boundary
`n = 16384 = 2 * 64 * 128` on a start DNF of one realized width-2 term:
two rounds, budgets `[2, 2]`, star counts `[128, 2]` (entering widths
`>= 1` per the geometric construction).  Single finite instance of
`formulaFamilyCollapse`. -/
theorem formulaFamily_widthTwo_twoStage :
    ∃ cert : GeneratedRefinedIteratedCertificate 16384
        (freeRestriction 16384) (BDFormula.or [dnfToBD witnessDNF]) 2,
      cert.stageGateCounts = [1, 1] ∧
      cert.stageBudgets = [2, 2] ∧
      cert.stageStarCounts = [128, 2] ∧
      TreeBudgetFrom (fun _ _ => 1) 1 2 (geometricSchedule 1 128 2) := by
  obtain ⟨cert, hgc, hb, hsc, ht⟩ :=
    formulaFamilyCollapse 1 2 ParentKind.or [witnessDNF] witnessDNFs_simple
      (by decide) (by decide) witnessDNFs_width (by decide)
  refine ⟨cert, ?_, ?_, ?_, ?_⟩
  · rw [hgc]
    rfl
  · rw [hb]
    rfl
  · rw [hsc]
    rfl
  · exact ht

end FormulaFamilyCollapse
end PvNP
