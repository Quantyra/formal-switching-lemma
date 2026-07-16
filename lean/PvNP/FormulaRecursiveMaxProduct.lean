import PvNP.FormulaRecursiveGlobalSchedule

/-!
# Recursive frontier layers with a max-count product bound

`FormulaRecursiveGlobalSchedule` gives every recursive frontier layer a shared
formula-local tree budget, but each layer still consumed a product schedule at
that layer's exact gate count.  This module adds the next narrow Gate B
interface: a product-bound family can be frozen at the formula's maximum
frontier gate count and then reused for any smaller recursive frontier layer.

## HONEST SCOPE STATEMENT (read this)

* This transports supplied product/counting beats from the max frontier count
  down to individual layer counts.  It does not prove the product/counting
  beats themselves.
* The global tree budget remains formula-local, based on
  `recursiveFrontierMaxGateCount F`, and is not an efficient asymptotic
  `t(d,s)` theorem.
* Intermediate frontier layers still use the truth-table/path-DNF fallback
  width budget `n`.  The terminal layer has width budget `1`, but its product
  beats are still supplied at that width.
* This is not full frozen-form B4, not a Gate A/PHP switching lemma, not a
  Frege/PHP lower bound, not an NP/circuit lower bound, and not a statement
  about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveMaxProduct

open BoundedDepthFrege
open BoundedDepthIteratedCollapse
open BoundedDepthLayerView
open BoundedDepthRestriction
open FormulaRecursiveDepth
open FormulaRecursiveGateLayers
open FormulaRecursiveLayerProfile
open FormulaRecursiveGlobalSchedule
open FrozenProductSchedule
open GeneratedGoodRestriction
open GeneratedOneStepDepthReduction
open GeneratedRefinedCollapse
open ScheduledAutoCollapse
open SwitchingLemmaStatement

/-! ## Freezing product bounds at a max gate count -/

/-- Freeze a product-bound family at a chosen gate-count budget. -/
def freezeGateCountBound (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (M : Nat) : Nat -> Nat -> Nat -> Nat -> Nat :=
  fun _m w s depth => B M w s depth

/-- The raw bad-count expression is monotone in the gate count. -/
theorem rawBadCount_le_of_gateCount_le
    {m M p w : Nat} (hm : m <= M) (st : ScheduleStage) :
    rawBadCount m p w st <= rawBadCount M p w st := by
  cases st with
  | mk s ell =>
      simp [rawBadCount]
      exact Nat.mul_le_mul_right
        (Nat.choose p (ell - s) * 2 ^ (p - (ell - s)) * (4 * w) ^ s) hm

/-- A product beat at a max gate count can be reused for any smaller gate
count after freezing the bound family at the max count. -/
theorem productBeat_freezeGateCount_of_le
    {B : Nat -> Nat -> Nat -> Nat -> Nat}
    {m M p w depth : Nat} {st : ScheduleStage}
    (hm : m <= M) (h : ProductBeat B M p w depth st) :
    ProductBeat (freezeGateCountBound B M) m p w depth st := by
  constructor
  · exact Nat.le_trans (rawBadCount_le_of_gateCount_le hm st) h.1
  · simpa [freezeGateCountBound] using h.2

/-- A full product-valid schedule at a max gate count can be reused for any
smaller gate count after freezing the bound family at the max count. -/
theorem productValidFrom_freezeGateCount_of_le
    {B : Nat -> Nat -> Nat -> Nat -> Nat}
    {m M n depth w p : Nat} {sched : List ScheduleStage}
    (hm : m <= M)
    (h : ProductValidFrom B M n depth w p sched) :
    ProductValidFrom (freezeGateCountBound B M) m n depth w p sched := by
  induction sched generalizing depth w p with
  | nil =>
      trivial
  | cons st rest ih =>
      rcases h with ⟨hbase, hambient, hrest⟩
      exact ⟨productBeat_freezeGateCount_of_le hm hbase,
        productBeat_freezeGateCount_of_le hm hambient,
        ih hrest⟩

/-! ## Recursive frontier max-product consumers -/

/-- The product-bound family frozen at a formula's recursive max frontier
gate count. -/
def recursiveFrontierMaxProductBound {n : Nat} (F : BDFormula n)
    (B : Nat -> Nat -> Nat -> Nat -> Nat) :
    Nat -> Nat -> Nat -> Nat -> Nat :=
  freezeGateCountBound B (recursiveFrontierMaxGateCount F)

/-- A max-frontier product schedule gives a product schedule for any in-depth
frontier layer.  Intermediate layers use the shared fallback width `n`. -/
theorem frontierLayer_productValidFrom_of_maxProductBeats {n : Nat}
    (F : BDFormula n) {k : Nat} (hk : k <= depth F)
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hbeats : ProductValidFrom B (recursiveFrontierMaxGateCount F) n
      sched.length n (stars (freeRestriction n)) sched) :
    ProductValidFrom (recursiveFrontierMaxProductBound F B)
      (frontierLayerGateCount F k) n sched.length
      (frontierLayerWidthBudget F k) (stars (freeRestriction n)) sched := by
  have hm := frontierLayerGateCount_le_recursiveFrontierMaxGateCount F hk
  have hbeats' : ProductValidFrom B (recursiveFrontierMaxGateCount F) n
      sched.length (frontierLayerWidthBudget F k)
      (stars (freeRestriction n)) sched := by
    simpa [frontierLayerWidthBudget] using hbeats
  simpa [recursiveFrontierMaxProductBound] using
    productValidFrom_freezeGateCount_of_le
      (B := B) (m := frontierLayerGateCount F k)
      (M := recursiveFrontierMaxGateCount F) hm hbeats'

/-- A max-frontier product schedule at terminal width gives the terminal-layer
product schedule after freezing the bound family at the max count. -/
theorem terminalLayer_productValidFrom_of_maxProductBeats {n : Nat}
    (F : BDFormula n) (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hbeats : ProductValidFrom B (recursiveFrontierMaxGateCount F) n
      sched.length (terminalLayerWidthBudget F)
      (stars (freeRestriction n)) sched) :
    ProductValidFrom (recursiveFrontierMaxProductBound F B)
      (frontierLayerGateCount F (depth F)) n sched.length
      (terminalLayerWidthBudget F) (stars (freeRestriction n)) sched := by
  have hm := frontierLayerGateCount_le_recursiveFrontierMaxGateCount F
    (Nat.le_refl (depth F))
  simpa [recursiveFrontierMaxProductBound] using
    productValidFrom_freezeGateCount_of_le
      (B := B) (m := frontierLayerGateCount F (depth F))
      (M := recursiveFrontierMaxGateCount F) hm hbeats

open GeneratedRefinedIteratedCertificate in
/-- Any in-depth frontier layer can consume one max-frontier product schedule,
with the bound family frozen at the formula's maximum frontier gate count. -/
theorem frontierLayer_autoIteratedCollapse_of_maxProductBeats {n : Nat}
    (F : BDFormula n) (k : Nat) (p : ParentKind)
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hk : k <= depth F)
    (hbeats : ProductValidFrom B (recursiveFrontierMaxGateCount F) n
      sched.length n (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (frontierLayerMinimalLayer F k p).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F k) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F k) sched.length sched := by
  have hlayer := frontierLayer_productValidFrom_of_maxProductBeats
    F hk B sched hbeats
  exact frontierLayer_autoIteratedCollapse_of_globalProductBeats
    F k p (recursiveFrontierMaxProductBound F B) sched hk hlayer

open GeneratedRefinedIteratedCertificate in
/-- Terminal bottom-layer consumer for a max-frontier product schedule supplied
at the terminal width-one budget. -/
theorem terminalLayer_autoIteratedCollapse_of_maxProductBeats {n : Nat}
    (F : BDFormula n) (p : ParentKind)
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hbeats : ProductValidFrom B (recursiveFrontierMaxGateCount F) n
      sched.length (terminalLayerWidthBudget F)
      (stars (freeRestriction n)) sched) :
    exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
        (terminalLayerMinimalLayer F p).originalFormula sched.length,
      cert.stageGateCounts =
        List.replicate sched.length (frontierLayerGateCount F (depth F)) /\
      cert.stageBudgets = sched.map stageS /\
      cert.stageStarCounts = sched.map stageStars /\
      TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
        (frontierLayerGateCount F (depth F)) sched.length sched := by
  have hterminal := terminalLayer_productValidFrom_of_maxProductBeats
    F B sched hbeats
  exact terminalLayer_autoIteratedCollapse_of_globalProductBeats
    F p (recursiveFrontierMaxProductBound F B) sched hterminal

open GeneratedRefinedIteratedCertificate in
/-- Uniform frontier form: one max-frontier product schedule covers every
recursive frontier layer up to `depth F`. -/
theorem allFrontierLayers_autoIteratedCollapse_of_maxProductBeats {n : Nat}
    (F : BDFormula n) (p : ParentKind)
    (B : Nat -> Nat -> Nat -> Nat -> Nat)
    (sched : List ScheduleStage)
    (hbeats : ProductValidFrom B (recursiveFrontierMaxGateCount F) n
      sched.length n (stars (freeRestriction n)) sched) :
    forall k, k <= depth F ->
      exists cert : GeneratedRefinedIteratedCertificate n (freeRestriction n)
          (frontierLayerMinimalLayer F k p).originalFormula sched.length,
        cert.stageGateCounts =
          List.replicate sched.length (frontierLayerGateCount F k) /\
        cert.stageBudgets = sched.map stageS /\
        cert.stageStarCounts = sched.map stageStars /\
        TreeBudgetFrom (recursiveFrontierGlobalTreeBudget F)
          (frontierLayerGateCount F k) sched.length sched := by
  intro k hk
  exact frontierLayer_autoIteratedCollapse_of_maxProductBeats
    F k p B sched hk hbeats

end FormulaRecursiveMaxProduct
end PvNP
