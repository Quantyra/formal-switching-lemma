import PvNP.TreePathViews
import PvNP.GeneratedRefinedCollapse

/-!
# Automatic next-layer scaffold from generated tree re-viewing

With the general tree-to-DNF/CNF re-viewing declarations from
`TreePathViews`, the next stage's layered view of a generated rewritten formula
can be built automatically from one generated one-step certificate:

* `nextLayer C` re-views every generated stage tree as a DNF gate; its
  `originalFormula` equals the certificate's rewritten formula
  (`nextLayer_originalFormula`), its gate count is preserved
  (`nextLayer_gateCount`), and its gates have width `≤ s - 1`
  (`nextLayer_width`).

The imported `TreePathViews` module also supplies the general DNF and CNF
tree-path re-view declarations.  This module does NOT implement or claim a
three-stage/nonempty-gate theorem.

## HONEST SCOPE STATEMENT (read this)

* Representation/next-layer scaffolding only: this module does not prove a
  concrete finite plan or concrete counting parameters.  Any future plan still
  needs supplied/proved per-stage counting beats and generated restrictions from
  the existing refined collapse machinery.
* The realized widths of auto re-viewed gates depend on the generated trees
  (they may be constants); width BUDGETS are `s - 1` per stage and every beat
  carries the non-degenerate `(8w)^s` factor.
* Frozen-form B4 (single upfront depth-`d` view, product hypothesis
  `B(m, w, s, d)`, `t(d, s)` tree bound) remains OPEN: the plan/beat data are
  still per-stage, not a single product hypothesis.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.
  Gate A rung 4 remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace AutoReviewedIteration

set_option maxRecDepth 8192
set_option exponentiation.threshold 20000

attribute [local irreducible] SwitchingLemmaStatement.restrictionsWithStars
attribute [local irreducible] RefinedSubspace.refinesSubspace
attribute [local irreducible] SwitchingLemmaStatement.stars

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open RestrictionComposition
open RefinedSubspace
open GeneratedOneStepDepthReduction
open GeneratedIteratedCollapseFinal
open GeneratedRefinedCollapse
open TreePathViews

/-! ## The automatic next-stage layer -/

/-- Re-view every generated stage tree as a DNF gate under the same parent. -/
noncomputable def nextLayer {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) : MinimalLayeredFormula n where
  parent := I.layer.parent
  gates := I.layer.gates.attach.map (fun g =>
    GateSpec.dnf (treeToFormula (C.treeOf g.1 g.2))
      (treeDNFView (C.treeOf g.1 g.2)))

theorem nextLayer_originalFormula {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    (nextLayer C).originalFormula = C.reducedFormula := by
  show I.layer.parent.merge
      ((I.layer.gates.attach.map (fun g =>
        GateSpec.dnf (treeToFormula (C.treeOf g.1 g.2))
          (treeDNFView (C.treeOf g.1 g.2)))).map GateSpec.formula)
    = I.layer.parent.merge (I.layer.gates.attach.map (fun g =>
        treeToFormula (C.treeOf g.1 g.2)))
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro g _
  rfl

theorem nextLayer_gateCount {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    (nextLayer C).gates.length = I.layer.gates.length := by
  simp [nextLayer]

theorem nextLayer_width {n : Nat} {I : GeneratedOneStepInput n}
    (C : GeneratedOneStepCertificate I) :
    ∀ g ∈ (nextLayer C).gates, widthDNF g.theDNF ≤ I.s - 1 := by
  intro g hg
  rw [show (nextLayer C).gates = I.layer.gates.attach.map (fun g =>
      GateSpec.dnf (treeToFormula (C.treeOf g.1 g.2))
        (treeDNFView (C.treeOf g.1 g.2))) from rfl] at hg
  rw [List.mem_map] at hg
  obtain ⟨g₀, _, rfl⟩ := hg
  show widthDNF (treeDNFView (C.treeOf g₀.1 g₀.2)).D ≤ I.s - 1
  have hd := C.treeDepth g₀.1 g₀.2
  have hw := widthDNF_treeDNFView_le (C.treeOf g₀.1 g₀.2)
  omega

end AutoReviewedIteration
end PvNP
