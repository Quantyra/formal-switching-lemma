import PvNP.BoundedDepthLayerView

/-!
# Two-layer explicit-view bounded-depth collapse schedules

P-vs-NP-relevant proof-complexity progress under the repository's claims
boundary: this module advances the one-step DNF-view collapse infrastructure to a
two-layer explicit-view/schedule collapse certificate.  It records only named
bottom-layer views, concrete restrictions, semantic compatibility, and explicit
decision-tree witnesses for two stages.  It is **not** an arbitrary AC0 collapse,
not a Frege/PHP lower bound, and not a `P ≠ NP` or NP lower-bound claim.
-/

namespace PvNP
namespace BoundedDepthIteratedCollapse

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthLayerView
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open SwitchingEncodeConstruct

/-! ## Alternating bottom-layer views -/

/-- A clause is a disjunction of literals. -/
abbrev Clause (n : Nat) := List (Literal n)

/-- A CNF is a conjunction of clauses. -/
abbrev CNF (n : Nat) := List (Clause n)

/-- A simple CNF clause mentions each variable at most once. -/
def SimpleClause {n : Nat} (c : Clause n) : Prop := (c.map (·.var)).Nodup

/-- A simple CNF has only simple clauses. -/
def SimpleCNF {n : Nat} (C : CNF n) : Prop := ∀ c ∈ C, SimpleClause c

/-- Real semantics of a CNF clause. -/
def clauseEval {n : Nat} (a : Assignment n) (c : Clause n) : Bool :=
  c.any (fun l => litEval a l)

/-- Real semantics of a CNF. -/
def cnfEval {n : Nat} (a : Assignment n) (C : CNF n) : Bool :=
  C.all (fun c => clauseEval a c)

@[simp] theorem clauseEval_nil {n : Nat} (a : Assignment n) :
    clauseEval a ([] : Clause n) = false := rfl

@[simp] theorem cnfEval_nil {n : Nat} (a : Assignment n) :
    cnfEval a ([] : CNF n) = true := rfl

/-- A semantic bottom-layer CNF view of a real bounded-depth formula.  This is a
dual view record only; no CNF switching lemma is asserted here. -/
structure CNFView {n : Nat} (F : BDFormula n) where
  C : CNF n
  sem_eq : ∀ a : Assignment n, eval a F = cnfEval a C
  simple : SimpleCNF C

/-- The trivially true formula has the empty-CNF view. -/
def emptyCNFView (n : Nat) : CNFView (BDFormula.tru : BDFormula n) where
  C := []
  sem_eq := fun a => by simp [eval_tru, cnfEval]
  simple := by intro c hc; cases hc

/-! ## Explicit two-stage schedules and certificates -/

/-- A named first-stage DNF switching premise with its concrete restriction and
decision-tree witness.  The witness can be obtained from
`bdFormula_dnfView_switching_collapse` for good restrictions, but this record is
kept as explicit stage data for composition. -/
structure DNFLayerCollapsePremise {n : Nat} (F : BDFormula n) where
  view : DNFView F
  ρ : Restriction n
  T : DTree n
  depthBound : Nat
  depth_lt : dtDepth T < depthBound
  computes : ∀ a : Assignment n, Agree ρ a → dtEval a T = eval a (restrict ρ F)

/-- A named second-stage CNF collapse premise.  Since this file does not prove a
CNF switching lemma, the CNF-side collapse is an explicit schedule/premise record,
not a theorem about arbitrary CNFs. -/
structure CNFLayerCollapsePremise {n : Nat} (F : BDFormula n) where
  view : CNFView F
  ρ : Restriction n
  T : DTree n
  depthBound : Nat
  depth_lt : dtDepth T < depthBound
  computes : ∀ a : Assignment n, Agree ρ a → dtEval a T = eval a (restrict ρ F)

/-- The explicit two-layer schedule: first a DNF-view layer, then a CNF-view
layer, together with a compatibility field saying that the two restrictions are
used only on common extensions. -/
structure TwoLayerSchedule {n : Nat} (F₁ F₂ : BDFormula n) where
  dnfStage : DNFLayerCollapsePremise F₁
  cnfStage : CNFLayerCollapsePremise F₂
  compatible : ∃ a : Assignment n, Agree dnfStage.ρ a ∧ Agree cnfStage.ρ a

/-- A clean two-layer collapse certificate for the conjunction of the two viewed
layers under the two restrictions.  It deliberately stores the two stage trees
rather than claiming a general tree-grafting construction for all AC0 formulas. -/
structure TwoLayerCollapseCertificate {n : Nat} (F₁ F₂ : BDFormula n) where
  ρ₁ : Restriction n
  ρ₂ : Restriction n
  T₁ : DTree n
  T₂ : DTree n
  bound₁ : Nat
  bound₂ : Nat
  depth₁_lt : dtDepth T₁ < bound₁
  depth₂_lt : dtDepth T₂ < bound₂
  compatible : ∃ a : Assignment n, Agree ρ₁ a ∧ Agree ρ₂ a
  computes : ∀ a : Assignment n, Agree ρ₁ a → Agree ρ₂ a →
    (dtEval a T₁ && dtEval a T₂) =
      eval a (restrict ρ₂ (restrict ρ₁ (BDFormula.and [F₁, F₂])))

/-- Composition theorem for two explicit bottom layers.  If the first DNF-view
layer and the second CNF-view layer each come with a restriction-compatible
decision-tree witness, then their conjunction has a two-stage collapse
certificate under the iterated restrictions. -/
def twoLayerCollapse_from_stagePremises {n : Nat} {F₁ F₂ : BDFormula n}
    (S : TwoLayerSchedule F₁ F₂) :
    TwoLayerCollapseCertificate F₁ F₂ where
  ρ₁ := S.dnfStage.ρ
  ρ₂ := S.cnfStage.ρ
  T₁ := S.dnfStage.T
  T₂ := S.cnfStage.T
  bound₁ := S.dnfStage.depthBound
  bound₂ := S.cnfStage.depthBound
  depth₁_lt := S.dnfStage.depth_lt
  depth₂_lt := S.cnfStage.depth_lt
  compatible := S.compatible
  computes := by
    intro a ha₁ ha₂
    calc
      (dtEval a S.dnfStage.T && dtEval a S.cnfStage.T)
          = (eval a (restrict S.dnfStage.ρ F₁) && eval a (restrict S.cnfStage.ρ F₂)) := by
              rw [S.dnfStage.computes a ha₁, S.cnfStage.computes a ha₂]
      _ = (eval a F₁ && eval a F₂) := by
              rw [eval_restrict S.dnfStage.ρ a F₁ ha₁]
              rw [eval_restrict S.cnfStage.ρ a F₂ ha₂]
      _ = eval a (BDFormula.and [F₁, F₂]) := by
              rw [eval_and]
              cases h₁ : eval a F₁ <;> cases h₂ : eval a F₂ <;> simp [h₁, h₂]
      _ = eval a (restrict S.dnfStage.ρ (BDFormula.and [F₁, F₂])) :=
              (eval_restrict S.dnfStage.ρ a (BDFormula.and [F₁, F₂]) ha₁).symm
      _ = eval a (restrict S.cnfStage.ρ (restrict S.dnfStage.ρ (BDFormula.and [F₁, F₂]))) :=
              (eval_restrict S.cnfStage.ρ a (restrict S.dnfStage.ρ (BDFormula.and [F₁, F₂])) ha₂).symm

/-- Proposition-valued wrapper around the certificate-producing composition
construction, recording that the output uses exactly the scheduled restrictions
and depth bounds. -/
theorem twoLayerCollapse_exists_from_stagePremises {n : Nat} {F₁ F₂ : BDFormula n}
    (S : TwoLayerSchedule F₁ F₂) :
    ∃ C : TwoLayerCollapseCertificate F₁ F₂,
      C.ρ₁ = S.dnfStage.ρ ∧ C.ρ₂ = S.cnfStage.ρ ∧
        C.bound₁ = S.dnfStage.depthBound ∧ C.bound₂ = S.cnfStage.depthBound := by
  exact ⟨twoLayerCollapse_from_stagePremises S, rfl, rfl, rfl, rfl⟩

/-! ## Small non-vacuous example -/

/-- The everywhere-free restriction. -/
def freeRestriction (n : Nat) : Restriction n := fun _ => none

theorem agree_freeRestriction {n : Nat} (a : Assignment n) :
    Agree (freeRestriction n) a := by
  intro v b h
  cases h

/-- The first variable of a nonempty variable set, as a positive literal. -/
def firstPosLit (n : Nat) : Literal (Nat.succ n) :=
  { var := ⟨0, Nat.succ_pos n⟩, sign := true }

/-- The one-literal DNF over `Nat.succ n`. -/
def oneLitDNF (n : Nat) : DNF (Nat.succ n) := [[firstPosLit n]]

/-- The one-literal CNF over `Nat.succ n`. -/
def oneLitCNF (n : Nat) : CNF (Nat.succ n) := [[firstPosLit n]]

/-- The one-literal DNF is simple. -/
theorem oneLitDNF_simple (n : Nat) : SimpleDNF (oneLitDNF n) := by
  intro t ht
  have ht' : t = [firstPosLit n] := by simpa [oneLitDNF] using ht
  subst t
  simp [SimpleTerm]

/-- The one-literal CNF is simple. -/
theorem oneLitCNF_simple (n : Nat) : SimpleCNF (oneLitCNF n) := by
  intro c hc
  have hc' : c = [firstPosLit n] := by simpa [oneLitCNF] using hc
  subst c
  simp [SimpleClause]

/-- Concrete non-empty DNF view for a one-literal embedded DNF. -/
def oneLitDNFView (n : Nat) :
    DNFView (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n)) :=
  dnfToBD_dnfView (oneLitDNF n) (oneLitDNF_simple n)

/-- Concrete non-empty CNF view for the same one-literal formula. -/
def oneLitCNFView (n : Nat) :
    CNFView (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n)) where
  C := oneLitCNF n
  sem_eq := by
    intro a
    simp [oneLitCNF, firstPosLit, cnfEval, clauseEval, eval_lit, litEval]
  simple := oneLitCNF_simple n

/-- Decision tree for the positive first literal. -/
def oneLitTree (n : Nat) : DTree (Nat.succ n) :=
  DTree.node (firstPosLit n).var (DTree.leaf false) (DTree.leaf true)

/-- First-stage one-literal DNF premise using the free restriction. -/
def oneLitDNFStage (n : Nat) :
    DNFLayerCollapsePremise
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n)) where
  view := oneLitDNFView n
  ρ := freeRestriction (Nat.succ n)
  T := oneLitTree n
  depthBound := 2
  depth_lt := by simp [oneLitTree]
  computes := by
    intro a ha
    rw [eval_restrict (freeRestriction (Nat.succ n)) a
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n)) ha]
    rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
    simp [oneLitTree, oneLitDNF, firstPosLit, dnfEval, termEval, litEval]

/-- Second-stage one-literal CNF premise using the free restriction. -/
def oneLitCNFStage (n : Nat) :
    CNFLayerCollapsePremise (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n)) where
  view := oneLitCNFView n
  ρ := freeRestriction (Nat.succ n)
  T := oneLitTree n
  depthBound := 2
  depth_lt := by simp [oneLitTree]
  computes := by
    intro a ha
    rw [eval_restrict (freeRestriction (Nat.succ n)) a
      (BDFormula.lit (firstPosLit n)) ha]
    simp [oneLitTree, firstPosLit, eval_lit, litEval]

/-- First-stage empty-DNF premise.  Its view is the same `emptyDNFView` used by
the existing `emptyDNFView_switching_collapse`; here we store the concrete
collapse witness needed for type-valued schedule composition. -/
def emptyDNFStage (n : Nat) :
    DNFLayerCollapsePremise (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n)) where
  view := emptyDNFView n
  ρ := freeRestriction n
  T := DTree.leaf false
  depthBound := 1
  depth_lt := by simp
  computes := by
    intro a ha
    rw [dtEval_leaf]
    rw [eval_restrict (freeRestriction n) a
      (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n)) ha]
    rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
    rfl

/-- Second-stage explicit CNF premise for the trivially true empty CNF. -/
def emptyCNFStage (n : Nat) :
    CNFLayerCollapsePremise (BDFormula.tru : BDFormula n) where
  view := emptyCNFView n
  ρ := freeRestriction n
  T := DTree.leaf true
  depthBound := 1
  depth_lt := by simp
  computes := by
    intro a _ha
    simp [eval_tru, restrict_tru]

/-- A concrete two-layer schedule combining the empty DNF bottom layer with the
empty CNF top layer.  Compatibility is witnessed by an arbitrary total assignment,
so this is not a vacuous schedule. -/
def emptyTwoLayerSchedule (n : Nat) :
    TwoLayerSchedule (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n))
      (BDFormula.tru : BDFormula n) where
  dnfStage := emptyDNFStage n
  cnfStage := emptyCNFStage n
  compatible := by
    refine ⟨fun _ => false, ?_, ?_⟩
    · simpa [emptyDNFStage] using agree_freeRestriction (fun _ : Fin n => false)
    · simpa [emptyCNFStage] using agree_freeRestriction (fun _ : Fin n => false)

/-- Non-vacuous instantiation of the two-layer composition theorem. -/
def emptyTwoLayerCollapse_example (n : Nat) :
    TwoLayerCollapseCertificate
      (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n))
      (BDFormula.tru : BDFormula n) :=
  twoLayerCollapse_from_stagePremises (emptyTwoLayerSchedule n)

/-- The concrete empty-DNF/empty-CNF example has an explicit common-extension
compatibility witness. -/
theorem emptyTwoLayerCollapse_example_nonvacuous (n : Nat) :
    ∃ C : TwoLayerCollapseCertificate
      (BoundedDepthFregeSwitchingBridge.dnfToBD ([] : DNF n))
      (BDFormula.tru : BDFormula n), ∃ a : Assignment n, Agree C.ρ₁ a ∧ Agree C.ρ₂ a :=
  ⟨emptyTwoLayerCollapse_example n, (emptyTwoLayerCollapse_example n).compatible⟩

/-- Concrete two-layer schedule with a one-literal DNF stage and a one-literal CNF
stage over `Nat.succ n`.  The common extension is explicit because both stages use
`freeRestriction`; the certificate remains schedule-based by design, rather than
claiming a general CNF switching lemma for arbitrary CNF views. -/
def oneLitTwoLayerSchedule (n : Nat) :
    TwoLayerSchedule
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n))
      (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n)) where
  dnfStage := oneLitDNFStage n
  cnfStage := oneLitCNFStage n
  compatible := by
    refine ⟨fun _ => false, ?_, ?_⟩
    · simpa [oneLitDNFStage] using agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)
    · simpa [oneLitCNFStage] using agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)

/-- Non-empty two-layer collapse certificate obtained from the concrete
one-literal schedule. -/
def oneLitTwoLayerCollapse_example (n : Nat) :
    TwoLayerCollapseCertificate
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n))
      (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n)) :=
  twoLayerCollapse_from_stagePremises (oneLitTwoLayerSchedule n)

end BoundedDepthIteratedCollapse
end PvNP
