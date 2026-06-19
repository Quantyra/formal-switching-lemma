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

/-- Negate a literal. -/
def negLit {n : Nat} (l : Literal n) : Literal n :=
  { var := l.var, sign := !l.sign }

/-- A CNF clause is falsified exactly by the term of negated literals. -/
def clauseDualTerm {n : Nat} (c : Clause n) : Term n :=
  c.map negLit

/-- The DNF dual of a CNF: one term for each falsified clause. -/
def cnfDualDNF {n : Nat} (C : CNF n) : DNF n :=
  C.map clauseDualTerm

@[simp] theorem clauseEval_nil {n : Nat} (a : Assignment n) :
    clauseEval a ([] : Clause n) = false := rfl

@[simp] theorem cnfEval_nil {n : Nat} (a : Assignment n) :
    cnfEval a ([] : CNF n) = true := rfl

@[simp] theorem litEval_negLit {n : Nat} (a : Assignment n) (l : Literal n) :
    litEval a (negLit l) = !(litEval a l) := by
  cases hs : l.sign <;> simp [negLit, litEval, hs]

/-- A clause's dual term evaluates to the negation of the clause. -/
theorem termEval_clauseDualTerm {n : Nat} (a : Assignment n) (c : Clause n) :
    termEval a (clauseDualTerm c) = !(clauseEval a c) := by
  induction c with
  | nil => simp [clauseDualTerm, clauseEval, termEval]
  | cons l c ih =>
      rw [show clauseDualTerm (l :: c) = negLit l :: clauseDualTerm c by rfl]
      rw [termEval_cons, litEval_negLit, ih]
      change (!litEval a l && !clauseEval a c) = !(litEval a l || clauseEval a c)
      cases litEval a l <;> cases clauseEval a c <;> rfl

/-- The DNF dual of a CNF computes the negation of the CNF. -/
theorem dnfEval_cnfDualDNF {n : Nat} (a : Assignment n) (C : CNF n) :
    dnfEval a (cnfDualDNF C) = !(cnfEval a C) := by
  induction C with
  | nil => simp [cnfDualDNF, cnfEval, dnfEval]
  | cons c C ih =>
      rw [show cnfDualDNF (c :: C) = clauseDualTerm c :: cnfDualDNF C by rfl]
      rw [dnfEval_cons, termEval_clauseDualTerm, ih]
      change (!clauseEval a c || !cnfEval a C) = !(clauseEval a c && cnfEval a C)
      cases clauseEval a c <;> cases cnfEval a C <;> rfl

/-- Clause simplicity transfers to the dual DNF term. -/
theorem simpleTerm_clauseDualTerm_of_simpleClause {n : Nat} {c : Clause n}
    (hc : SimpleClause c) : SimpleTerm (clauseDualTerm c) := by
  simpa [clauseDualTerm, negLit, SimpleClause, SimpleTerm] using hc

/-- A simple CNF dualizes to a simple DNF. -/
theorem simpleDNF_cnfDualDNF_of_simpleCNF {n : Nat} {C : CNF n}
    (hC : SimpleCNF C) : SimpleDNF (cnfDualDNF C) := by
  intro t ht
  rcases List.mem_map.1 ht with ⟨c, hc, rfl⟩
  exact simpleTerm_clauseDualTerm_of_simpleClause (hC c hc)

/-- Complement every leaf of a decision tree. -/
def notTree {n : Nat} : DTree n -> DTree n
  | DTree.leaf b => DTree.leaf (!b)
  | DTree.node v t0 t1 => DTree.node v (notTree t0) (notTree t1)

@[simp] theorem dtEval_notTree {n : Nat} (a : Assignment n) (T : DTree n) :
    dtEval a (notTree T) = !(dtEval a T) := by
  induction T with
  | leaf b => simp [notTree]
  | node v t0 t1 ih0 ih1 =>
      simp [notTree, ih0, ih1]
      cases a v <;> rfl

@[simp] theorem dtDepth_notTree {n : Nat} (T : DTree n) :
    dtDepth (notTree T) = dtDepth T := by
  induction T with
  | leaf _ => simp [notTree]
  | node _ _ _ ih0 ih1 => simp [notTree, ih0, ih1]

/-- A semantic bottom-layer CNF view of a real bounded-depth formula.  This is a
dual view record only; no CNF switching lemma is asserted here. -/
structure CNFView {n : Nat} (F : BDFormula n) where
  C : CNF n
  sem_eq : ∀ a : Assignment n, eval a F = cnfEval a C
  simple : SimpleCNF C

/-- The DNF switching theorem applied to the dual DNF gives a genuine CNF-view
collapse theorem.  This replaces the previous purely explicit CNF-stage premise
for any CNF view whose dual DNF has the requested width bound: good restrictions
for the dual DNF yield a shallow decision tree computing the restricted CNF-view
formula, by complementing the dual-DNF decision tree. -/
theorem bdFormula_cnfView_dual_switching_collapse {n : Nat} {F : BDFormula n}
    (V : CNFView F) (w s ℓ : Nat) (hw : widthDNF (cnfDualDNF V.C) ≤ w) :
    (badSetTerm (cnfDualDNF V.C) s ℓ).card ≤
        (restrictionsWithStars n (ℓ - s)).card * (8 * w)^s ∧
      ∀ ρ, ρ ∈ restrictionsWithStars n ℓ → ρ ∉ badSetTerm (cnfDualDNF V.C) s ℓ →
        ∃ T : DTree n, dtDepth T < s ∧
          ∀ a : Assignment n, Agree ρ a → dtEval a T = eval a (restrict ρ F) := by
  have hsimpleDual : SimpleDNF (cnfDualDNF V.C) :=
    simpleDNF_cnfDualDNF_of_simpleCNF V.simple
  rcases BoundedDepthFregeSwitchingBridge.bdDNF_switching_bridge
      (cnfDualDNF V.C) w s ℓ hsimpleDual hw with ⟨hcard, hcollapse⟩
  constructor
  · exact hcard
  · intro ρ hρstars hρgood
    rcases hcollapse ρ hρstars hρgood with ⟨T, hdepth, hT⟩
    refine ⟨notTree T, by simpa using hdepth, ?_⟩
    intro a ha
    calc
      dtEval a (notTree T) = !(dtEval a T) := dtEval_notTree a T
      _ = !(eval a (restrict ρ (BoundedDepthFregeSwitchingBridge.dnfToBD (cnfDualDNF V.C)))) := by
        rw [hT a ha]
      _ = !(eval a (BoundedDepthFregeSwitchingBridge.dnfToBD (cnfDualDNF V.C))) := by
        rw [eval_restrict ρ a (BoundedDepthFregeSwitchingBridge.dnfToBD (cnfDualDNF V.C)) ha]
      _ = !(dnfEval a (cnfDualDNF V.C)) := by
        rw [BoundedDepthFregeSwitchingBridge.eval_dnfToBD]
      _ = cnfEval a V.C := by
        rw [dnfEval_cnfDualDNF]
        cases cnfEval a V.C <;> rfl
      _ = eval a F := (V.sem_eq a).symm
      _ = eval a (restrict ρ F) := (eval_restrict ρ a F ha).symm

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

/-! ## Three-stage schedule extension -/

/-- A three-stage explicit schedule alternating DNF/CNF/DNF viewed layers.  This
is still schedule data, not a theorem that arbitrary bounded-depth formulas admit
such views or restrictions. -/
structure ThreeLayerSchedule {n : Nat} (F₁ F₂ F₃ : BDFormula n) where
  dnfStage₁ : DNFLayerCollapsePremise F₁
  cnfStage₂ : CNFLayerCollapsePremise F₂
  dnfStage₃ : DNFLayerCollapsePremise F₃
  compatible : ∃ a : Assignment n,
    Agree dnfStage₁.ρ a ∧ Agree cnfStage₂.ρ a ∧ Agree dnfStage₃.ρ a

/-- Three-stage explicit collapse certificate for a DNF/CNF/DNF schedule. -/
structure ThreeLayerCollapseCertificate {n : Nat} (F₁ F₂ F₃ : BDFormula n) where
  ρ₁ : Restriction n
  ρ₂ : Restriction n
  ρ₃ : Restriction n
  T₁ : DTree n
  T₂ : DTree n
  T₃ : DTree n
  bound₁ : Nat
  bound₂ : Nat
  bound₃ : Nat
  depth₁_lt : dtDepth T₁ < bound₁
  depth₂_lt : dtDepth T₂ < bound₂
  depth₃_lt : dtDepth T₃ < bound₃
  compatible : ∃ a : Assignment n, Agree ρ₁ a ∧ Agree ρ₂ a ∧ Agree ρ₃ a
  computes : ∀ a : Assignment n, Agree ρ₁ a → Agree ρ₂ a → Agree ρ₃ a →
    ((dtEval a T₁ && dtEval a T₂) && dtEval a T₃) =
      eval a (restrict ρ₃ (restrict ρ₂ (restrict ρ₁ (BDFormula.and [F₁, F₂, F₃]))))

/-- Composition theorem for three explicit bottom layers. -/
def threeLayerCollapse_from_stagePremises {n : Nat} {F₁ F₂ F₃ : BDFormula n}
    (S : ThreeLayerSchedule F₁ F₂ F₃) :
    ThreeLayerCollapseCertificate F₁ F₂ F₃ where
  ρ₁ := S.dnfStage₁.ρ
  ρ₂ := S.cnfStage₂.ρ
  ρ₃ := S.dnfStage₃.ρ
  T₁ := S.dnfStage₁.T
  T₂ := S.cnfStage₂.T
  T₃ := S.dnfStage₃.T
  bound₁ := S.dnfStage₁.depthBound
  bound₂ := S.cnfStage₂.depthBound
  bound₃ := S.dnfStage₃.depthBound
  depth₁_lt := S.dnfStage₁.depth_lt
  depth₂_lt := S.cnfStage₂.depth_lt
  depth₃_lt := S.dnfStage₃.depth_lt
  compatible := S.compatible
  computes := by
    intro a ha₁ ha₂ ha₃
    calc
      ((dtEval a S.dnfStage₁.T && dtEval a S.cnfStage₂.T) && dtEval a S.dnfStage₃.T)
          = ((eval a (restrict S.dnfStage₁.ρ F₁) && eval a (restrict S.cnfStage₂.ρ F₂)) &&
              eval a (restrict S.dnfStage₃.ρ F₃)) := by
                rw [S.dnfStage₁.computes a ha₁, S.cnfStage₂.computes a ha₂,
                  S.dnfStage₃.computes a ha₃]
      _ = ((eval a F₁ && eval a F₂) && eval a F₃) := by
              rw [eval_restrict S.dnfStage₁.ρ a F₁ ha₁]
              rw [eval_restrict S.cnfStage₂.ρ a F₂ ha₂]
              rw [eval_restrict S.dnfStage₃.ρ a F₃ ha₃]
      _ = eval a (BDFormula.and [F₁, F₂, F₃]) := by
              rw [eval_and]
              cases h₁ : eval a F₁ <;> cases h₂ : eval a F₂ <;> cases h₃ : eval a F₃ <;>
                simp [h₁, h₂, h₃]
      _ = eval a (restrict S.dnfStage₁.ρ (BDFormula.and [F₁, F₂, F₃])) :=
              (eval_restrict S.dnfStage₁.ρ a (BDFormula.and [F₁, F₂, F₃]) ha₁).symm
      _ = eval a (restrict S.cnfStage₂.ρ (restrict S.dnfStage₁.ρ (BDFormula.and [F₁, F₂, F₃]))) :=
              (eval_restrict S.cnfStage₂.ρ a
                (restrict S.dnfStage₁.ρ (BDFormula.and [F₁, F₂, F₃])) ha₂).symm
      _ = eval a (restrict S.dnfStage₃.ρ
            (restrict S.cnfStage₂.ρ (restrict S.dnfStage₁.ρ (BDFormula.and [F₁, F₂, F₃])))) :=
              (eval_restrict S.dnfStage₃.ρ a
                (restrict S.cnfStage₂.ρ (restrict S.dnfStage₁.ρ (BDFormula.and [F₁, F₂, F₃]))) ha₃).symm

/-- Proposition-valued wrapper around the three-stage schedule construction. -/
theorem threeLayerCollapse_exists_from_stagePremises {n : Nat} {F₁ F₂ F₃ : BDFormula n}
    (S : ThreeLayerSchedule F₁ F₂ F₃) :
    ∃ C : ThreeLayerCollapseCertificate F₁ F₂ F₃,
      C.ρ₁ = S.dnfStage₁.ρ ∧ C.ρ₂ = S.cnfStage₂.ρ ∧ C.ρ₃ = S.dnfStage₃.ρ ∧
        C.bound₁ = S.dnfStage₁.depthBound ∧ C.bound₂ = S.cnfStage₂.depthBound ∧
          C.bound₃ = S.dnfStage₃.depthBound := by
  exact ⟨threeLayerCollapse_from_stagePremises S, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## List-indexed alternating schedules -/

/-- The declared view kind of a bottom layer in a list-indexed schedule. -/
inductive LayerKind where
  | dnf
  | cnf
deriving DecidableEq

namespace LayerKind

/-- Adjacent layer kinds alternate.  Empty and singleton schedules are allowed
as structural certificates; nonempty witnesses below show inhabited schedules. -/
def Alternating : List LayerKind -> Prop
  | [] => True
  | [_] => True
  | k₁ :: k₂ :: rest => k₁ ≠ k₂ ∧ Alternating (k₂ :: rest)

end LayerKind

/-- One explicit viewed stage in a list-indexed schedule.  The `kind` field
records whether the stage came from a DNF or CNF view; the witness fields record
the actual restriction, tree, depth accounting, and restricted-formula semantics. -/
structure ExplicitLayerStage (n : Nat) where
  kind : LayerKind
  F : BDFormula n
  ρ : Restriction n
  T : DTree n
  depthBound : Nat
  depth_lt : dtDepth T < depthBound
  computes : ∀ a : Assignment n, Agree ρ a → dtEval a T = eval a (restrict ρ F)

/-- Convert an explicit DNF stage premise to the list-indexed stage format. -/
def explicitStageOfDNF {n : Nat} {F : BDFormula n}
    (P : DNFLayerCollapsePremise F) : ExplicitLayerStage n where
  kind := LayerKind.dnf
  F := F
  ρ := P.ρ
  T := P.T
  depthBound := P.depthBound
  depth_lt := P.depth_lt
  computes := P.computes

/-- Convert an explicit CNF stage premise to the list-indexed stage format. -/
def explicitStageOfCNF {n : Nat} {F : BDFormula n}
    (P : CNFLayerCollapsePremise F) : ExplicitLayerStage n where
  kind := LayerKind.cnf
  F := F
  ρ := P.ρ
  T := P.T
  depthBound := P.depthBound
  depth_lt := P.depth_lt
  computes := P.computes

/-- A list-indexed alternating schedule with explicit depth accounting and a
common-extension witness for all scheduled restrictions. -/
structure KLayerSchedule (n : Nat) where
  stages : List (ExplicitLayerStage n)
  alternating : LayerKind.Alternating (stages.map (fun S => S.kind))
  compatible : ∃ a : Assignment n, ∀ S, S ∈ stages → Agree S.ρ a

/-- A list-indexed collapse certificate.  It deliberately certifies the named
stage witnesses and common extension rather than claiming arbitrary AC0 collapse. -/
structure KLayerCollapseCertificate (n : Nat) where
  stages : List (ExplicitLayerStage n)
  alternating : LayerKind.Alternating (stages.map (fun S => S.kind))
  depthAccounting : ∀ S, S ∈ stages → dtDepth S.T < S.depthBound
  compatible : ∃ a : Assignment n, ∀ S, S ∈ stages → Agree S.ρ a
  computesEach : ∀ S, S ∈ stages → ∀ a : Assignment n,
    Agree S.ρ a → dtEval a S.T = eval a (restrict S.ρ S.F)

/-- Turn a list-indexed alternating schedule into a collapse certificate. -/
def kLayerCollapse_from_schedule {n : Nat} (S : KLayerSchedule n) :
    KLayerCollapseCertificate n where
  stages := S.stages
  alternating := S.alternating
  depthAccounting := by
    intro stage _hstage
    exact stage.depth_lt
  compatible := S.compatible
  computesEach := by
    intro stage _hstage a ha
    exact stage.computes a ha

/-- Proposition-valued wrapper for the list-indexed schedule construction. -/
theorem kLayerCollapse_exists_from_schedule {n : Nat} (S : KLayerSchedule n) :
    ∃ C : KLayerCollapseCertificate n, C.stages = S.stages := by
  exact ⟨kLayerCollapse_from_schedule S, rfl⟩

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

/-- Concrete three-layer schedule with one-literal DNF, CNF, then DNF stages over
the same nonempty variable set.  All restrictions are free, so the common
extension is explicit while the certificate remains schedule-based. -/
def oneLitThreeLayerSchedule (n : Nat) :
    ThreeLayerSchedule
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n))
      (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n))
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n)) where
  dnfStage₁ := oneLitDNFStage n
  cnfStage₂ := oneLitCNFStage n
  dnfStage₃ := oneLitDNFStage n
  compatible := by
    refine ⟨fun _ => false, ?_, ?_, ?_⟩
    · simpa [oneLitDNFStage] using agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)
    · simpa [oneLitCNFStage] using agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)
    · simpa [oneLitDNFStage] using agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)

/-- Non-empty three-layer collapse certificate obtained from the concrete
one-literal DNF/CNF/DNF schedule. -/
def oneLitThreeLayerCollapse_example (n : Nat) :
    ThreeLayerCollapseCertificate
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n))
      (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n))
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n)) :=
  threeLayerCollapse_from_stagePremises (oneLitThreeLayerSchedule n)

/-- The concrete three-layer example has an explicit common-extension witness. -/
theorem oneLitThreeLayerCollapse_example_nonvacuous (n : Nat) :
    ∃ C : ThreeLayerCollapseCertificate
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n))
      (BDFormula.lit (firstPosLit n) : BDFormula (Nat.succ n))
      (BoundedDepthFregeSwitchingBridge.dnfToBD (oneLitDNF n)),
        ∃ a : Assignment (Nat.succ n), Agree C.ρ₁ a ∧ Agree C.ρ₂ a ∧ Agree C.ρ₃ a :=
  ⟨oneLitThreeLayerCollapse_example n, (oneLitThreeLayerCollapse_example n).compatible⟩

/-- The one-literal DNF/CNF/DNF schedule as a list-indexed alternating schedule. -/
def oneLitKLayerSchedule3 (n : Nat) : KLayerSchedule (Nat.succ n) where
  stages := [
    explicitStageOfDNF (oneLitDNFStage n),
    explicitStageOfCNF (oneLitCNFStage n),
    explicitStageOfDNF (oneLitDNFStage n)]
  alternating := by
    simp [explicitStageOfDNF, explicitStageOfCNF, LayerKind.Alternating]
  compatible := by
    refine ⟨fun _ => false, ?_⟩
    intro S hS
    simp only [List.mem_cons, List.mem_singleton] at hS
    rcases hS with hS | hS
    · subst S
      simpa [explicitStageOfDNF, oneLitDNFStage] using
        agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)
    · rcases hS with hS | hS
      · subst S
        simpa [explicitStageOfCNF, oneLitCNFStage] using
          agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)
      · rcases hS with hS | hS
        · subst S
          simpa [explicitStageOfDNF, oneLitDNFStage] using
            agree_freeRestriction (fun _ : Fin (Nat.succ n) => false)
        · cases hS

/-- Nonempty list-indexed alternating DNF/CNF/DNF witness with explicit common
extension compatibility. -/
theorem oneLitKLayerSchedule3_nonempty (n : Nat) :
    ∃ C : KLayerCollapseCertificate (Nat.succ n),
      C.stages.length = 3 ∧
        ∃ a : Assignment (Nat.succ n), ∀ S, S ∈ C.stages → Agree S.ρ a := by
  refine ⟨kLayerCollapse_from_schedule (oneLitKLayerSchedule3 n), ?_, ?_⟩
  · simp [kLayerCollapse_from_schedule, oneLitKLayerSchedule3]
  · exact (kLayerCollapse_from_schedule (oneLitKLayerSchedule3 n)).compatible

end BoundedDepthIteratedCollapse
end PvNP
