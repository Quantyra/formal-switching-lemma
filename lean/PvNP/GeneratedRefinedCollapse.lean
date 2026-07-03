import PvNP.SwitchingRelabel
import PvNP.GeneratedIteratedCollapseFinal

/-!
# Gate B: renormalized (free-subcube) counting and the refined iterated collapse

This module closes, FOR THE REFINEMENT ROUTE, the KNOWN SATISFIABILITY GAP
disclosed on the B4 route theorem (frozen-form B4 remains open).  The old stage beat compared a FULL-space bad-set count against a
consistent-subspace cardinality; here the bad set intersected with the
REFINEMENT subspace of a base restriction is counted against the base's free
subcube:

* `badSetTerm_refines_card_le` — the renormalized bad-set bound
  `|badSetTerm D s ℓ ∩ refinesSubspace base ℓ| ≤ |R(stars base, ℓ-s)| * (8w)^s`,
  by transporting along the free-subcube relabeling and instantiating the
  PROVED SimpleDNF switching lemma at dimension `stars base`;
* `simultaneousCollapse_exists_refined` — counting generates one refinement of
  the base that simultaneously collapses every listed gate, whenever the
  renormalized union bound beats the refinement-subspace cardinality (which
  has the closed form `C(stars base, ℓ)·2^(stars base - ℓ)`);
* `GeneratedRefinedCollapsePlan` / `GeneratedRefinedIteratedCertificate` /
  `generatedRefinedIteratedCollapse` — the B4 route machinery with the
  renormalized stage beats.  Stage restrictions now REFINE the accumulated
  base (strictly stronger than consistency), so the composed-restriction and
  agreement-transfer conclusions carry over.

## HONEST SCOPE STATEMENT (read this)

* The per-stage layered views, the renormalized beats, and the (easy)
  full-space beats used to index the B3 certificate type are SUPPLIED by the
  plan; the restrictions are never supplied — counting generates them.
* This is still NOT arbitrary AC0/`BDFormula` decomposition: a caller who
  wants a nonempty later stage must supply that stage's view of the generated
  rewritten formula through the plan's `next` function.
* Frozen-form B4 (single upfront depth-`d` view, product hypothesis
  `B(m, w, s, d)`, `t(d, s)` tree bound) remains OPEN.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size lower
  bound, NOT an NP/circuit lower bound, NOT a statement about P vs NP.
  Gate A rung 4 remains open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace GeneratedRefinedCollapse

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
open SwitchingTermCanonicalDT
open RestrictionComposition
open RefinedSubspace
open SwitchingRelabel
open GeneratedOneStepDepthReduction
open GeneratedIteratedCollapseFinal

/-! ## Fully fixed restrictions collapse everything to depth 0 -/

theorem dtDepth_termCanonicalDT_of_allNil {n : Nat} (E : DNF n)
    (h : ∀ t ∈ E, t = []) : dtDepth (termCanonicalDT E) = 0 := by
  cases E with
  | nil =>
      rw [show termCanonicalDT ([] : DNF n) = DTree.leaf false from by
        rw [termCanonicalDT]]
      rfl
  | cons t E =>
      have ht : t = [] := h t (List.mem_cons_self t E)
      subst ht
      rw [show termCanonicalDT (([] : Term n) :: E) = DTree.leaf true from by
        rw [termCanonicalDT]]
      rfl

theorem dtDepth_dnfRestrict_of_stars_zero {n : Nat} (ρ : Restriction n)
    (h : stars ρ = 0) (D : DNF n) :
    dtDepth (termCanonicalDT (dnfRestrict ρ D)) = 0 := by
  apply dtDepth_termCanonicalDT_of_allNil
  intro t ht
  have hvars := dnfVarsIn_starSet_dnfRestrict ρ D t ht
  have hempty : starSet ρ = ∅ := by
    have := stars_eq_starSet_card ρ
    rw [h] at this
    exact Finset.card_eq_zero.mp this.symm
  rw [List.eq_nil_iff_forall_not_mem]
  intro l hl
  have := hvars l hl
  rw [hempty] at this
  exact absurd this (Finset.not_mem_empty _)

/-! ## The renormalized bad-set bound -/

/-- **The renormalized per-gate bad-set bound.**  Inside the refinement
subspace of `base`, at most `|R(stars base, ℓ-s)| * (8w)^s` restrictions are
bad for a width-`≤ w` simple DNF: transport along the free subcube and apply
the PROVED switching lemma at dimension `stars base`. -/
theorem badSetTerm_refines_card_le {n : Nat} (base : Restriction n)
    {D : DNF n} (hD : SimpleDNF D) (w s ℓ : Nat) (hw : widthDNF D ≤ w) :
    ((badSetTerm D s ℓ) ∩ refinesSubspace base ℓ).card ≤
      (restrictionsWithStars (stars base) (ℓ - s)).card * (8 * w) ^ s := by
  classical
  by_cases hℓm : ℓ ≤ stars base
  · by_cases hm : 0 < stars base
    · -- Main case: transport along the free subcube.
      have hr0 : (0 : Nat) < stars base := hm
      let r : Fin n → Fin (stars base) := fun v =>
        if hv : v ∈ starSet base then freeEquiv base ⟨v, hv⟩ else ⟨0, hr0⟩
      have hr_free : ∀ (v : Fin n) (hv : v ∈ starSet base),
          r v = freeEquiv base ⟨v, hv⟩ := by
        intro v hv
        simp only [r, dif_pos hv]
      have hinj : ∀ u ∈ starSet base, ∀ v ∈ starSet base, r u = r v → u = v := by
        intro u hu v hv huv
        rw [hr_free u hu, hr_free v hv] at huv
        have h2 := (freeEquiv base).injective huv
        exact congrArg Subtype.val h2
      have hEvars : DNFVarsIn (dnfRestrict base D) (starSet base) :=
        dnfVarsIn_starSet_dnfRestrict base D
      have hD'simple : SimpleDNF (mapDNF r (dnfRestrict base D)) :=
        simpleDNF_mapDNF r hinj hEvars (simpleDNF_dnfRestrict base hD)
      have hD'width : widthDNF (mapDNF r (dnfRestrict base D)) ≤ w := by
        rw [widthDNF_mapDNF]
        exact Nat.le_trans
          (SwitchingLemmaStatement.widthDNF_dnfRestrict_le base D) hw
      have hswitch := SwitchingClose2.switchingLemmaTermSimple_proved
        (n := stars base) (mapDNF r (dnfRestrict base D)) w s ℓ
        hD'simple hD'width
      have hmap : ∀ ρ ∈ (badSetTerm D s ℓ) ∩ refinesSubspace base ℓ,
          downRestriction base ρ ∈
            badSetTerm (mapDNF r (dnfRestrict base D)) s ℓ := by
        intro ρ hρ
        rw [Finset.mem_inter] at hρ
        obtain ⟨hbad, hrefmem⟩ := hρ
        rw [mem_badSetTerm] at hbad
        obtain ⟨hstars, hdepth⟩ := hbad
        rw [mem_refinesSubspace] at hrefmem
        obtain ⟨_, href⟩ := hrefmem
        rw [mem_badSetTerm]
        constructor
        · rw [stars_downRestriction href, hstars]
        · have hcorr : ∀ v ∈ starSet base,
              (downRestriction base ρ) (r v) = ρ v := by
            intro v hv
            rw [hr_free v hv]
            show ρ (freeEmbed base (freeEquiv base ⟨v, hv⟩)) = ρ v
            rw [freeEmbed_freeEquiv]
          have hrest : dnfRestrict (downRestriction base ρ)
              (mapDNF r (dnfRestrict base D)) =
              mapDNF r (dnfRestrict ρ (dnfRestrict base D)) :=
            dnfRestrict_mapDNF r ρ (downRestriction base ρ) hcorr
              (dnfRestrict base D) hEvars
          have hfact : dnfRestrict ρ (dnfRestrict base D) = dnfRestrict ρ D :=
            (dnfRestrict_refinesWith href D).symm
          have hvars2 : DNFVarsIn (dnfRestrict ρ D) (starSet base) := by
            intro t ht l hl
            exact starSet_subset_of_refinesWith href
              (dnfVarsIn_starSet_dnfRestrict ρ D t ht l hl)
          have hdepth' : dtDepth (termCanonicalDT
              (dnfRestrict (downRestriction base ρ)
                (mapDNF r (dnfRestrict base D)))) =
              dtDepth (termCanonicalDT (dnfRestrict ρ D)) := by
            rw [hrest, hfact]
            exact dtDepth_termCanonicalDT_mapDNF r (starSet base) hinj
              (dnfRestrict ρ D) hvars2
          omega
      have hinjOn : Set.InjOn (downRestriction base)
          (↑((badSetTerm D s ℓ) ∩ refinesSubspace base ℓ) :
            Set (Restriction n)) := by
        intro ρ₁ h₁ ρ₂ h₂ heq
        rw [Finset.mem_coe, Finset.mem_inter, mem_refinesSubspace] at h₁ h₂
        calc ρ₁ = upRestriction base (downRestriction base ρ₁) :=
              (upRestriction_downRestriction h₁.2.2).symm
          _ = upRestriction base (downRestriction base ρ₂) := by rw [heq]
          _ = ρ₂ := upRestriction_downRestriction h₂.2.2
      calc ((badSetTerm D s ℓ) ∩ refinesSubspace base ℓ).card
          ≤ (badSetTerm (mapDNF r (dnfRestrict base D)) s ℓ).card :=
            Finset.card_le_card_of_injOn (downRestriction base) hmap hinjOn
        _ ≤ (restrictionsWithStars (stars base) (ℓ - s)).card * (8 * w) ^ s :=
            hswitch
    · -- Degenerate case: the base has no free variables, so ℓ = 0.
      have hℓ0 : ℓ = 0 := by omega
      subst hℓ0
      by_cases hs : s = 0
      · subst hs
        calc ((badSetTerm D 0 0) ∩ refinesSubspace base 0).card
            ≤ (refinesSubspace base 0).card :=
              Finset.card_le_card Finset.inter_subset_right
          _ = (stars base).choose 0 * 2 ^ (stars base - 0) :=
              refinesSubspace_card base 0
          _ = (restrictionsWithStars (stars base) (0 - 0)).card := by
              rw [restrictionsWithStars_card]
          _ = (restrictionsWithStars (stars base) (0 - 0)).card *
                (8 * w) ^ 0 := by
              rw [pow_zero, Nat.mul_one]
      · have hempty : (badSetTerm D s 0) ∩ refinesSubspace base 0 = ∅ := by
          rw [Finset.eq_empty_iff_forall_not_mem]
          intro ρ hρ
          rw [Finset.mem_inter, mem_badSetTerm] at hρ
          obtain ⟨⟨hstars0, hdepth⟩, _⟩ := hρ
          have hzero := dtDepth_dnfRestrict_of_stars_zero ρ hstars0 D
          omega
        rw [hempty, Finset.card_empty]
        exact Nat.zero_le _
  · -- ℓ exceeds the base's free capacity: the refinement subspace is empty.
    rw [refinesSubspace_eq_empty_of_lt (by omega), Finset.inter_empty,
      Finset.card_empty]
    exact Nat.zero_le _

/-- **The renormalized union bound.**  Inside the refinement subspace, at most
`m * (|R(stars base, ℓ-s)| * (8w)^s)` restrictions are bad for any of `m`
width-`≤ w` gates. -/
theorem jointBadSet_refines_card_le {n : Nat} (base : Restriction n)
    (gates : List (GateSpec n)) (w s ℓ : Nat)
    (hwidth : ∀ g ∈ gates, widthDNF g.theDNF ≤ w) :
    ((jointBadSet gates s ℓ) ∩ refinesSubspace base ℓ).card ≤
      gates.length *
        ((restrictionsWithStars (stars base) (ℓ - s)).card * (8 * w) ^ s) := by
  classical
  induction gates with
  | nil =>
      simp [jointBadSet]
  | cons g gates ih =>
      have hg := badSetTerm_refines_card_le base g.theDNF_simple w s ℓ
        (hwidth g (List.mem_cons_self g gates))
      have hrest := ih (fun g' hg' => hwidth g' (List.mem_cons_of_mem g hg'))
      have hcons : jointBadSet (g :: gates) s ℓ =
          badSetTerm g.theDNF s ℓ ∪ jointBadSet gates s ℓ := rfl
      calc ((jointBadSet (g :: gates) s ℓ) ∩ refinesSubspace base ℓ).card
          = (((badSetTerm g.theDNF s ℓ) ∩ refinesSubspace base ℓ) ∪
              ((jointBadSet gates s ℓ) ∩ refinesSubspace base ℓ)).card := by
            rw [hcons, Finset.union_inter_distrib_right]
        _ ≤ ((badSetTerm g.theDNF s ℓ) ∩ refinesSubspace base ℓ).card +
              ((jointBadSet gates s ℓ) ∩ refinesSubspace base ℓ).card :=
            Finset.card_union_le _ _
        _ ≤ (restrictionsWithStars (stars base) (ℓ - s)).card * (8 * w) ^ s +
              gates.length *
                ((restrictionsWithStars (stars base) (ℓ - s)).card *
                  (8 * w) ^ s) :=
            Nat.add_le_add hg hrest
        _ = (g :: gates).length *
              ((restrictionsWithStars (stars base) (ℓ - s)).card *
                (8 * w) ^ s) := by
            rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-! ## Counting generates a refining good restriction -/

/-- **The renormalized stage keystone.**  When the renormalized union bound
beats the refinement-subspace cardinality, counting generates ONE restriction
that has `ℓ` stars, REFINES the base, and collapses EVERY listed gate to a
decision tree of depth `< s`. -/
theorem simultaneousCollapse_exists_refined {n : Nat} (base : Restriction n)
    (gates : List (GateSpec n)) (w s ℓ : Nat)
    (hwidth : ∀ g ∈ gates, widthDNF g.theDNF ≤ w)
    (hbeat : gates.length *
        ((restrictionsWithStars (stars base) (ℓ - s)).card * (8 * w) ^ s) <
      (refinesSubspace base ℓ).card) :
    ∃ ρ ∈ restrictionsWithStars n ℓ, RefinesWith base ρ ∧
      ∀ g ∈ gates, ∃ T : DTree n, dtDepth T < s ∧
        ∀ a : Assignment n, Agree ρ a →
          dtEval a T = eval a (restrict ρ g.formula) := by
  classical
  have hcard : ((jointBadSet gates s ℓ) ∩ refinesSubspace base ℓ).card <
      (refinesSubspace base ℓ).card :=
    Nat.lt_of_le_of_lt (jointBadSet_refines_card_le base gates w s ℓ hwidth)
      hbeat
  have hsd : (refinesSubspace base ℓ) \ jointBadSet gates s ℓ =
      (refinesSubspace base ℓ) \
        ((jointBadSet gates s ℓ) ∩ refinesSubspace base ℓ) := by
    ext ρ
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsdiff : 0 <
      ((refinesSubspace base ℓ) \ jointBadSet gates s ℓ).card := by
    rw [hsd]
    have := Finset.le_card_sdiff
      ((jointBadSet gates s ℓ) ∩ refinesSubspace base ℓ)
      (refinesSubspace base ℓ)
    omega
  obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp hsdiff
  rw [Finset.mem_sdiff] at hρ
  obtain ⟨hρmem, hρgood⟩ := hρ
  rw [mem_refinesSubspace] at hρmem
  refine ⟨ρ, hρmem.1, hρmem.2, ?_⟩
  intro g hg
  exact gate_collapse g w s ℓ (hwidth g hg) ρ hρmem.1
    (fun hbad => hρgood (mem_jointBadSet.mpr ⟨g, hg, hbad⟩))

/-! ## Refined stage inputs -/

/-- A renormalized B4 stage input: the counting beat is stated against the
refinement subspace of the accumulated base (with the closed-form cardinality
`C(stars base, ℓ)·2^(stars base - ℓ)`), plus the easy full-space beat used
only to index the B3 certificate type. -/
structure GeneratedRefinedStepInput (n : Nat) (base : Restriction n) where
  layer : MinimalLayeredFormula n
  w : Nat
  s : Nat
  ℓ : Nat
  width : ∀ g ∈ layer.gates, widthDNF g.theDNF ≤ w
  beatRefined : layer.gates.length *
      ((restrictionsWithStars (stars base) (ℓ - s)).card * (8 * w) ^ s) <
    (refinesSubspace base ℓ).card
  beatPlain : layer.gates.length *
      ((restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s) <
    (restrictionsWithStars n ℓ).card

namespace GeneratedRefinedStepInput

/-- Forget the renormalization (the plain full-space input indexes the B3
certificate type). -/
def toPlain {n : Nat} {base : Restriction n}
    (I : GeneratedRefinedStepInput n base) : GeneratedOneStepInput n where
  layer := I.layer
  w := I.w
  s := I.s
  ℓ := I.ℓ
  width := I.width
  beat := I.beatPlain

end GeneratedRefinedStepInput

/-- **Renormalized stage theorem.**  A refined stage input generates a full B3
certificate whose restriction REFINES the base. -/
theorem generatedRefinedOneStep_exists {n : Nat} {base : Restriction n}
    (I : GeneratedRefinedStepInput n base) :
    ∃ C : GeneratedOneStepCertificate I.toPlain, RefinesWith base C.ρ := by
  classical
  obtain ⟨ρ, hstars, href, hcollapse⟩ :=
    simultaneousCollapse_exists_refined base I.layer.gates I.w I.s I.ℓ
      I.width I.beatRefined
  exact ⟨{
    ρ := ρ
    stars := hstars
    treeOf := fun g hg => Classical.choose (hcollapse g hg)
    treeDepth := fun g hg => (Classical.choose_spec (hcollapse g hg)).1
    treeSemantics := fun g hg a ha =>
      (Classical.choose_spec (hcollapse g hg)).2 a ha
  }, href⟩

/-! ## Refined iteration plans and certificates -/

/-- Sequential refinement of a restriction list against an accumulating base. -/
def RefinesSeq {n : Nat} : Restriction n → List (Restriction n) → Prop
  | _, [] => True
  | base, ρ :: rest => RefinesWith base ρ ∧ RefinesSeq (compose base ρ) rest

theorem refinesSeq_consistentSeq {n : Nat} :
    ∀ (base : Restriction n) (ρs : List (Restriction n)),
      RefinesSeq base ρs →
        GeneratedIteratedCertificate.ConsistentSeq base ρs
  | _, [], _ => trivial
  | base, ρ :: rest, h =>
      ⟨h.1.consistentWith, refinesSeq_consistentSeq (compose base ρ) rest h.2⟩

/-- A renormalized generated collapse plan: as the B4 plan, but every stage
beat is stated against the refinement subspace of the accumulated base. -/
inductive GeneratedRefinedCollapsePlan (n : Nat) :
    Restriction n → BDFormula n → Nat → Type where
  | done (base : Restriction n) (F : BDFormula n) :
      GeneratedRefinedCollapsePlan n base F 0
  | step {d : Nat} {base : Restriction n}
      (I : GeneratedRefinedStepInput n base)
      (next : (C : GeneratedOneStepCertificate I.toPlain) →
        RefinesWith base C.ρ →
        GeneratedRefinedCollapsePlan n (compose base C.ρ) C.reducedFormula d) :
      GeneratedRefinedCollapsePlan n base I.layer.originalFormula (d + 1)

/-- A renormalized iterated certificate: one B3 certificate per stage, each
restriction refining the composition of all earlier ones. -/
inductive GeneratedRefinedIteratedCertificate (n : Nat) :
    Restriction n → BDFormula n → Nat → Type where
  | done (base : Restriction n) (F : BDFormula n) :
      GeneratedRefinedIteratedCertificate n base F 0
  | step {d : Nat} {base : Restriction n}
      (I : GeneratedRefinedStepInput n base)
      (C : GeneratedOneStepCertificate I.toPlain)
      (href : RefinesWith base C.ρ)
      (rest : GeneratedRefinedIteratedCertificate n (compose base C.ρ)
        C.reducedFormula d) :
      GeneratedRefinedIteratedCertificate n base I.layer.originalFormula (d + 1)

namespace GeneratedRefinedIteratedCertificate

def finalFormula {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedRefinedIteratedCertificate n base F d → BDFormula n
  | .done _ F => F
  | .step _ _ _ rest => rest.finalFormula

def finalComposed {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedRefinedIteratedCertificate n base F d → Restriction n
  | .done base _ => base
  | .step _ _ _ rest => rest.finalComposed

def stageRestrictions {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} :
    GeneratedRefinedIteratedCertificate n base F d → List (Restriction n)
  | .done _ _ => []
  | .step _ C _ rest => C.ρ :: rest.stageRestrictions

def stageBudgets {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedRefinedIteratedCertificate n base F d → List Nat
  | .done _ _ => []
  | .step I _ _ rest => I.s :: rest.stageBudgets

def stageStarCounts {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} : GeneratedRefinedIteratedCertificate n base F d → List Nat
  | .done _ _ => []
  | .step I _ _ rest => I.ℓ :: rest.stageStarCounts

def stageGateCounts {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} : GeneratedRefinedIteratedCertificate n base F d → List Nat
  | .done _ _ => []
  | .step I _ _ rest => I.layer.gates.length :: rest.stageGateCounts

def stageOutputs {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedRefinedIteratedCertificate n base F d → List (BDFormula n)
  | .done _ _ => []
  | .step _ C _ rest => C.reducedFormula :: rest.stageOutputs

def lastStage {n : Nat} {base : Restriction n} {F : BDFormula n} {d : Nat} :
    GeneratedRefinedIteratedCertificate n base F d →
      Option (DTree n × Nat × Nat)
  | .done _ _ => none
  | .step I C _ rest =>
      match rest.lastStage with
      | some x => some x
      | none => some (certTree C, I.layer.gates.length, I.s)

theorem stageRestrictions_length {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    cert.stageRestrictions.length = d := by
  induction cert with
  | done _base _F => rfl
  | step _I _C _href rest ih => simp [stageRestrictions, ih]

theorem agree_finalComposed_base {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a → Agree base a := by
  induction cert with
  | done base F =>
      intro a h
      exact h
  | step I C href rest ih =>
      intro a h
      simp only [finalComposed] at h
      exact agree_compose_left (ih a h)

theorem agree_finalComposed_stages {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a →
      ∀ ρ ∈ cert.stageRestrictions, Agree ρ a := by
  induction cert with
  | done base F =>
      intro a _ ρ hρ
      simp [stageRestrictions] at hρ
  | step I C href rest ih =>
      intro a h ρ hρ
      simp only [finalComposed] at h
      simp only [stageRestrictions, List.mem_cons] at hρ
      rcases hρ with rfl | hρ
      · exact agree_compose_right href.consistentWith
          (agree_finalComposed_base rest a h)
      · exact ih a h ρ hρ

theorem finalFormula_eval {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedRefinedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a →
      eval a cert.finalFormula = eval a F := by
  induction cert with
  | done base F =>
      intro a _
      rfl
  | step I C href rest ih =>
      intro a h
      simp only [finalComposed] at h
      have hcomp := agree_finalComposed_base rest a h
      have hρ : Agree C.ρ a :=
        agree_compose_right href.consistentWith hcomp
      simp only [finalFormula]
      calc eval a rest.finalFormula
          = eval a C.reducedFormula := ih a h
        _ = eval a (restrict C.ρ I.toPlain.originalFormula) :=
            C.semantic_preservation a hρ
        _ = eval a I.layer.originalFormula := eval_restrict C.ρ a _ hρ

theorem finalFormula_restrict_eval {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    ∀ a : Assignment n, Agree cert.finalComposed a →
      eval a cert.finalFormula = eval a (restrict cert.finalComposed F) := by
  intro a h
  rw [finalFormula_eval cert a h, eval_restrict cert.finalComposed a F h]

theorem finalComposed_extension {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    ∃ a : Assignment n, Agree cert.finalComposed a :=
  restriction_has_extension cert.finalComposed

theorem finalComposed_eq_foldl {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    cert.finalComposed = cert.stageRestrictions.foldl compose base := by
  induction cert with
  | done base F => rfl
  | step I C href rest ih =>
      simp only [finalComposed, stageRestrictions, List.foldl_cons]
      exact ih

theorem stageRestrictions_refinesSeq {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    RefinesSeq base cert.stageRestrictions := by
  induction cert with
  | done _base _F => trivial
  | step _I _C href rest ih => exact ⟨href, ih⟩

theorem stageRestrictions_stars {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d) :
    List.Forall₂ (fun (ρ : Restriction n) (ℓ : Nat) =>
        ρ ∈ restrictionsWithStars n ℓ)
      cert.stageRestrictions cert.stageStarCounts := by
  induction cert with
  | done _base _F => exact List.Forall₂.nil
  | step _I C _href rest ih => exact List.Forall₂.cons C.stars ih

theorem stageOutputs_depth {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedRefinedIteratedCertificate n base F d) :
    List.Forall₂ (fun (out : BDFormula n) (s : Nat) =>
        depth out ≤ 1 + (2 * (s - 1) + 1))
      cert.stageOutputs cert.stageBudgets := by
  induction cert with
  | done _base _F => exact List.Forall₂.nil
  | step _I C _href rest ih =>
      exact List.Forall₂.cons C.reducedFormula_depth_bound ih

theorem stageOutputs_size {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedRefinedIteratedCertificate n base F d) :
    List.Forall₂ (fun (out : BDFormula n) (p : Nat × Nat) =>
        formulaSize out ≤ 1 + p.1 * (6 * 2 ^ (p.2 - 1)))
      cert.stageOutputs (cert.stageGateCounts.zip cert.stageBudgets) := by
  induction cert with
  | done _base _F => exact List.Forall₂.nil
  | step _I C _href rest ih =>
      simp only [stageOutputs, stageGateCounts, stageBudgets,
        List.zip_cons_cons]
      exact List.Forall₂.cons (reducedFormula_size_le C) ih

theorem lastStage_isSome {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedRefinedIteratedCertificate n base F d)
    (hd : 0 < d) : cert.lastStage.isSome := by
  induction cert with
  | done _base _F => omega
  | step _I _C _href rest _ih =>
      simp only [lastStage]
      cases rest.lastStage with
      | some x => simp
      | none => simp

theorem finalFormula_of_lastStage_none {n : Nat} {base : Restriction n}
    {F : BDFormula n} {d : Nat}
    (cert : GeneratedRefinedIteratedCertificate n base F d)
    (h : cert.lastStage = none) : cert.finalFormula = F := by
  induction cert with
  | done _base _F => rfl
  | step _I _C _href rest _ih =>
      simp only [lastStage] at h
      cases hlast : rest.lastStage with
      | some x => rw [hlast] at h; simp at h
      | none => rw [hlast] at h; simp at h

theorem lastStage_spec {n : Nat} {base : Restriction n} {F : BDFormula n}
    {d : Nat} (cert : GeneratedRefinedIteratedCertificate n base F d) :
    ∀ T : DTree n, ∀ m s : Nat, cert.lastStage = some (T, m, s) →
      (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
        dtDepth T ≤ m * (s - 1) := by
  induction cert with
  | done _base _F =>
      intro T m s h
      simp [lastStage] at h
  | step I C _href rest ih =>
      intro T m s h
      simp only [lastStage] at h
      cases hlast : rest.lastStage with
      | some x =>
          rw [hlast] at h
          simp only [Option.some.injEq] at h
          subst h
          have hrest := ih T m s hlast
          simp only [finalFormula]
          exact hrest
      | none =>
          rw [hlast] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hfin : rest.finalFormula = C.reducedFormula :=
            finalFormula_of_lastStage_none rest hlast
          constructor
          · intro a
            simp only [finalFormula]
            rw [hfin]
            exact dtEval_certTree C a
          · exact dtDepth_certTree_le C

end GeneratedRefinedIteratedCertificate

open GeneratedRefinedIteratedCertificate

/-! ## Running a refined plan -/

theorem generatedRefinedIteratedCertificate_exists {n : Nat}
    {base : Restriction n} {F : BDFormula n} {d : Nat}
    (P : GeneratedRefinedCollapsePlan n base F d) :
    Nonempty (GeneratedRefinedIteratedCertificate n base F d) := by
  induction P with
  | done base F => exact ⟨.done base F⟩
  | step I _next ih =>
      obtain ⟨C, href⟩ := generatedRefinedOneStep_exists I
      obtain ⟨rest⟩ := ih C href
      exact ⟨.step I C href rest⟩

/-! ## The renormalized final theorem -/

/-- **The renormalized generated iterated-collapse theorem (plan-supplied
per-stage views; see the HONEST SCOPE STATEMENT above).**  As the B4 route
theorem, but with every stage beat stated against the refinement subspace of
the accumulated base (closed-form cardinality), and every generated stage
restriction REFINING the composition of all earlier ones. -/
theorem generatedRefinedIteratedCollapse {n d : Nat} {F : BDFormula n}
    (P : GeneratedRefinedCollapsePlan n (freeRestriction n) F d)
    (hd : 0 < d) :
    ∃ cert : GeneratedRefinedIteratedCertificate n (freeRestriction n) F d,
      cert.stageRestrictions.length = d ∧
      RefinesSeq (freeRestriction n) cert.stageRestrictions ∧
      GeneratedIteratedCertificate.ConsistentSeq (freeRestriction n)
        cert.stageRestrictions ∧
      cert.finalComposed =
        cert.stageRestrictions.foldl compose (freeRestriction n) ∧
      List.Forall₂ (fun (ρ : Restriction n) (ℓ : Nat) =>
          ρ ∈ restrictionsWithStars n ℓ)
        cert.stageRestrictions cert.stageStarCounts ∧
      (∃ a : Assignment n, Agree cert.finalComposed a) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        ∀ ρ ∈ cert.stageRestrictions, Agree ρ a) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        eval a cert.finalFormula = eval a (restrict cert.finalComposed F)) ∧
      (∀ a : Assignment n, Agree cert.finalComposed a →
        eval a cert.finalFormula = eval a F) ∧
      List.Forall₂ (fun (out : BDFormula n) (s : Nat) =>
          depth out ≤ 1 + (2 * (s - 1) + 1))
        cert.stageOutputs cert.stageBudgets ∧
      List.Forall₂ (fun (out : BDFormula n) (p : Nat × Nat) =>
          formulaSize out ≤ 1 + p.1 * (6 * 2 ^ (p.2 - 1)))
        cert.stageOutputs (cert.stageGateCounts.zip cert.stageBudgets) ∧
      ∃ (T : DTree n) (m s : Nat),
        cert.lastStage = some (T, m, s) ∧
        (∀ a : Assignment n, dtEval a T = eval a cert.finalFormula) ∧
        dtDepth T ≤ m * (s - 1) ∧
        (∀ a : Assignment n, Agree cert.finalComposed a →
          dtEval a T = eval a (restrict cert.finalComposed F)) := by
  obtain ⟨cert⟩ := generatedRefinedIteratedCertificate_exists P
  have hsome := lastStage_isSome cert hd
  cases hlast : cert.lastStage with
  | none => rw [hlast] at hsome; simp at hsome
  | some x =>
      obtain ⟨T, m, s⟩ := x
      obtain ⟨heval, hdepth⟩ := lastStage_spec cert T m s hlast
      refine ⟨cert, stageRestrictions_length cert,
        stageRestrictions_refinesSeq cert,
        refinesSeq_consistentSeq _ _ (stageRestrictions_refinesSeq cert),
        finalComposed_eq_foldl cert, stageRestrictions_stars cert,
        finalComposed_extension cert, agree_finalComposed_stages cert,
        finalFormula_restrict_eval cert, finalFormula_eval cert,
        stageOutputs_depth cert, stageOutputs_size cert,
        T, m, s, hlast, heval, hdepth, ?_⟩
      intro a ha
      rw [heval a, finalFormula_restrict_eval cert a ha]

end GeneratedRefinedCollapse
end PvNP
