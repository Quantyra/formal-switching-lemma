import PvNP.RefinedSubspace

/-!
# Variable relabeling for the switching counting (renormalization transport)

Relabeling machinery along a function `f : Fin n → Fin m` that is injective on
a variable-support set `S`: literals, terms, DNFs, and decision trees relabel
pointwise, and every construction in the term-canonical switching route
commutes with the relabeling:

* `assignTerm`/`assignVar` (residualization),
* `termRestrict`/`dnfRestrict` (partial restriction, against a corresponding
  pair of restrictions),
* `termCanonicalDT`/`queryTerm` (the canonical decision tree, by mirroring its
  mutual well-founded recursion), preserving `dtDepth`.

It also proves the support/width/simplicity bookkeeping used by the
renormalized bad-set bound: restriction shrinks per-term literal lists to
sublists (so width never grows and simplicity is preserved), the literals kept
by a restriction live on its star set, and a refinement's restriction factors
through the base restriction (`dnfRestrict_refinesWith`).

## HONEST SCOPE STATEMENT (read this)

* Pure syntactic transport and bookkeeping for the already-proved SimpleDNF
  switching lemma; no new probabilistic or counting content.
* Formula-collapse infrastructure only: NOT a Frege/PHP proof-size bound, NOT
  an NP/circuit bound, NOT a statement about P vs NP.  Gate A rung 4 remains
  open.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace SwitchingRelabel

open CNFModel
open BoundedDepthFrege
open BoundedDepthRestriction
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthIteratedCollapse
open GeneratedGoodRestriction
open SwitchingEncodeConstruct
open SwitchingLemmaStatement
open SwitchingTermCanonicalDT
open RestrictionComposition
open RefinedSubspace

/-! ## Relabeling maps -/

def mapLit {n m : Nat} (f : Fin n → Fin m) (l : Literal n) : Literal m :=
  ⟨f l.var, l.sign⟩

def mapTerm {n m : Nat} (f : Fin n → Fin m) (t : Term n) : Term m :=
  t.map (mapLit f)

def mapDNF {n m : Nat} (f : Fin n → Fin m) (D : DNF n) : DNF m :=
  D.map (mapTerm f)

def mapTree {n m : Nat} (f : Fin n → Fin m) : DTree n → DTree m
  | .leaf b => .leaf b
  | .node v t0 t1 => .node (f v) (mapTree f t0) (mapTree f t1)

@[simp] theorem mapTerm_nil {n m : Nat} (f : Fin n → Fin m) :
    mapTerm f ([] : Term n) = [] := rfl

@[simp] theorem mapTerm_cons {n m : Nat} (f : Fin n → Fin m) (l : Literal n)
    (t : Term n) : mapTerm f (l :: t) = mapLit f l :: mapTerm f t := rfl

@[simp] theorem mapDNF_nil {n m : Nat} (f : Fin n → Fin m) :
    mapDNF f ([] : DNF n) = [] := rfl

@[simp] theorem mapDNF_cons {n m : Nat} (f : Fin n → Fin m) (t : Term n)
    (D : DNF n) : mapDNF f (t :: D) = mapTerm f t :: mapDNF f D := rfl

theorem dtDepth_mapTree {n m : Nat} (f : Fin n → Fin m) (T : DTree n) :
    dtDepth (mapTree f T) = dtDepth T := by
  induction T with
  | leaf b => rfl
  | node _v t0 t1 ih0 ih1 => simp [mapTree, ih0, ih1]

/-! ## Variable support -/

def TermVarsIn {n : Nat} (t : Term n) (S : Finset (Fin n)) : Prop :=
  ∀ l ∈ t, l.var ∈ S

def DNFVarsIn {n : Nat} (D : DNF n) (S : Finset (Fin n)) : Prop :=
  ∀ t ∈ D, TermVarsIn t S

theorem termVarsIn_of_cons {n : Nat} {l : Literal n} {t : Term n}
    {S : Finset (Fin n)} (h : TermVarsIn (l :: t) S) : TermVarsIn t S :=
  fun l' hl' => h l' (List.mem_cons_of_mem l hl')

theorem dnfVarsIn_of_cons {n : Nat} {t : Term n} {D : DNF n}
    {S : Finset (Fin n)} (h : DNFVarsIn (t :: D) S) : DNFVarsIn D S :=
  fun t' ht' => h t' (List.mem_cons_of_mem t ht')

/-- The literals kept by `termRestrict` form a sublist of the original term. -/
theorem termRestrict_sublist {n : Nat} (ρ : Restriction n) :
    ∀ (t t' : Term n), termRestrict ρ t = some t' → t'.Sublist t := by
  intro t
  induction t with
  | nil =>
      intro t' h
      simp only [termRestrict, Option.some.injEq] at h
      subst h
      exact List.Sublist.refl []
  | cons l t ih =>
      intro t' h
      cases hρ : ρ l.var with
      | none =>
          cases hrec : termRestrict ρ t with
          | some t'' =>
              rw [show termRestrict ρ (l :: t) = some (l :: t'') by
                    simp only [termRestrict, hρ, hrec]] at h
              rw [Option.some.injEq] at h
              subst h
              exact List.Sublist.cons₂ l (ih t'' hrec)
          | none =>
              rw [show termRestrict ρ (l :: t) = none by
                    simp only [termRestrict, hρ, hrec]] at h
              cases h
      | some b =>
          by_cases hb : b = l.sign
          · rw [show termRestrict ρ (l :: t) = termRestrict ρ t by
                  simp only [termRestrict, hρ, if_pos hb]] at h
            exact List.Sublist.cons l (ih t' h)
          · rw [show termRestrict ρ (l :: t) = none by
                  simp only [termRestrict, hρ, if_neg hb]] at h
            cases h

/-- The literals kept by `assignTerm` form a sublist of the original term. -/
theorem assignTerm_sublist {n : Nat} (v : Fin n) (b : Bool) :
    ∀ (t t' : Term n), assignTerm v b t = some t' → t'.Sublist t := by
  intro t
  induction t with
  | nil =>
      intro t' h
      simp only [assignTerm, Option.some.injEq] at h
      subst h
      exact List.Sublist.refl []
  | cons l t ih =>
      intro t' h
      by_cases hlv : l.var = v
      · by_cases hls : l.sign = b
        · rw [show assignTerm v b (l :: t) = assignTerm v b t by
                simp only [assignTerm, if_pos hlv, if_pos hls]] at h
          exact List.Sublist.cons l (ih t' h)
        · rw [show assignTerm v b (l :: t) = none by
                simp only [assignTerm, if_pos hlv, if_neg hls]] at h
          cases h
      · cases hrec : assignTerm v b t with
        | some t'' =>
            rw [show assignTerm v b (l :: t) = some (l :: t'') by
                  simp only [assignTerm, if_neg hlv, hrec]] at h
            rw [Option.some.injEq] at h
            subst h
            exact List.Sublist.cons₂ l (ih t'' hrec)
        | none =>
            rw [show assignTerm v b (l :: t) = none by
                  simp only [assignTerm, if_neg hlv, hrec]] at h
            cases h

theorem termVarsIn_of_sublist {n : Nat} {t t' : Term n} {S : Finset (Fin n)}
    (hsub : t'.Sublist t) (h : TermVarsIn t S) : TermVarsIn t' S :=
  fun l hl => h l (hsub.mem hl)

theorem dnfVarsIn_assignVar {n : Nat} {D : DNF n} {S : Finset (Fin n)}
    (h : DNFVarsIn D S) (v : Fin n) (b : Bool) :
    DNFVarsIn (assignVar v b D) S := by
  intro t' ht'
  rw [assignVar, List.mem_filterMap] at ht'
  obtain ⟨t, ht, hassign⟩ := ht'
  exact termVarsIn_of_sublist (assignTerm_sublist v b t t' hassign) (h t ht)

theorem dnfVarsIn_dnfRestrict {n : Nat} {D : DNF n} {S : Finset (Fin n)}
    (h : DNFVarsIn D S) (ρ : Restriction n) :
    DNFVarsIn (dnfRestrict ρ D) S := by
  intro t' ht'
  rw [dnfRestrict, List.mem_filterMap] at ht'
  obtain ⟨t, ht, hrestrict⟩ := ht'
  exact termVarsIn_of_sublist (termRestrict_sublist ρ t t' hrestrict) (h t ht)

/-- The literals kept by a restriction live on its star set. -/
theorem dnfVarsIn_starSet_dnfRestrict {n : Nat} (ρ : Restriction n)
    (D : DNF n) : DNFVarsIn (dnfRestrict ρ D) (starSet ρ) := by
  intro t' ht'
  rw [dnfRestrict, List.mem_filterMap] at ht'
  obtain ⟨t, hmem, hrestrict⟩ := ht'
  clear hmem
  induction t generalizing t' with
  | nil =>
      simp only [termRestrict, Option.some.injEq] at hrestrict
      subst hrestrict
      intro l hl
      cases hl
  | cons l t ih =>
      cases hρ : ρ l.var with
      | none =>
          cases hrec : termRestrict ρ t with
          | some t'' =>
              rw [show termRestrict ρ (l :: t) = some (l :: t'') by
                    simp only [termRestrict, hρ, hrec]] at hrestrict
              rw [Option.some.injEq] at hrestrict
              subst hrestrict
              intro l' hl'
              rcases List.mem_cons.mp hl' with rfl | hl'
              · rw [mem_starSet]
                exact hρ
              · exact ih t'' hrec l' hl'
          | none =>
              rw [show termRestrict ρ (l :: t) = none by
                    simp only [termRestrict, hρ, hrec]] at hrestrict
              cases hrestrict
      | some b =>
          by_cases hb : b = l.sign
          · rw [show termRestrict ρ (l :: t) = termRestrict ρ t by
                  simp only [termRestrict, hρ, if_pos hb]] at hrestrict
            exact ih t' hrestrict
          · rw [show termRestrict ρ (l :: t) = none by
                  simp only [termRestrict, hρ, if_neg hb]] at hrestrict
            cases hrestrict

/-! ## Width and simplicity bookkeeping -/

theorem simpleDNF_dnfRestrict {n : Nat} (ρ : Restriction n) {D : DNF n}
    (h : SimpleDNF D) : SimpleDNF (dnfRestrict ρ D) := by
  intro t' ht'
  rw [dnfRestrict, List.mem_filterMap] at ht'
  obtain ⟨t, ht, hrestrict⟩ := ht'
  have hsub := termRestrict_sublist ρ t t' hrestrict
  exact List.Nodup.sublist (hsub.map (·.var)) (h t ht)

theorem widthDNF_mapDNF {n m : Nat} (f : Fin n → Fin m) (D : DNF n) :
    widthDNF (mapDNF f D) = widthDNF D := by
  induction D with
  | nil => rfl
  | cons t D ih =>
      simp only [mapDNF_cons, widthDNF_cons, ih, termWidth, mapTerm,
        List.length_map]

theorem simpleDNF_mapDNF {n m : Nat} (f : Fin n → Fin m) {S : Finset (Fin n)}
    (hinj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v) {D : DNF n}
    (hD : DNFVarsIn D S) (h : SimpleDNF D) : SimpleDNF (mapDNF f D) := by
  intro t' ht'
  rw [mapDNF, List.mem_map] at ht'
  obtain ⟨t, ht, rfl⟩ := ht'
  show ((mapTerm f t).map (·.var)).Nodup
  have hmap : (mapTerm f t).map (·.var) = (t.map (·.var)).map f := by
    simp [mapTerm, mapLit, List.map_map, Function.comp_def]
  rw [hmap]
  apply List.Nodup.map_on
  · intro u hu v hv huv
    rw [List.mem_map] at hu hv
    obtain ⟨lu, hlu, rfl⟩ := hu
    obtain ⟨lv, hlv, rfl⟩ := hv
    exact hinj lu.var (hD t ht lu hlu) lv.var (hD t ht lv hlv) huv
  · exact h t ht

/-! ## Relabeling commutes with residualization and restriction -/

theorem assignTerm_mapTerm {n m : Nat} (f : Fin n → Fin m)
    {S : Finset (Fin n)} (hinj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v)
    (v : Fin n) (hv : v ∈ S) (b : Bool) :
    ∀ (t : Term n), TermVarsIn t S →
      assignTerm (f v) b (mapTerm f t) = (assignTerm v b t).map (mapTerm f) := by
  intro t
  induction t with
  | nil =>
      intro _
      simp [assignTerm]
  | cons l t ih =>
      intro hvars
      have hl : l.var ∈ S := hvars l (List.mem_cons_self l t)
      have ht := termVarsIn_of_cons hvars
      rw [mapTerm_cons]
      by_cases hlv : l.var = v
      · have hfl : (mapLit f l).var = f v := congrArg f hlv
        by_cases hls : l.sign = b
        · have hfls : (mapLit f l).sign = b := hls
          rw [show assignTerm v b (l :: t) = assignTerm v b t by
                simp only [assignTerm, if_pos hlv, if_pos hls]]
          rw [show assignTerm (f v) b (mapLit f l :: mapTerm f t)
                = assignTerm (f v) b (mapTerm f t) by
              simp only [assignTerm, if_pos hfl, if_pos hfls]]
          exact ih ht
        · have hfls : ¬((mapLit f l).sign = b) := hls
          rw [show assignTerm v b (l :: t) = none by
                simp only [assignTerm, if_pos hlv, if_neg hls]]
          rw [show assignTerm (f v) b (mapLit f l :: mapTerm f t) = none by
              simp only [assignTerm, if_pos hfl, if_neg hfls]]
          rfl
      · have hfl : ¬((mapLit f l).var = f v) := fun hcontra =>
          hlv (hinj l.var hl v hv hcontra)
        cases hrec : assignTerm v b t with
        | some t' =>
            have hrec' : assignTerm (f v) b (mapTerm f t)
                = some (mapTerm f t') := by
              rw [ih ht, hrec, Option.map_some']
            rw [show assignTerm v b (l :: t) = some (l :: t') by
                  simp only [assignTerm, if_neg hlv, hrec]]
            rw [show assignTerm (f v) b (mapLit f l :: mapTerm f t)
                  = some (mapLit f l :: mapTerm f t') by
                simp only [assignTerm, if_neg hfl, hrec']]
            rfl
        | none =>
            have hrec' : assignTerm (f v) b (mapTerm f t) = none := by
              rw [ih ht, hrec, Option.map_none']
            rw [show assignTerm v b (l :: t) = none by
                  simp only [assignTerm, if_neg hlv, hrec]]
            rw [show assignTerm (f v) b (mapLit f l :: mapTerm f t) = none by
                simp only [assignTerm, if_neg hfl, hrec']]
            rfl

theorem assignVar_mapDNF {n m : Nat} (f : Fin n → Fin m)
    {S : Finset (Fin n)} (hinj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v)
    (v : Fin n) (hv : v ∈ S) (b : Bool) :
    ∀ (D : DNF n), DNFVarsIn D S →
      assignVar (f v) b (mapDNF f D) = mapDNF f (assignVar v b D) := by
  intro D
  induction D with
  | nil =>
      intro _
      rfl
  | cons t D ih =>
      intro hD
      have ht := hD t (List.mem_cons_self t D)
      have hD' := dnfVarsIn_of_cons hD
      rw [mapDNF_cons]
      rw [show assignVar (f v) b (mapTerm f t :: mapDNF f D)
            = (match assignTerm (f v) b (mapTerm f t) with
                | some t' => t' :: assignVar (f v) b (mapDNF f D)
                | none => assignVar (f v) b (mapDNF f D)) by
          simp only [assignVar, List.filterMap_cons]
          cases assignTerm (f v) b (mapTerm f t) <;> rfl]
      rw [show assignVar v b (t :: D)
            = (match assignTerm v b t with
                | some t' => t' :: assignVar v b D
                | none => assignVar v b D) by
          simp only [assignVar, List.filterMap_cons]
          cases assignTerm v b t <;> rfl]
      rw [assignTerm_mapTerm f hinj v hv b t ht]
      cases assignTerm v b t with
      | some t' => simp only [Option.map_some', mapDNF_cons, ih hD']
      | none => simp only [Option.map_none', ih hD']

theorem termRestrict_mapTerm {n m : Nat} (f : Fin n → Fin m)
    {S : Finset (Fin n)} (ρ : Restriction n) (σ : Restriction m)
    (hcorr : ∀ v ∈ S, σ (f v) = ρ v) :
    ∀ (t : Term n), TermVarsIn t S →
      termRestrict σ (mapTerm f t) = (termRestrict ρ t).map (mapTerm f) := by
  intro t
  induction t with
  | nil =>
      intro _
      simp [termRestrict]
  | cons l t ih =>
      intro hvars
      have hl : l.var ∈ S := hvars l (List.mem_cons_self l t)
      have ht := termVarsIn_of_cons hvars
      have hσ : σ (f l.var) = ρ l.var := hcorr l.var hl
      rw [mapTerm_cons]
      cases hρ : ρ l.var with
      | none =>
          have hσ' : σ ((mapLit f l).var) = none := by
            rw [show (mapLit f l).var = f l.var from rfl, hσ, hρ]
          cases hrec : termRestrict ρ t with
          | some t' =>
              have hrec' : termRestrict σ (mapTerm f t)
                  = some (mapTerm f t') := by
                rw [ih ht, hrec, Option.map_some']
              rw [show termRestrict ρ (l :: t) = some (l :: t') by
                    simp only [termRestrict, hρ, hrec]]
              rw [show termRestrict σ (mapLit f l :: mapTerm f t)
                    = some (mapLit f l :: mapTerm f t') by
                  simp only [termRestrict, hσ', hrec']]
              rfl
          | none =>
              have hrec' : termRestrict σ (mapTerm f t) = none := by
                rw [ih ht, hrec, Option.map_none']
              rw [show termRestrict ρ (l :: t) = none by
                    simp only [termRestrict, hρ, hrec]]
              rw [show termRestrict σ (mapLit f l :: mapTerm f t) = none by
                  simp only [termRestrict, hσ', hrec']]
              rfl
      | some b =>
          have hσ' : σ ((mapLit f l).var) = some b := by
            rw [show (mapLit f l).var = f l.var from rfl, hσ, hρ]
          by_cases hb : b = l.sign
          · have hbf : b = (mapLit f l).sign := hb
            rw [show termRestrict σ (mapLit f l :: mapTerm f t)
                  = termRestrict σ (mapTerm f t) by
                simp only [termRestrict, hσ', if_pos hbf]]
            rw [show termRestrict ρ (l :: t) = termRestrict ρ t by
                simp only [termRestrict, hρ, if_pos hb]]
            exact ih ht
          · have hbf : ¬(b = (mapLit f l).sign) := hb
            rw [show termRestrict σ (mapLit f l :: mapTerm f t) = none by
                simp only [termRestrict, hσ', if_neg hbf]]
            rw [show termRestrict ρ (l :: t) = none by
                simp only [termRestrict, hρ, if_neg hb]]
            rfl

theorem dnfRestrict_mapDNF {n m : Nat} (f : Fin n → Fin m)
    {S : Finset (Fin n)} (ρ : Restriction n) (σ : Restriction m)
    (hcorr : ∀ v ∈ S, σ (f v) = ρ v) :
    ∀ (D : DNF n), DNFVarsIn D S →
      dnfRestrict σ (mapDNF f D) = mapDNF f (dnfRestrict ρ D) := by
  intro D
  induction D with
  | nil =>
      intro _
      rfl
  | cons t D ih =>
      intro hD
      have ht := hD t (List.mem_cons_self t D)
      have hD' := dnfVarsIn_of_cons hD
      rw [mapDNF_cons]
      rw [show dnfRestrict σ (mapTerm f t :: mapDNF f D)
            = (match termRestrict σ (mapTerm f t) with
                | some t' => t' :: dnfRestrict σ (mapDNF f D)
                | none => dnfRestrict σ (mapDNF f D)) by
          simp only [dnfRestrict, List.filterMap_cons]
          cases termRestrict σ (mapTerm f t) <;> rfl]
      rw [show dnfRestrict ρ (t :: D)
            = (match termRestrict ρ t with
                | some t' => t' :: dnfRestrict ρ D
                | none => dnfRestrict ρ D) by
          simp only [dnfRestrict, List.filterMap_cons]
          cases termRestrict ρ t <;> rfl]
      rw [termRestrict_mapTerm f ρ σ hcorr t ht]
      cases termRestrict ρ t with
      | some t' => simp only [Option.map_some', mapDNF_cons, ih hD']
      | none => simp only [Option.map_none', ih hD']

/-! ## A refinement's restriction factors through the base -/

theorem termRestrict_refinesWith {n : Nat} {base ρ : Restriction n}
    (h : RefinesWith base ρ) :
    ∀ (t : Term n),
      termRestrict ρ t = (termRestrict base t).bind (termRestrict ρ) := by
  intro t
  induction t with
  | nil => simp [termRestrict]
  | cons l t ih =>
      cases hb : base l.var with
      | some b =>
          have hρl : ρ l.var = some b := h l.var b hb
          by_cases hbs : b = l.sign
          · rw [show termRestrict base (l :: t) = termRestrict base t by
                  simp only [termRestrict, hb, if_pos hbs]]
            rw [show termRestrict ρ (l :: t) = termRestrict ρ t by
                  simp only [termRestrict, hρl, if_pos hbs]]
            exact ih
          · rw [show termRestrict base (l :: t) = none by
                  simp only [termRestrict, hb, if_neg hbs]]
            rw [show termRestrict ρ (l :: t) = none by
                  simp only [termRestrict, hρl, if_neg hbs]]
            rfl
      | none =>
          cases hbase : termRestrict base t with
          | none =>
              have hbcons : termRestrict base (l :: t) = none := by
                simp only [termRestrict, hb, hbase]
              have hrt : termRestrict ρ t = none := by
                rw [ih, hbase]
                rfl
              have hLHS : termRestrict ρ (l :: t) = none := by
                cases hρl : ρ l.var with
                | none => simp only [termRestrict, hρl, hrt]
                | some c =>
                    by_cases hcs : c = l.sign
                    · simp only [termRestrict, hρl, if_pos hcs]
                      exact hrt
                    · simp only [termRestrict, hρl, if_neg hcs]
              rw [hLHS, hbcons]
              rfl
          | some tb =>
              have hbcons : termRestrict base (l :: t) = some (l :: tb) := by
                simp only [termRestrict, hb, hbase]
              have hrt : termRestrict ρ t = termRestrict ρ tb := by
                rw [ih, hbase]
                rfl
              rw [hbcons, Option.some_bind]
              cases hρl : ρ l.var with
              | none =>
                  cases hrtb : termRestrict ρ tb with
                  | some t' =>
                      have hrt' : termRestrict ρ t = some t' := by
                        rw [hrt, hrtb]
                      rw [show termRestrict ρ (l :: t) = some (l :: t') by
                            simp only [termRestrict, hρl, hrt']]
                      rw [show termRestrict ρ (l :: tb) = some (l :: t') by
                            simp only [termRestrict, hρl, hrtb]]
                  | none =>
                      have hrt' : termRestrict ρ t = none := by
                        rw [hrt, hrtb]
                      rw [show termRestrict ρ (l :: t) = none by
                            simp only [termRestrict, hρl, hrt']]
                      rw [show termRestrict ρ (l :: tb) = none by
                            simp only [termRestrict, hρl, hrtb]]
              | some c =>
                  by_cases hcs : c = l.sign
                  · rw [show termRestrict ρ (l :: t) = termRestrict ρ t by
                        simp only [termRestrict, hρl, if_pos hcs]]
                    rw [show termRestrict ρ (l :: tb) = termRestrict ρ tb by
                        simp only [termRestrict, hρl, if_pos hcs]]
                    exact hrt
                  · rw [show termRestrict ρ (l :: t) = none by
                        simp only [termRestrict, hρl, if_neg hcs]]
                    rw [show termRestrict ρ (l :: tb) = none by
                        simp only [termRestrict, hρl, if_neg hcs]]

/-- **Factoring through the base.**  A refinement restricts a DNF exactly as
the base restriction followed by the refinement. -/
theorem dnfRestrict_refinesWith {n : Nat} {base ρ : Restriction n}
    (h : RefinesWith base ρ) (D : DNF n) :
    dnfRestrict ρ D = dnfRestrict ρ (dnfRestrict base D) := by
  induction D with
  | nil => rfl
  | cons t D ih =>
      have hstep : ∀ (τ : Restriction n) (u : Term n) (E : DNF n),
          dnfRestrict τ (u :: E)
            = (match termRestrict τ u with
                | some u' => u' :: dnfRestrict τ E
                | none => dnfRestrict τ E) := by
        intro τ u E
        simp only [dnfRestrict, List.filterMap_cons]
        cases termRestrict τ u <;> rfl
      rw [hstep ρ t D]
      have hfact := termRestrict_refinesWith h t
      cases hbase : termRestrict base t with
      | none =>
          have hrt : termRestrict ρ t = none := by
            rw [hfact, hbase]
            rfl
          simp only [hrt]
          rw [show dnfRestrict base (t :: D) = dnfRestrict base D by
                rw [hstep base t D, hbase]]
          exact ih
      | some tb =>
          have hrt : termRestrict ρ t = termRestrict ρ tb := by
            rw [hfact, hbase]
            rfl
          rw [show dnfRestrict base (t :: D) = tb :: dnfRestrict base D by
                rw [hstep base t D, hbase]]
          rw [hstep ρ tb (dnfRestrict base D)]
          rw [hrt, ih]

/-! ## Relabeling commutes with the canonical decision tree -/

mutual
/-- Relabeling along a support-injective map commutes with the term-canonical
decision tree (mirrors the `termCanonicalDT`/`queryTerm` recursion). -/
theorem termCanonicalDT_mapDNF {n m : Nat} (f : Fin n → Fin m)
    (S : Finset (Fin n)) (hinj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v) :
    ∀ (D : DNF n), DNFVarsIn D S →
      termCanonicalDT (mapDNF f D) = mapTree f (termCanonicalDT D)
  | [], _ => by
      rw [mapDNF_nil]
      rw [show termCanonicalDT ([] : DNF n) = DTree.leaf false from by
        rw [termCanonicalDT]]
      rw [show termCanonicalDT ([] : DNF m) = DTree.leaf false from by
        rw [termCanonicalDT]]
      rfl
  | [] :: D, _ => by
      rw [mapDNF_cons, mapTerm_nil]
      rw [show termCanonicalDT (([] : Term n) :: D) = DTree.leaf true from by
        rw [termCanonicalDT]]
      rw [show termCanonicalDT (([] : Term m) :: mapDNF f D) = DTree.leaf true
        from by rw [termCanonicalDT]]
      rfl
  | (l :: t) :: D, hD => by
      have hl : l.var ∈ S :=
        hD (l :: t) (List.mem_cons_self _ _) l (List.mem_cons_self l t)
      have ht : TermVarsIn t S :=
        termVarsIn_of_cons (hD (l :: t) (List.mem_cons_self _ _))
      rw [mapDNF_cons, mapTerm_cons]
      rw [show termCanonicalDT ((mapLit f l :: mapTerm f t) :: mapDNF f D)
            = DTree.node (mapLit f l).var
                (queryTerm (mapTerm f t) (assignVar (mapLit f l).var false
                  ((mapLit f l :: mapTerm f t) :: mapDNF f D)))
                (queryTerm (mapTerm f t) (assignVar (mapLit f l).var true
                  ((mapLit f l :: mapTerm f t) :: mapDNF f D))) from by
          rw [termCanonicalDT]]
      rw [show termCanonicalDT ((l :: t) :: D)
            = DTree.node l.var
                (queryTerm t (assignVar l.var false ((l :: t) :: D)))
                (queryTerm t (assignVar l.var true ((l :: t) :: D))) from by
          rw [termCanonicalDT]]
      have hmap : (mapLit f l :: mapTerm f t) :: mapDNF f D
          = mapDNF f ((l :: t) :: D) := by
        rw [mapDNF_cons, mapTerm_cons]
      rw [show (mapLit f l).var = f l.var from rfl, hmap]
      rw [assignVar_mapDNF f hinj l.var hl false ((l :: t) :: D) hD]
      rw [assignVar_mapDNF f hinj l.var hl true ((l :: t) :: D) hD]
      rw [queryTerm_mapDNF f S hinj t (assignVar l.var false ((l :: t) :: D))
        ht (dnfVarsIn_assignVar hD l.var false)]
      rw [queryTerm_mapDNF f S hinj t (assignVar l.var true ((l :: t) :: D))
        ht (dnfVarsIn_assignVar hD l.var true)]
      rfl
  termination_by D => (dnfSize D, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var false l t D rfl)
    · exact Prod.Lex.left _ _ (dnfSize_assignVar_lt l.var true l t D rfl)

/-- Relabeling commutes with the canonical-tree block helper. -/
theorem queryTerm_mapDNF {n m : Nat} (f : Fin n → Fin m)
    (S : Finset (Fin n)) (hinj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v) :
    ∀ (vs : Term n) (D : DNF n), TermVarsIn vs S → DNFVarsIn D S →
      queryTerm (mapTerm f vs) (mapDNF f D) = mapTree f (queryTerm vs D)
  | [], D, _, hD => by
      rw [mapTerm_nil]
      rw [show queryTerm ([] : Term m) (mapDNF f D)
            = termCanonicalDT (mapDNF f D) from by rw [queryTerm]]
      rw [show queryTerm ([] : Term n) D = termCanonicalDT D from by
        rw [queryTerm]]
      exact termCanonicalDT_mapDNF f S hinj D hD
  | l :: vs, D, hvs, hD => by
      have hl : l.var ∈ S := hvs l (List.mem_cons_self l vs)
      have hvs' : TermVarsIn vs S := termVarsIn_of_cons hvs
      rw [mapTerm_cons]
      rw [show queryTerm (mapLit f l :: mapTerm f vs) (mapDNF f D)
            = DTree.node (mapLit f l).var
                (queryTerm (mapTerm f vs)
                  (assignVar (mapLit f l).var false (mapDNF f D)))
                (queryTerm (mapTerm f vs)
                  (assignVar (mapLit f l).var true (mapDNF f D))) from by
          rw [queryTerm]]
      rw [show queryTerm (l :: vs) D
            = DTree.node l.var
                (queryTerm vs (assignVar l.var false D))
                (queryTerm vs (assignVar l.var true D)) from by
          rw [queryTerm]]
      rw [show (mapLit f l).var = f l.var from rfl]
      rw [assignVar_mapDNF f hinj l.var hl false D hD]
      rw [assignVar_mapDNF f hinj l.var hl true D hD]
      rw [queryTerm_mapDNF f S hinj vs (assignVar l.var false D) hvs'
        (dnfVarsIn_assignVar hD l.var false)]
      rw [queryTerm_mapDNF f S hinj vs (assignVar l.var true D) hvs'
        (dnfVarsIn_assignVar hD l.var true)]
      rfl
  termination_by vs D => (dnfSize D, vs.length + 1)
  decreasing_by
    all_goals
      first
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var false D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right' _ (dnfSize_assignVar_le l.var true D)
            (by simp only [List.length_cons]; omega)
        | exact Prod.Lex.right _ (by simp only [List.length_nil]; omega)
end

/-- The canonical-tree depth is invariant under support-injective relabeling. -/
theorem dtDepth_termCanonicalDT_mapDNF {n m : Nat} (f : Fin n → Fin m)
    (S : Finset (Fin n)) (hinj : ∀ u ∈ S, ∀ v ∈ S, f u = f v → u = v)
    (D : DNF n) (hD : DNFVarsIn D S) :
    dtDepth (termCanonicalDT (mapDNF f D)) = dtDepth (termCanonicalDT D) := by
  rw [termCanonicalDT_mapDNF f S hinj D hD, dtDepth_mapTree]

end SwitchingRelabel
end PvNP
