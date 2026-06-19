import PvNP.BoundedDepthCanonicalDT
import PvNP.BoundedDepthCanonicalDTDepth
import PvNP.BoundedDepthRestriction
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Card

/-!
# The counting framework and PRECISE STATEMENT of the Håstad/Razborov switching lemma

This file is the **setup brick** for a Håstad/Razborov-style switching lemma over
the existing bounded-depth Frege foundation.  It builds the *counting framework*
(restriction sets, star counts, widths, the "bad set" of restrictions that fail
to collapse to a shallow decision tree) and writes down the **precise statement**
of the switching lemma as an *isolated `Prop`*.  It then proves the genuinely easy
structural lemmas — most importantly the real semantic-correctness lemma for
restriction of a DNF.

## HONEST SCOPE STATEMENT (read this)
This is the switching-lemma **SETUP + STATEMENT**, nothing more:

* It **DEFINES** the combinatorial objects (DNF restriction, width, star count,
  restriction sets, the bad set) and **STATES** the switching lemma as a `Prop`
  named `SwitchingLemma`.
* `SwitchingLemma` is an **isolated, UNPROVEN `def : Prop`** — it is **NOT** an
  `axiom`, **NOT** asserted true anywhere, and **NOT** proved here.  It is the
  TARGET of a later "main injection/counting" brick, exactly analogous to how
  `DagNarrows` was isolated *as a definition* before being proved in a separate
  effort.  Nothing in this file (or that this file lets through) depends on its
  truth.
* The only real theorem of substance here is `dnfEval_dnfRestrict`, the genuine
  semantic correctness of DNF restriction:
  `dnfEval a (dnfRestrict ρ D) = dnfEval a D` whenever the total assignment `a`
  agrees with (extends) the partial restriction `ρ`.  No proxy, no weakening.

This file does **NOT** prove the switching lemma, does **NOT** prove any lower
bound, and does **NOT** claim P ≠ NP.

Reused, unchanged, from earlier bricks:
* `DNF n`, `Term n`, `dnfEval`, `termEval`, `assignVar`, `dnfEval_assignVar`,
  `canonicalDT`, `dnfSize` from `PvNP.BoundedDepthCanonicalDT`;
* `dtDepth_canonicalDT_le` from `PvNP.BoundedDepthCanonicalDTDepth`;
* `dtDepth` from `PvNP.BoundedDepthDecisionTree`;
* `Restriction n = Fin n → Option Bool`, `Agree` from
  `PvNP.BoundedDepthRestriction`;
* `Assignment n`, `Literal n`, `litEval` from `PvNP.CNFModel`.
-/

namespace PvNP
namespace SwitchingLemmaStatement

open CNFModel
open BoundedDepthDecisionTree
open BoundedDepthCanonicalDT
open BoundedDepthRestriction

/-! ## 1. Restriction of a whole DNF

We restrict a DNF by a *partial* restriction `ρ : Restriction n = Fin n → Option
Bool`.  A single term is processed by `termRestrict`:

* a literal whose variable is **fixed and falsified** by `ρ` kills the whole term
  → `none`;
* a literal whose variable is **fixed and satisfied** by `ρ` is dropped (it is
  constantly true);
* a literal whose variable is **free** (`ρ l.var = none`) survives unchanged.

A term that is entirely satisfied collapses to `[]` (the constant-true term).  The
whole DNF is then `List.filterMap termRestrict` — falsified terms vanish. -/

/-- Restrict a single term under the partial restriction `ρ`.  Returns `none` if
the term is falsified (some literal is fixed against its sign); otherwise `some`
of the term with all fixed-and-satisfied literals dropped and all free literals
kept. -/
def termRestrict {n : Nat} (ρ : Restriction n) : Term n → Option (Term n)
  | [] => some []
  | l :: t =>
      match ρ l.var with
      | none =>
          -- free variable: keep the literal
          match termRestrict ρ t with
          | some t' => some (l :: t')
          | none => none
      | some b =>
          if b = l.sign then
            -- literal satisfied by the fixing: drop it
            termRestrict ρ t
          else
            -- literal falsified by the fixing: term dies
            none

/-- Restrict a whole DNF under the partial restriction `ρ`: restrict every term
and drop the falsified ones. -/
def dnfRestrict {n : Nat} (ρ : Restriction n) (D : DNF n) : DNF n :=
  D.filterMap (termRestrict ρ)

/-! ## 2. Semantic correctness of DNF restriction

The load-bearing structural lemma: for any total assignment `a` that *agrees*
with `ρ` (extends every fixing of `ρ`), restricting `D` by `ρ` does not change
its Boolean value under `a`. -/

/-- A fixed-and-satisfied literal is invisible to `termEval` under an agreeing
`a`; a fixed-and-falsified literal makes the term false (matching `none`). -/
theorem termEval_termRestrict {n : Nat} (ρ : Restriction n) (a : Assignment n)
    (h : Agree ρ a) (t : Term n) :
    (match termRestrict ρ t with
      | some t' => termEval a t'
      | none => false) = termEval a t := by
  induction t with
  | nil => simp [termRestrict]
  | cons l t ih =>
      cases hρ : ρ l.var with
      | none =>
          -- free variable: literal kept; recurse
          cases hrec : termRestrict ρ t with
          | some t' =>
              rw [show termRestrict ρ (l :: t) = some (l :: t') by
                    simp only [termRestrict, hρ, hrec]]
              simp only [hrec] at ih
              simp only [termEval_cons]
              rw [ih]
          | none =>
              rw [show termRestrict ρ (l :: t) = none by
                    simp only [termRestrict, hρ, hrec]]
              simp only [hrec] at ih
              simp only [termEval_cons]
              rw [← ih]
              simp
      | some b =>
          -- fixed variable: `a l.var = b` by agreement
          have hab : a l.var = b := h l.var b hρ
          by_cases hbs : b = l.sign
          · -- satisfied: literal dropped
            rw [show termRestrict ρ (l :: t) = termRestrict ρ t by
                  simp only [termRestrict, hρ, if_pos hbs]]
            rw [ih]
            have hlit : litEval a l = true := by
              simp only [litEval]
              cases hs : l.sign <;> simp_all
            simp [termEval_cons, hlit]
          · -- falsified: term dies
            rw [show termRestrict ρ (l :: t) = none by
                  simp only [termRestrict, hρ, if_neg hbs]]
            have hlit : litEval a l = false := by
              simp only [litEval]
              cases hs : l.sign <;> simp_all
            simp [termEval_cons, hlit]

/-- **`dnfEval_dnfRestrict` — the load-bearing semantic correctness lemma.**
When the total assignment `a` agrees with (extends) the partial restriction `ρ`,
restricting the whole DNF by `ρ` leaves its Boolean value under `a` unchanged:
`dnfEval a (dnfRestrict ρ D) = dnfEval a D`.  This is the genuine, unweakened
semantic correctness — no proxy. -/
theorem dnfEval_dnfRestrict {n : Nat} (ρ : Restriction n) (a : Assignment n)
    (h : Agree ρ a) (D : DNF n) :
    dnfEval a (dnfRestrict ρ D) = dnfEval a D := by
  induction D with
  | nil => simp [dnfRestrict]
  | cons t D ih =>
      rw [show dnfRestrict ρ (t :: D)
            = (match termRestrict ρ t with
                | some t' => t' :: dnfRestrict ρ D
                | none => dnfRestrict ρ D) by
            simp only [dnfRestrict, List.filterMap_cons]
            cases termRestrict ρ t <;> rfl]
      have hterm := termEval_termRestrict ρ a h t
      cases hrec : termRestrict ρ t with
      | some t' =>
          simp only [hrec] at hterm
          simp only [dnfEval_cons, ih, hterm]
      | none =>
          simp only [hrec] at hterm
          simp only [dnfEval_cons, ih, ← hterm, Bool.false_or]

/-! ## 3. Widths and star counts -/

/-- The width of a term: its number of literals. -/
def termWidth {n : Nat} (t : Term n) : Nat := t.length

/-- The width of a DNF: the maximum width over its terms (`0` for the empty
DNF). -/
def widthDNF {n : Nat} (D : DNF n) : Nat :=
  (D.map termWidth).foldr max 0

@[simp] theorem widthDNF_nil {n : Nat} : widthDNF ([] : DNF n) = 0 := rfl

@[simp] theorem widthDNF_cons {n : Nat} (t : Term n) (D : DNF n) :
    widthDNF (t :: D) = max (termWidth t) (widthDNF D) := by
  simp [widthDNF]

/-- The number of **stars** (free variables) of a restriction: the count of
variables `v` with `ρ v = none`. -/
noncomputable def stars {n : Nat} (ρ : Restriction n) : Nat :=
  (Finset.univ.filter (fun v => ρ v = none)).card

/-! ## 4. Restriction sets and the bad set

`Restriction n = Fin n → Option Bool` is a `Fintype` (a finite function type into
a `Fintype`), so `Finset.univ : Finset (Restriction n)` exists.  We work
classically for the decidability of the filtering predicates. -/

/-- `Restriction n = Fin n → Option Bool` is a finite function type into the
`Fintype` `Option Bool`, hence itself a `Fintype`.  Since `Restriction` is a
`def` (not reducible), we expose the instance explicitly so `Finset.univ` over
restrictions is available. -/
instance instFintypeRestriction (n : Nat) :
    Fintype (Restriction n) :=
  inferInstanceAs (Fintype (Fin n → Option Bool))

open Classical in
/-- All restrictions on `Fin n` with exactly `ℓ` stars (free variables). -/
noncomputable def restrictionsWithStars (n ℓ : Nat) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ => stars ρ = ℓ)

open Classical in
/-- The **bad set**: restrictions with exactly `ℓ` stars whose restricted DNF has
canonical decision tree of depth `≥ s` (i.e. it fails to collapse to a tree of
depth `< s`).  Bounding the size of this set is exactly the content of the
switching lemma. -/
noncomputable def badSet {n : Nat} (D : DNF n) (s ℓ : Nat) :
    Finset (Restriction n) :=
  (restrictionsWithStars n ℓ).filter
    (fun ρ => s ≤ dtDepth (canonicalDT (dnfRestrict ρ D)))

/-! ## 5. THE STATEMENT (isolated `Prop`, NOT asserted, NOT an axiom)

The switching lemma in counting form.  For a width-`≤ w` DNF, the number of
restrictions with `ℓ` stars whose restricted canonical decision tree is deep
(depth `≥ s`) is bounded by the number of restrictions with `ℓ - s` stars times
`(8·w)^s`.  This is the standard Håstad/Razborov shape:

  #(bad restrictions, ℓ stars)  ≤  #(restrictions, ℓ−s stars) · (8·w)^s

The constant `8` is a clean placeholder for the standard absolute constant; the
ESSENTIAL content is the form "# bad ≤ # restrictions-with-fewer-stars · (c·w)^s".

**INTEGRITY.**  `SwitchingLemma` is a *definition* of a `Prop` — the TARGET to be
proved by a later brick.  It is **isolated and UNPROVEN here**: it is NOT an
`axiom`, it is NOT asserted true anywhere in this development, and nothing depends
on its truth.  This is exactly the `DagNarrows`-style isolation: state precisely,
prove later. -/
def SwitchingLemma (n : Nat) : Prop :=
  ∀ (D : DNF n) (w s ℓ : Nat), widthDNF D ≤ w →
    (badSet D s ℓ).card ≤ (restrictionsWithStars n (ℓ - s)).card * (8 * w) ^ s

/-! ## 6. Easy structural lemmas (proved; NOT the switching lemma itself) -/

/-- `widthDNF` is monotone under prepending a term whose width is dominated. -/
theorem widthDNF_le_of_cons {n : Nat} (t : Term n) (D : DNF n) :
    widthDNF D ≤ widthDNF (t :: D) := by
  rw [widthDNF_cons]; exact Nat.le_max_right _ _

/-- Every term's width is `≤ widthDNF`. -/
theorem termWidth_le_widthDNF {n : Nat} {t : Term n} {D : DNF n} (ht : t ∈ D) :
    termWidth t ≤ widthDNF D := by
  induction D with
  | nil => exact absurd ht (List.not_mem_nil t)
  | cons s D ih =>
      rw [widthDNF_cons]
      rcases List.mem_cons.mp ht with h | h
      · subst h; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- `termRestrict` never increases a term's width (length). -/
theorem length_termRestrict_le {n : Nat} (ρ : Restriction n)
    (t t' : Term n) (h : termRestrict ρ t = some t') :
    t'.length ≤ t.length := by
  induction t generalizing t' with
  | nil =>
      simp only [termRestrict, Option.some.injEq] at h; subst h; simp
  | cons l t ih =>
      simp only [termRestrict] at h
      cases hρ : ρ l.var with
      | none =>
          simp only [hρ] at h
          cases hrec : termRestrict ρ t with
          | some t'' =>
              simp only [hrec, Option.some.injEq] at h
              subst h
              simp only [List.length_cons]
              exact Nat.succ_le_succ (ih t'' hrec)
          | none => simp only [hrec] at h; exact absurd h (by simp)
      | some b =>
          simp only [hρ] at h
          by_cases hbs : b = l.sign
          · simp only [if_pos hbs] at h
            exact Nat.le_trans (ih t' h) (Nat.le_succ _)
          · simp only [if_neg hbs] at h; exact absurd h (by simp)

/-- **`dnfRestrict` does not increase width.**  Every surviving restricted term
has length `≤` that of some original term, so the maximum width can only stay the
same or shrink. -/
theorem widthDNF_dnfRestrict_le {n : Nat} (ρ : Restriction n) (D : DNF n) :
    widthDNF (dnfRestrict ρ D) ≤ widthDNF D := by
  induction D with
  | nil => simp [dnfRestrict]
  | cons t D ih =>
      rw [show dnfRestrict ρ (t :: D)
            = (match termRestrict ρ t with
                | some t' => t' :: dnfRestrict ρ D
                | none => dnfRestrict ρ D) by
            simp only [dnfRestrict, List.filterMap_cons]
            cases termRestrict ρ t <;> rfl]
      cases hrec : termRestrict ρ t with
      | some t' =>
          simp only [hrec, widthDNF_cons]
          have hlen : termWidth t' ≤ termWidth t :=
            length_termRestrict_le ρ t t' hrec
          have hwt : termWidth t ≤ widthDNF (t :: D) := by
            rw [widthDNF_cons]; exact Nat.le_max_left _ _
          have hwD : widthDNF D ≤ widthDNF (t :: D) := widthDNF_le_of_cons t D
          exact Nat.max_le.mpr
            ⟨Nat.le_trans hlen hwt, Nat.le_trans ih hwD⟩
      | none =>
          simp only [hrec]
          exact Nat.le_trans ih (widthDNF_le_of_cons t D)

/-- The number of stars is at most the number of variables. -/
theorem stars_le {n : Nat} (ρ : Restriction n) : stars ρ ≤ n := by
  classical
  unfold stars
  calc (Finset.univ.filter (fun v => ρ v = none)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

open Classical in
/-- The bad set is a subset of the restrictions with `ℓ` stars (it is defined as a
further `filter` of that set). -/
theorem badSet_subset {n : Nat} (D : DNF n) (s ℓ : Nat) :
    badSet D s ℓ ⊆ restrictionsWithStars n ℓ := by
  unfold badSet
  exact Finset.filter_subset _ _

open Classical in
/-- Membership in `restrictionsWithStars` unfolds to the star count. -/
theorem mem_restrictionsWithStars {n ℓ : Nat} (ρ : Restriction n) :
    ρ ∈ restrictionsWithStars n ℓ ↔ stars ρ = ℓ := by
  unfold restrictionsWithStars
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open Classical in
/-- Membership in `badSet` unfolds to having `ℓ` stars and a deep restricted
canonical decision tree. -/
theorem mem_badSet {n : Nat} {D : DNF n} {s ℓ : Nat} (ρ : Restriction n) :
    ρ ∈ badSet D s ℓ ↔
      stars ρ = ℓ ∧ s ≤ dtDepth (canonicalDT (dnfRestrict ρ D)) := by
  unfold badSet
  rw [Finset.mem_filter, mem_restrictionsWithStars]

/-- The bad set's cardinality is at most that of all restrictions with `ℓ` stars
(an unconditional, trivial bound — it is a subset).  This is NOT the switching
lemma, which is the much sharper `(8·w)^s`-type bound in `SwitchingLemma`. -/
theorem badSet_card_le {n : Nat} (D : DNF n) (s ℓ : Nat) :
    (badSet D s ℓ).card ≤ (restrictionsWithStars n ℓ).card :=
  Finset.card_le_card (badSet_subset D s ℓ)

end SwitchingLemmaStatement
end PvNP
