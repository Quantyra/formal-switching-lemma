import PvNP.BoundedDepthFrege

/-!
# Restriction machinery on bounded-depth (AC0) formulas

This file builds the **restriction (partial assignment) operation** on the
faithful bounded-depth formula model `PvNP.BoundedDepthFrege.BDFormula`.  A
*restriction* fixes some variables to Boolean constants and leaves the rest free
("stars").  Applying a restriction substitutes the fixed variables and propagates
the resulting constants structurally through the formula.

Restriction is the foundational operation underlying **switching-lemma**
arguments for AC0 lower bounds: one applies a random restriction, then argues the
restricted formula collapses to a low-depth decision tree.  This file provides
ONLY that foundational operation together with its two load-bearing correctness
properties:

* `eval_restrict` — **the key semantic faithfulness theorem**: for any total
  assignment `a` that *agrees* with the restriction `ρ` (extends it), the
  restricted formula evaluates exactly as the original:
  `eval a (restrict ρ F) = eval a F`.
* `depth_restrict_le` — restriction never increases depth:
  `depth (restrict ρ F) ≤ depth F`.

## HONEST SCOPE STATEMENT (read this)
This is switching-lemma **INFRASTRUCTURE ONLY**.  It is

* **NOT** the switching lemma (no random-restriction probabilistic argument, no
  decision-tree collapse, no closure bound);
* **NOT** any lower bound;
* **NOT** a claim about P vs NP.

It is the genuine, real-semantics restriction operation with its honest
correctness lemmas, to be reused by a later switching-lemma effort.  Soundness /
faithfulness of `restrict` proves no hardness on its own.
-/

namespace PvNP
namespace BoundedDepthRestriction

open PvNP.CNFModel
open PvNP.BoundedDepthFrege

/-! ## 1. Partial restrictions -/

/--
A partial restriction (partial assignment): each variable is either left free
(`none`, a "star") or fixed to a Boolean constant (`some b`).
-/
def Restriction (n : Nat) : Type := Fin n → Option Bool

/-! ## 2. The restriction operation on formulas -/

/--
Apply a partial restriction to a bounded-depth formula, substituting fixed
variables and propagating the resulting constants.

* constants `tru`/`fls` are unchanged;
* a literal `lit l` whose variable is fixed (`ρ l.var = some b`) becomes the
  constant `tru` if the literal is satisfied by that fixing (`b == l.sign`) and
  `fls` otherwise; if the variable is free (`ρ l.var = none`) the literal is left
  unchanged;
* `and`/`or` gates recurse structurally into every child (plain structural map;
  no list simplification, keeping the proof burden minimal).
-/
def restrict {n : Nat} (ρ : Restriction n) : BDFormula n → BDFormula n
  | .tru => .tru
  | .fls => .fls
  | .lit l =>
      match ρ l.var with
      | some b => if b == l.sign then .tru else .fls
      | none => .lit l
  | .and l => .and (l.attach.map (fun f => restrict ρ f.1))
  | .or  l => .or  (l.attach.map (fun f => restrict ρ f.1))
  termination_by F => sizeOf F
  decreasing_by
    all_goals
      simp_wf
      have hlt := List.sizeOf_lt_of_mem f.2
      omega

theorem restrict_tru {n : Nat} (ρ : Restriction n) :
    restrict ρ (BDFormula.tru) = BDFormula.tru := by simp only [restrict]

theorem restrict_fls {n : Nat} (ρ : Restriction n) :
    restrict ρ (BDFormula.fls) = BDFormula.fls := by simp only [restrict]

/-- `restrict` on an `and` gate, with `attach` erased: it is the plain structural
map of `restrict ρ` over the children. -/
theorem restrict_and {n : Nat} (ρ : Restriction n) (l : List (BDFormula n)) :
    restrict ρ (BDFormula.and l) = BDFormula.and (l.map (fun f => restrict ρ f)) := by
  rw [show restrict ρ (BDFormula.and l)
        = BDFormula.and (l.attach.map (fun f => restrict ρ f.1)) by simp only [restrict]]
  rw [List.attach_map_val l (fun f => restrict ρ f)]

/-- `restrict` on an `or` gate, with `attach` erased. -/
theorem restrict_or {n : Nat} (ρ : Restriction n) (l : List (BDFormula n)) :
    restrict ρ (BDFormula.or l) = BDFormula.or (l.map (fun f => restrict ρ f)) := by
  rw [show restrict ρ (BDFormula.or l)
        = BDFormula.or (l.attach.map (fun f => restrict ρ f.1)) by simp only [restrict]]
  rw [List.attach_map_val l (fun f => restrict ρ f)]

/-! ## 3. Agreement between a restriction and a total assignment -/

/--
A total assignment `a` *agrees* with a restriction `ρ` when `a` extends every
fixing made by `ρ`: wherever `ρ` fixes a variable to `b`, `a` also gives it `b`.
Free variables (`ρ v = none`) are unconstrained.
-/
def Agree {n : Nat} (ρ : Restriction n) (a : Assignment n) : Prop :=
  ∀ v b, ρ v = some b → a v = b

/-! ## 4. The key semantic lemma -/

/--
**The load-bearing faithfulness theorem.** If the total assignment `a` agrees
with (extends) the restriction `ρ`, then the restricted formula evaluates exactly
as the original under `a`:
`eval a (restrict ρ F) = eval a F`.

This is the genuine, unweakened semantic commutation of `restrict` with `eval`.
-/
theorem eval_restrict {n : Nat} (ρ : Restriction n) (a : Assignment n)
    (F : BDFormula n) (h : Agree ρ a) :
    eval a (restrict ρ F) = eval a F := by
  induction F using BDFormula.recAux with
  | htru => rw [restrict_tru]
  | hfls => rw [restrict_fls]
  | hlit l =>
      rw [eval_lit]
      -- Unfold `restrict` on the literal and case on the restriction at `l.var`.
      simp only [restrict]
      cases hρ : ρ l.var with
      | none => rw [eval_lit]
      | some b =>
          -- `a l.var = b` by agreement; both sides reduce to `b == l.sign`.
          have hab : a l.var = b := h l.var b hρ
          -- `litEval a l = if l.sign then a l.var else !a l.var = (a l.var == l.sign)`.
          cases hb : b <;> cases hs : l.sign <;>
            simp [litEval, hb, hs, hab, eval_tru, eval_fls]
  | hand l ih =>
      rw [restrict_and, eval_and, eval_and, List.all_map]
      apply all_congr_mem
      intro f hf
      simpa [Function.comp] using ih f hf
  | hor l ih =>
      rw [restrict_or, eval_or, eval_or, List.any_map]
      apply any_congr_mem
      intro f hf
      simpa [Function.comp] using ih f hf

/-! ## 5. Restriction does not increase depth -/

/-- Childwise depth domination lifts to the `foldr Nat.max` aggregate. -/
theorem foldr_max_le_of_le {n : Nat} (l : List (BDFormula n)) (ρ : Restriction n)
    (ih : ∀ f ∈ l, depth (restrict ρ f) ≤ depth f) :
    ((l.map (fun f => restrict ρ f)).map (fun f => depth f)).foldr Nat.max 0
      ≤ (l.map (fun f => depth f)).foldr Nat.max 0 := by
  induction l with
  | nil => simp
  | cons x xs ihl =>
      simp only [List.map_cons, List.foldr_cons]
      have hx : depth (restrict ρ x) ≤ depth x := ih x (List.mem_cons_self x xs)
      have hxs : ((xs.map (fun f => restrict ρ f)).map (fun f => depth f)).foldr Nat.max 0
          ≤ (xs.map (fun f => depth f)).foldr Nat.max 0 :=
        ihl (fun f hf => ih f (List.mem_cons_of_mem x hf))
      exact Nat.max_le.mpr ⟨Nat.le_trans hx (Nat.le_max_left _ _),
        Nat.le_trans hxs (Nat.le_max_right _ _)⟩

/--
**Restriction never increases depth.** Restriction maps each gate to a gate over
restricted children (and a fixed literal to a depth-`0` constant), so the
alternation/nesting depth can only stay the same or shrink:
`depth (restrict ρ F) ≤ depth F`.
-/
theorem depth_restrict_le {n : Nat} (ρ : Restriction n) (F : BDFormula n) :
    depth (restrict ρ F) ≤ depth F := by
  induction F using BDFormula.recAux with
  | htru => rw [restrict_tru]; exact Nat.le_refl _
  | hfls => rw [restrict_fls]; exact Nat.le_refl _
  | hlit l =>
      -- A fixed literal becomes a constant (depth 0); a free literal is unchanged.
      simp only [restrict]
      cases _hρ : ρ l.var with
      | none => exact Nat.le_refl _
      | some b => cases hb : b == l.sign <;> simp [hb, depth]
  | hand l ih =>
      rw [restrict_and]
      -- depth (and m) = 1 + foldr max 0 (map depth m); compare childwise maxima.
      show depth (BDFormula.and (l.map (fun f => restrict ρ f))) ≤ depth (BDFormula.and l)
      rw [show depth (BDFormula.and (l.map (fun f => restrict ρ f)))
            = 1 + ((l.map (fun f => restrict ρ f)).attach.map (fun f => depth f.1)).foldr Nat.max 0
            from by simp only [depth]]
      rw [show depth (BDFormula.and l)
            = 1 + (l.attach.map (fun f => depth f.1)).foldr Nat.max 0
            from by simp only [depth]]
      apply Nat.add_le_add_left
      rw [List.attach_map_val l (fun f => depth f),
          List.attach_map_val (l.map (fun f => restrict ρ f)) (fun f => depth f)]
      exact foldr_max_le_of_le l ρ ih
  | hor l ih =>
      rw [restrict_or]
      show depth (BDFormula.or (l.map (fun f => restrict ρ f))) ≤ depth (BDFormula.or l)
      rw [show depth (BDFormula.or (l.map (fun f => restrict ρ f)))
            = 1 + ((l.map (fun f => restrict ρ f)).attach.map (fun f => depth f.1)).foldr Nat.max 0
            from by simp only [depth]]
      rw [show depth (BDFormula.or l)
            = 1 + (l.attach.map (fun f => depth f.1)).foldr Nat.max 0
            from by simp only [depth]]
      apply Nat.add_le_add_left
      rw [List.attach_map_val l (fun f => depth f),
          List.attach_map_val (l.map (fun f => restrict ρ f)) (fun f => depth f)]
      exact foldr_max_le_of_le l ρ ih

end BoundedDepthRestriction
end PvNP
