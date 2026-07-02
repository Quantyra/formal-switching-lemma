import PvNP.PHPBooleanDepthFloor

/-!
# Depth floors for satisfiable PHP under PARTIAL-MATCHING restrictions

The Gate A rung after S2071: `PHPDepthFloorStatement` instances with
NONTRIVIAL restriction families.  A partial-matching restriction fixes a set
`S` of pigeons to the rows of a permutation `f` (pigeon `i ∈ S` sits exactly
in hole `f i`) and leaves the other rows free.  The MASTER theorem
(`matchingRestriction_depthFloor`): for ANY such restriction, every decision
tree computing the restricted `h x h` PHP function has depth at least the
number of FREE variables — the restricted function is still EVASIVE on its
free grid.  The canonical two-parameter boundary family
(`matchingBoundary h s`, fixing the first `s` pigeons along the identity)
instantiates `PHPDepthFloorStatement` with floor `(h - s) * h` for every
`h` and `s`.

Full sensitivity survives the restriction: at the permutation point, flipping
a free `1` starves its pigeon; flipping a free `0` in a free hole collides two
free pigeons; flipping a free `0` in a USED hole collides a free pigeon with a
FIXED one.  So every free variable is sensitive, and an unqueried-variable
argument on the free grid closes the floor.

## HONEST SCOPE STATEMENT (read this)

* These are worst-case Boolean decision-tree depth floors for the SATISFIABLE
  `p = h` pigeonhole function under every fixed partial-matching restriction
  (elementary sensitivity mathematics).  The material content is that the
  `PHPDepthFloorStatement` surface now carries instances with genuinely
  NONTRIVIAL restriction families, parameterized by the number of fixed
  pigeons.
* This is still NOT the switching-lemma-consumable endgame: the switching
  lemma needs PROBABILISTIC statements over DISTRIBUTIONS of random
  restrictions; these are per-restriction worst-case floors for the
  partial-matching class.  NOT a Frege/PHP proof-size bound, NOT an
  NP/circuit bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPRestrictedDepthFloor

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPSearchFloor
open PHPFamilyCoverage
open PHPFamilyTraceSearchRoute
open PHPBooleanDepthFloor

/-! ## Permutation points -/

/-- The permutation-matrix assignment of `f`: variable `(i, j)` is `true`
exactly when `j = f i` (ambient variable reads `false`). -/
def permAssignment {h : Nat} (f : Fin h → Fin h) :
    Assignment (Nat.succ (h * h)) :=
  fun w =>
    if hw : w.val < h * h then
      decide (holeOf w hw = f (pigeonOf w hw))
    else false

theorem permAssignment_phpVar {h : Nat} (f : Fin h → Fin h) (i j : Fin h) :
    permAssignment f (phpVar h h i j) = decide (j = f i) := by
  have hlt := phpVar_lt (p := h) (h := h) i j
  rw [permAssignment, dif_pos hlt, pigeonOf_phpVar i j hlt,
    holeOf_phpVar i j hlt]

/-- Any permutation point satisfies the full `h x h` formula (injectivity of
`f`, via its left inverse `g`, rules out collisions). -/
theorem eval_permAssignment_true {h : Nat} (f g : Fin h → Fin h)
    (hgf : ∀ i, g (f i) = i) :
    eval (permAssignment f) (restrictedPHPFormula (fullPHPView h)) = true := by
  rw [restrictedPHPFormula_fullPHPView, eval_and, List.all_eq_true]
  intro c hc
  rcases mem_fullPHPClauses hc with ⟨i, he⟩ | ⟨i, k, j, hik, he⟩
  · subst he
    rw [eval_pigeonClause, List.any_eq_true]
    refine ⟨f i, mem_finList h _, ?_⟩
    rw [permAssignment_phpVar]
    simp
  · subst he
    rw [eval_collisionClause, permAssignment_phpVar, permAssignment_phpVar]
    by_cases hij : j = f i
    · have hkj : ¬ (j = f k) := by
        intro hkj
        have : i = k := by
          have := congrArg g (hij.symm.trans hkj)
          rwa [hgf, hgf] at this
        omega
      simp [hkj]
    · simp [hij]

/-- Full sensitivity at any permutation point: flipping ANY PHP variable
falsifies the formula.  (Only the right-inverse law is needed: the flipped
pigeon's collision partner is hole `holeOf w`'s occupant `g (holeOf w)`.) -/
theorem eval_flip_permAssignment_false {h : Nat} (f g : Fin h → Fin h)
    (hfg : ∀ j, f (g j) = j)
    (w : Fin (Nat.succ (h * h))) (hw : w.val < h * h) :
    eval (flipAt (permAssignment f) w)
      (restrictedPHPFormula (fullPHPView h)) = false := by
  have hwv : phpVar h h (pigeonOf w hw) (holeOf w hw) = w :=
    phpVar_pigeonOf_holeOf w hw
  apply Bool.eq_false_iff.mpr
  intro htrue
  rw [restrictedPHPFormula_fullPHPView, eval_and, List.all_eq_true] at htrue
  by_cases hdiag : holeOf w hw = f (pigeonOf w hw)
  · -- Flipping a `1`: the pigeon's clause is now all-false.
    have hclause := htrue _ (pigeonClause_mem_fullPHPClauses (pigeonOf w hw))
    rw [eval_pigeonClause, List.any_eq_true] at hclause
    rcases hclause with ⟨j, _, hj⟩
    by_cases hjj : j = holeOf w hw
    · subst hjj
      rw [hwv, flipAt_self] at hj
      rw [show permAssignment f w = true from by
        rw [← hwv, permAssignment_phpVar]; simpa using hdiag] at hj
      simp at hj
    · have hne : phpVar h h (pigeonOf w hw) j ≠ w := by
        intro he
        exact hjj (phpVar_inj (he.trans hwv.symm)).2
      rw [flipAt_ne _ hne, permAssignment_phpVar] at hj
      have hij : ¬ (j = f (pigeonOf w hw)) := by
        intro he
        exact hjj (he.trans hdiag.symm)
      simp [hij] at hj
  · -- Flipping a `0`: the flipped pigeon collides with hole `holeOf w`'s
    -- occupant `g (holeOf w)`.
    have hval0 : flipAt (permAssignment f) w
        (phpVar h h (pigeonOf w hw) (holeOf w hw)) = true := by
      rw [hwv, flipAt_self]
      rw [show permAssignment f w = false from by
        rw [← hwv, permAssignment_phpVar]; simpa using hdiag]
      rfl
    have hne01 : g (holeOf w hw) ≠ pigeonOf w hw := by
      intro he
      apply hdiag
      have := congrArg f he
      rwa [hfg] at this
    have hval1 : flipAt (permAssignment f) w
        (phpVar h h (g (holeOf w hw)) (holeOf w hw)) = true := by
      have hne : phpVar h h (g (holeOf w hw)) (holeOf w hw) ≠ w := by
        intro he
        exact hne01 (phpVar_inj (he.trans hwv.symm)).1
      rw [flipAt_ne _ hne, permAssignment_phpVar]
      simp [hfg]
    rcases Nat.lt_or_ge (pigeonOf w hw).val (g (holeOf w hw)).val with
      hlt | hge
    · have hclause := htrue _ (collisionClause_mem_fullPHPClauses
        (pigeonOf w hw) (g (holeOf w hw)) (holeOf w hw) hlt)
      rw [eval_collisionClause, hval0, hval1] at hclause
      simp at hclause
    · have hlt : (g (holeOf w hw)).val < (pigeonOf w hw).val := by
        rcases Nat.lt_or_ge (g (holeOf w hw)).val (pigeonOf w hw).val with
          h' | h'
        · exact h'
        · exact absurd (Fin.ext (Nat.le_antisymm hge h')) hne01
      have hclause := htrue _ (collisionClause_mem_fullPHPClauses
        (g (holeOf w hw)) (pigeonOf w hw) (holeOf w hw) hlt)
      rw [eval_collisionClause, hval0, hval1] at hclause
      simp at hclause

/-! ## Partial-matching restrictions -/

/-- The partial-matching restriction: pigeons with `S i = true` have their
whole row fixed to the indicator of hole `f i`; other rows (and the ambient
variable) are free. -/
def matchingRestriction {h : Nat} (S : Fin h → Bool) (f : Fin h → Fin h) :
    Restriction (Nat.succ (h * h)) :=
  fun w =>
    if hw : w.val < h * h then
      if S (pigeonOf w hw) then
        some (decide (holeOf w hw = f (pigeonOf w hw)))
      else none
    else none

/-- The permutation point of `f` extends every `(S, f)` partial matching. -/
theorem permAssignment_agrees {h : Nat} (S : Fin h → Bool)
    (f : Fin h → Fin h) :
    Agree (matchingRestriction S f) (permAssignment f) := by
  intro v b hv
  rw [matchingRestriction] at hv
  by_cases hlt : v.val < h * h
  · rw [dif_pos hlt] at hv
    by_cases hS : S (pigeonOf v hlt)
    · rw [if_pos hS] at hv
      have hb : b = decide (holeOf v hlt = f (pigeonOf v hlt)) :=
        (Option.some.injEq _ _ ▸ hv).symm
      rw [hb, permAssignment, dif_pos hlt]
    · rw [if_neg hS] at hv
      exact Option.noConfusion hv
  · rw [dif_neg hlt] at hv
    exact Option.noConfusion hv

/-- Flipping a FREE variable preserves agreement with the restriction. -/
theorem flip_agrees {h : Nat} (S : Fin h → Bool) (f : Fin h → Fin h)
    (a : Assignment (Nat.succ (h * h)))
    (ha : Agree (matchingRestriction S f) a)
    (w : Fin (Nat.succ (h * h))) (hw : w.val < h * h)
    (hfree : S (pigeonOf w hw) = false) :
    Agree (matchingRestriction S f) (flipAt a w) := by
  intro v b hv
  have hvw : v ≠ w := by
    intro he
    subst he
    rw [matchingRestriction, dif_pos hw, hfree] at hv
    simp at hv
  rw [flipAt_ne _ hvw]
  exact ha v b hv

/-! ## The free-variable grid -/

/-- The free pigeons of a partial matching. -/
def freeRows {h : Nat} (S : Fin h → Bool) : List (Fin h) :=
  (finList h).filter (fun i => !(S i))

/-- The free variables: every hole entry of every free pigeon's row. -/
def freeVars {h : Nat} (S : Fin h → Bool) :
    List (Fin (Nat.succ (h * h))) :=
  (freeRows S).bind (fun i => (finList h).map (fun j => phpVar h h i j))

theorem mem_freeVars {h : Nat} {S : Fin h → Bool}
    {w : Fin (Nat.succ (h * h))} (hw : w ∈ freeVars S) :
    ∃ (i j : Fin h), S i = false ∧ w = phpVar h h i j := by
  rcases List.mem_bind.mp hw with ⟨i, hi, hw⟩
  rcases List.mem_map.mp hw with ⟨j, _, he⟩
  rcases List.mem_filter.mp hi with ⟨_, hSi⟩
  exact ⟨i, j, by simpa using hSi, he.symm⟩

/-- A bind of pairwise-disjoint duplicate-free blocks is duplicate-free. -/
theorem nodup_bind_of_disjoint {α β : Type _} :
    ∀ (L : List α) (f : α → List β), L.Nodup →
      (∀ x ∈ L, (f x).Nodup) →
      (∀ x ∈ L, ∀ y ∈ L, x ≠ y → ∀ b ∈ f x, b ∉ f y) →
      (L.bind f).Nodup
  | [], _, _, _, _ => List.nodup_nil
  | x :: L, f, hnd, hblocks, hdisj => by
      rw [List.bind_cons]
      refine List.Nodup.append
        (hblocks x (List.mem_cons_self x L)) ?_ ?_
      · refine nodup_bind_of_disjoint L f
          ((List.nodup_cons.mp hnd).2)
          (fun y hy => hblocks y (List.mem_cons_of_mem x hy)) ?_
        intro y hy z hz hyz b hb
        exact hdisj y (List.mem_cons_of_mem x hy) z
          (List.mem_cons_of_mem x hz) hyz b hb
      · intro b hbx hbL
        rcases List.mem_bind.mp hbL with ⟨y, hy, hby⟩
        have hxy : x ≠ y := by
          intro he
          subst he
          exact (List.nodup_cons.mp hnd).1 hy
        exact hdisj x (List.mem_cons_self x L) y
          (List.mem_cons_of_mem x hy) hxy b hbx hby

theorem freeVars_nodup {h : Nat} (S : Fin h → Bool) :
    (freeVars S).Nodup := by
  refine nodup_bind_of_disjoint _ _
    (List.Nodup.filter _ (finList_nodup h)) ?_ ?_
  · intro i _
    exact List.Nodup.map (fun j1 j2 he => (phpVar_inj he).2) (finList_nodup h)
  · intro i _ k _ hik b hbi hbk
    rcases List.mem_map.mp hbi with ⟨j1, _, he1⟩
    rcases List.mem_map.mp hbk with ⟨j2, _, he2⟩
    exact hik (phpVar_inj (he1.trans he2.symm)).1

/-- A bind of constant-length blocks has length `|L| * k`. -/
theorem length_bind_const {α β : Type _} :
    ∀ (L : List α) (f : α → List β) (k : Nat),
      (∀ x ∈ L, (f x).length = k) → (L.bind f).length = L.length * k
  | [], _, _, _ => by simp
  | x :: L, f, k, hk => by
      rw [List.bind_cons, List.length_append,
        hk x (List.mem_cons_self x L),
        length_bind_const L f k (fun y hy => hk y (List.mem_cons_of_mem x hy)),
        List.length_cons, Nat.succ_mul]
      omega

theorem freeVars_length {h : Nat} (S : Fin h → Bool) :
    (freeVars S).length = (freeRows S).length * h := by
  refine length_bind_const _ _ h ?_
  intro i _
  rw [List.length_map, finList_length]

/-! ## The master theorem -/

/-- **Master partial-matching depth floor.**  For every partial matching
`(S, f)` (with `f` a permutation via its inverse `g`), any decision tree
computing the restricted `h x h` PHP function has depth at least the number
of free variables: the restricted function is evasive on its free grid. -/
theorem matchingRestriction_depthFloor {h : Nat} (S : Fin h → Bool)
    (f g : Fin h → Fin h) (hgf : ∀ i, g (f i) = i) (hfg : ∀ j, f (g j) = j)
    (T : DTree (Nat.succ (h * h)))
    (hT : ∀ a : Assignment (Nat.succ (h * h)),
      Agree (matchingRestriction S f) a →
      dtEval a T =
        eval a (restrict (matchingRestriction S f)
          (restrictedPHPFormula (fullPHPView h)))) :
    (freeVars S).length ≤ dtDepth T := by
  by_contra hlt
  push_neg at hlt
  have hagree := permAssignment_agrees S f
  -- The tree computes the unrestricted formula on agreeing assignments.
  have hcomp : ∀ a : Assignment (Nat.succ (h * h)),
      Agree (matchingRestriction S f) a →
      dtEval a T = eval a (restrictedPHPFormula (fullPHPView h)) := by
    intro a ha
    have := hT a ha
    rwa [eval_restrict _ _ _ ha] at this
  -- Some free variable is unqueried on the permutation-point path.
  have hpath : (dtPathVars (permAssignment f) T).length <
      (freeVars S).length := by
    have := dtPathVars_length_le_depth (permAssignment f) T
    omega
  obtain ⟨w, hwmem, hwnot⟩ := exists_not_mem_of_short (freeVars S)
    (freeVars_nodup S) (dtPathVars (permAssignment f) T) hpath
  obtain ⟨i, j, hSi, hwe⟩ := mem_freeVars hwmem
  subst hwe
  have hwlt : (phpVar h h i j).val < h * h := phpVar_lt i j
  have hfree : S (pigeonOf (phpVar h h i j) hwlt) = false := by
    rw [pigeonOf_phpVar i j hwlt]
    exact hSi
  -- Flipping it preserves agreement and the output, but flips the function.
  have hflip_agrees := flip_agrees S f (permAssignment f) hagree
    (phpVar h h i j) hwlt hfree
  have hsame := dtEval_flipAt_of_not_mem_path (permAssignment f)
    (phpVar h h i j) T hwnot
  have htrue : dtEval (permAssignment f) T = true := by
    rw [hcomp _ hagree, eval_permAssignment_true f g hgf]
  have hfalse : dtEval (flipAt (permAssignment f) (phpVar h h i j)) T =
      false := by
    rw [hcomp _ hflip_agrees,
      eval_flip_permAssignment_false f g hfg (phpVar h h i j) hwlt]
  rw [htrue, hfalse] at hsame
  exact Bool.noConfusion hsame

/-! ## The canonical `(h, s)` boundary family -/

/-- Fix the first `s` pigeons along the identity matching. -/
def thresholdS (h s : Nat) : Fin h → Bool :=
  fun i => decide (i.val < s)

/-- Filtering `Fin`-lifted range by a value predicate matches filtering the
range. -/
private theorem filter_pmap_length {n : Nat} (p : Nat → Bool) :
    ∀ (L : List Nat) (H : ∀ a ∈ L, a < n),
      ((List.pmap (fun a ha => (⟨a, ha⟩ : Fin n)) L H).filter
        (fun i => p i.val)).length = (L.filter p).length
  | [], _ => rfl
  | a :: L, H => by
      have ih := filter_pmap_length p L
        (fun b hb => H b (List.mem_cons_of_mem a hb))
      simp only [List.pmap, List.filter_cons]
      cases hpa : p a with
      | false => simpa [hpa] using ih
      | true => simpa [hpa] using ih

private theorem range_filter_ge_length (s : Nat) :
    ∀ h : Nat,
      ((List.range h).filter (fun t => !decide (t < s))).length = h - s := by
  intro h
  induction h with
  | zero => simp
  | succ h ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      by_cases hhs : h < s
      · simp [hhs]
        omega
      · simp [hhs]
        omega

theorem freeRows_thresholdS_length (h s : Nat) :
    (freeRows (thresholdS h s)).length = h - s := by
  have key := filter_pmap_length (n := h) (fun t => !decide (t < s))
    (List.range h) (fun a ha => List.mem_range.mp ha)
  calc (freeRows (thresholdS h s)).length
      = ((List.range h).filter (fun t => !decide (t < s))).length := key
    _ = h - s := range_filter_ge_length s h

/-- The canonical `(h, s)` partial-matching boundary: first `s` pigeons fixed
along the identity, floor `(h - s) * h`. -/
def matchingBoundary (h s : Nat) : PHPDepthFloorBoundary h h where
  view := fullPHPView h
  restrictionFamily := [matchingRestriction (thresholdS h s) (fun i => i)]
  depthFloor := (h - s) * h

/-- **The two-parameter Gate A family.**  For every `h` and `s`, the canonical
partial-matching boundary satisfies `PHPDepthFloorStatement` with floor
`(h - s) * h`: fixing `s` pigeons still leaves the function evasive on the
remaining `(h-s) x h` free grid.  Nontrivial restriction family for
`0 < s` (and `0 < h`, so fixed variables exist);
recovers the S2071 empty-restriction floor shape at `s = 0`. -/
theorem matchingBoundary_depthFloor (h s : Nat) :
    PHPDepthFloorStatement (matchingBoundary h s) := by
  intro ρ hρ T hT
  have hρe : ρ = matchingRestriction (thresholdS h s) (fun i => i) := by
    simpa [matchingBoundary] using hρ
  subst hρe
  show (h - s) * h ≤ dtDepth T
  have hmaster := matchingRestriction_depthFloor (thresholdS h s)
    (fun i => i) (fun i => i) (fun _ => rfl) (fun _ => rfl) T hT
  rwa [freeVars_length, freeRows_thresholdS_length] at hmaster

/-- **Non-vacuity of every `(h, s)` boundary.**  A tree satisfying the
boundary's correctness hypothesis exists (depth `h*h + 1`). -/
theorem matchingBoundary_correctTree_exists (h s : Nat) :
    ∃ T : DTree (Nat.succ (h * h)),
      (∀ a : Assignment (Nat.succ (h * h)),
        Agree (matchingRestriction (thresholdS h s) (fun i => i)) a →
        dtEval a T =
          eval a (restrict (matchingRestriction (thresholdS h s) (fun i => i))
            (restrictedPHPFormula (fullPHPView h)))) ∧
      dtDepth T = h * h + 1 := by
  refine ⟨dtOfFun
    (fun a => eval a (restrict (matchingRestriction (thresholdS h s)
      (fun i => i)) (restrictedPHPFormula (fullPHPView h))))
    (finList (Nat.succ (h * h))) (fun _ => false), fun a _ => ?_, ?_⟩
  · apply dtOfFun_eval
    intro v
    exact Or.inl (mem_finList _ v)
  · rw [dtOfFun_depth, finList_length]

end PHPRestrictedDepthFloor
end PvNP
