import PvNP.PHPFamilyTraceSearchRoute

/-!
# A family Boolean decision-tree depth floor for satisfiable PHP: evasiveness

The first genuine FAMILY instance of `RestrictedPHPFloor.PHPDepthFloorStatement`
beyond the trivial `1 x 1` boundary: for every `h`, any decision tree computing
the SATISFIABLE `h x h` pigeonhole Boolean function (under the empty
restriction) has depth at least `h * h` — the maximum possible, i.e. the
function is EVASIVE.

The argument is full sensitivity at a permutation point: the identity
permutation matrix satisfies the `h`-pigeon/`h`-hole PHP formula, and flipping
ANY single variable of it falsifies the formula (flipping a `1` starves that
pigeon; flipping a `0` collides two pigeons in one hole).  A tree of depth
`< h*h` leaves some variable unqueried on the identity-matrix path, and
flipping it cannot change the output.  (Only identity-point membership and
sensitivity are proved and used; the exact characterization of all satisfying
assignments is not stated.)

## HONEST SCOPE STATEMENT (read this)

* This is a Boolean decision-tree depth floor (an evasiveness/sensitivity
  result) for the SATISFIABLE `p = h` pigeonhole function, under the EMPTY
  restriction family.  The mathematics is elementary and classical; the
  material content here is inhabiting the `PHPDepthFloorStatement` surface
  with a growing family at the maximal floor.
* For `p > h` the PHP formula is identically false, so a positive Boolean
  depth floor there would be FALSE and is not claimed (the `p > h` regime is
  served by the falsified-clause SEARCH floors elsewhere in this repository).
* This is NOT the Frege/PHP gate's endgame: the switching-lemma route needs
  depth floors under NONTRIVIAL random-restriction families, which remain
  open.  NOT a Frege/PHP proof-size lower bound, NOT an NP/circuit lower
  bound, NOT a statement about P vs NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPBooleanDepthFloor

open CNFModel
open BoundedDepthFrege
open BoundedDepthDecisionTree
open BoundedDepthRestriction
open RestrictedPHPFloor
open PHPSearchFloor
open PHPFamilyCoverage
open PHPFamilyTraceSearchRoute

/-! ## The full `h x h` view, the empty restriction, and the identity point -/

/-- The full `h x h` PHP view: every pigeon may use every hole. -/
def fullPHPView (h : Nat) : RestrictedPHP h h where
  allowed _ := finList h

/-- The empty (all-free) restriction on the ambient variable space. -/
def emptyRestriction (h : Nat) : Restriction (Nat.succ (h * h)) :=
  fun _ => none

theorem agree_emptyRestriction {h : Nat} (a : Assignment (Nat.succ (h * h))) :
    Agree (emptyRestriction h) a := by
  intro v b hv
  exact Option.noConfusion hv

/-- The identity permutation-matrix assignment: variable `(i, j)` is `true`
exactly when `i = j` (ambient variable reads `false`). -/
def idAssignment (h : Nat) : Assignment (Nat.succ (h * h)) :=
  fun w =>
    if hw : w.val < h * h then
      decide ((pigeonOf w hw).val = (holeOf w hw).val)
    else false

theorem idAssignment_phpVar {h : Nat} (i j : Fin h) :
    idAssignment h (phpVar h h i j) = decide (i.val = j.val) := by
  have hlt := phpVar_lt (p := h) (h := h) i j
  rw [idAssignment, dif_pos hlt, pigeonOf_phpVar i j hlt, holeOf_phpVar i j hlt]

/-- Flip one variable of an assignment. -/
def flipAt {n : Nat} (a : Assignment n) (w : Fin n) : Assignment n :=
  fun v => if v = w then !(a v) else a v

theorem flipAt_self {n : Nat} (a : Assignment n) (w : Fin n) :
    flipAt a w w = !(a w) := by simp [flipAt]

theorem flipAt_ne {n : Nat} (a : Assignment n) {w v : Fin n} (hv : v ≠ w) :
    flipAt a w v = a v := by simp [flipAt, hv]

/-! ## The clause list of the full view -/

/-- The clause list of `restrictedPHPFormula (fullPHPView h)`, displayed. -/
def fullPHPClauses (h : Nat) : List (BDFormula (Nat.succ (h * h))) :=
  (finList h).map (pigeonSomewhereClause (fullPHPView h)) ++
    (finList h).bind (fun i =>
      (finList h).bind (fun k =>
        if i.val < k.val then
          (finList h).map (noCollisionClause h h i k)
        else []))

theorem restrictedPHPFormula_fullPHPView (h : Nat) :
    restrictedPHPFormula (fullPHPView h) = BDFormula.and (fullPHPClauses h) :=
  rfl

theorem mem_fullPHPClauses {h : Nat} {c : BDFormula (Nat.succ (h * h))}
    (hc : c ∈ fullPHPClauses h) :
    (∃ i : Fin h, c = pigeonSomewhereClause (fullPHPView h) i) ∨
      (∃ (i k : Fin h) (j : Fin h),
        i.val < k.val ∧ c = noCollisionClause h h i k j) := by
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_map.mp hc with ⟨i, _, he⟩
    exact Or.inl ⟨i, he.symm⟩
  · rcases List.mem_bind.mp hc with ⟨i, _, hc⟩
    rcases List.mem_bind.mp hc with ⟨k, _, hc⟩
    by_cases hik : i.val < k.val
    · rw [if_pos hik] at hc
      rcases List.mem_map.mp hc with ⟨j, _, he⟩
      exact Or.inr ⟨i, k, j, hik, he.symm⟩
    · rw [if_neg hik] at hc
      exact absurd hc (List.not_mem_nil c)

theorem pigeonClause_mem_fullPHPClauses {h : Nat} (i : Fin h) :
    pigeonSomewhereClause (fullPHPView h) i ∈ fullPHPClauses h :=
  List.mem_append.mpr (Or.inl (List.mem_map_of_mem _ (mem_finList h i)))

theorem collisionClause_mem_fullPHPClauses {h : Nat} (i k j : Fin h)
    (hik : i.val < k.val) :
    noCollisionClause h h i k j ∈ fullPHPClauses h := by
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_bind.mpr ⟨i, mem_finList h i, ?_⟩
  refine List.mem_bind.mpr ⟨k, mem_finList h k, ?_⟩
  rw [if_pos hik]
  exact List.mem_map_of_mem _ (mem_finList h j)

/-! ## Clause evaluation helpers -/

theorem eval_pigeonClause {h : Nat} (a : Assignment (Nat.succ (h * h)))
    (i : Fin h) :
    eval a (pigeonSomewhereClause (fullPHPView h) i) =
      (finList h).any (fun j => a (phpVar h h i j)) := by
  show eval a (BDFormula.or ((finList h).map
    (fun j => BDFormula.lit (mapsLit h h i j)))) = _
  rw [eval_or]
  generalize finList h = L
  induction L with
  | nil => rfl
  | cons j js ih =>
      simp only [List.map_cons, List.any_cons, ih]
      congr 1
      rw [eval_lit]
      simp [mapsLit, litEval]

theorem eval_collisionClause {h : Nat} (a : Assignment (Nat.succ (h * h)))
    (i k j : Fin h) :
    eval a (noCollisionClause h h i k j) =
      (!(a (phpVar h h i j)) || !(a (phpVar h h k j))) := by
  show eval a (BDFormula.or [BDFormula.lit (notMapsLit h h i j),
    BDFormula.lit (notMapsLit h h k j)]) = _
  rw [eval_or]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [eval_lit, eval_lit]
  simp [notMapsLit, litEval]

/-! ## The identity point satisfies the formula -/

theorem eval_idAssignment_true (h : Nat) :
    eval (idAssignment h) (restrictedPHPFormula (fullPHPView h)) = true := by
  rw [restrictedPHPFormula_fullPHPView, eval_and, List.all_eq_true]
  intro c hc
  rcases mem_fullPHPClauses hc with ⟨i, he⟩ | ⟨i, k, j, hik, he⟩
  · subst he
    rw [eval_pigeonClause, List.any_eq_true]
    refine ⟨⟨i.val, i.isLt⟩, mem_finList h _, ?_⟩
    rw [idAssignment_phpVar]
    simp
  · subst he
    rw [eval_collisionClause, idAssignment_phpVar, idAssignment_phpVar]
    by_cases hij : i.val = j.val
    · have hkj : ¬ (k.val = j.val) := by omega
      simp [hkj]
    · simp [hij]

/-! ## Full sensitivity at the identity point -/

/-- Flipping ANY PHP variable of the identity point falsifies the formula. -/
theorem eval_flip_idAssignment_false {h : Nat}
    (w : Fin (Nat.succ (h * h))) (hw : w.val < h * h) :
    eval (flipAt (idAssignment h) w) (restrictedPHPFormula (fullPHPView h)) =
      false := by
  have hwv : phpVar h h (pigeonOf w hw) (holeOf w hw) = w :=
    phpVar_pigeonOf_holeOf w hw
  apply Bool.eq_false_iff.mpr
  intro htrue
  rw [restrictedPHPFormula_fullPHPView, eval_and, List.all_eq_true] at htrue
  by_cases hdiag : (pigeonOf w hw).val = (holeOf w hw).val
  · -- Flipping a `1`: pigeon `pigeonOf w`'s clause is now all-false.
    have hclause := htrue _ (pigeonClause_mem_fullPHPClauses (pigeonOf w hw))
    rw [eval_pigeonClause, List.any_eq_true] at hclause
    rcases hclause with ⟨j, _, hj⟩
    by_cases hjj : j = holeOf w hw
    · subst hjj
      rw [hwv, flipAt_self] at hj
      rw [show idAssignment h w = true from by
        rw [← hwv, idAssignment_phpVar]; simpa using hdiag] at hj
      simp at hj
    · have hne : phpVar h h (pigeonOf w hw) j ≠ w := by
        intro he
        exact hjj (phpVar_inj (he.trans hwv.symm)).2
      rw [flipAt_ne _ hne, idAssignment_phpVar] at hj
      have hij : ¬ ((pigeonOf w hw).val = j.val) := by
        intro he
        refine hjj (Fin.ext ?_)
        omega
      simp [hij] at hj
  · -- Flipping a `0`: pigeons `pigeonOf w` and `holeOf w`'s value now share
    -- hole `holeOf w`.
    have hval0 : flipAt (idAssignment h) w
        (phpVar h h (pigeonOf w hw) (holeOf w hw)) = true := by
      rw [hwv, flipAt_self]
      rw [show idAssignment h w = false from by
        rw [← hwv, idAssignment_phpVar]; simpa using hdiag]
      rfl
    have hne01 : (⟨(holeOf w hw).val, (holeOf w hw).isLt⟩ : Fin h) ≠
        pigeonOf w hw := by
      intro he
      exact hdiag ((congrArg Fin.val he).symm)
    have hval1 : flipAt (idAssignment h) w
        (phpVar h h ⟨(holeOf w hw).val, (holeOf w hw).isLt⟩ (holeOf w hw)) =
          true := by
      have hne : phpVar h h ⟨(holeOf w hw).val, (holeOf w hw).isLt⟩
          (holeOf w hw) ≠ w := by
        intro he
        exact hne01 (phpVar_inj (he.trans hwv.symm)).1
      rw [flipAt_ne _ hne, idAssignment_phpVar]
      simp
    rcases Nat.lt_or_ge (pigeonOf w hw).val (holeOf w hw).val with hlt | hge
    · have hclause := htrue _ (collisionClause_mem_fullPHPClauses
        (pigeonOf w hw) ⟨(holeOf w hw).val, (holeOf w hw).isLt⟩ (holeOf w hw)
        (by simpa using hlt))
      rw [eval_collisionClause, hval0, hval1] at hclause
      simp at hclause
    · have hlt : (holeOf w hw).val < (pigeonOf w hw).val := by
        rcases Nat.lt_or_ge (holeOf w hw).val (pigeonOf w hw).val with h' | h'
        · exact h'
        · exact absurd (Nat.le_antisymm h' hge) hdiag
      have hclause := htrue _ (collisionClause_mem_fullPHPClauses
        ⟨(holeOf w hw).val, (holeOf w hw).isLt⟩ (pigeonOf w hw) (holeOf w hw)
        (by simpa using hlt))
      rw [eval_collisionClause, hval0, hval1] at hclause
      simp at hclause

/-! ## Decision-tree path machinery -/

/-- The variables queried along the path an assignment takes through a tree. -/
def dtPathVars {n : Nat} (a : Assignment n) : DTree n → List (Fin n)
  | .leaf _ => []
  | .node v t0 t1 =>
      v :: (if a v then dtPathVars a t1 else dtPathVars a t0)

theorem dtPathVars_node_false {n : Nat} (a : Assignment n)
    (v : Fin n) (t0 t1 : DTree n) (hav : a v = false) :
    dtPathVars a (DTree.node v t0 t1) = v :: dtPathVars a t0 := by
  simp [dtPathVars, hav]

theorem dtPathVars_node_true {n : Nat} (a : Assignment n)
    (v : Fin n) (t0 t1 : DTree n) (hav : a v = true) :
    dtPathVars a (DTree.node v t0 t1) = v :: dtPathVars a t1 := by
  simp [dtPathVars, hav]

theorem dtPathVars_length_le_depth {n : Nat} (a : Assignment n) :
    ∀ T : DTree n, (dtPathVars a T).length ≤ dtDepth T
  | .leaf _ => Nat.zero_le _
  | .node v t0 t1 => by
      have h0 := dtPathVars_length_le_depth a t0
      have h1 := dtPathVars_length_le_depth a t1
      have hm0 : dtDepth t0 ≤ max (dtDepth t0) (dtDepth t1) :=
        Nat.le_max_left _ _
      have hm1 : dtDepth t1 ≤ max (dtDepth t0) (dtDepth t1) :=
        Nat.le_max_right _ _
      cases hav : a v with
      | false =>
          rw [dtPathVars_node_false a v t0 t1 hav, dtDepth_node]
          simp only [List.length_cons]
          omega
      | true =>
          rw [dtPathVars_node_true a v t0 t1 hav, dtDepth_node]
          simp only [List.length_cons]
          omega

/-- Flipping a variable not queried on the assignment's path does not change
the tree's output. -/
theorem dtEval_flipAt_of_not_mem_path {n : Nat} (a : Assignment n)
    (w : Fin n) :
    ∀ T : DTree n, w ∉ dtPathVars a T →
      dtEval (flipAt a w) T = dtEval a T
  | .leaf _, _ => rfl
  | .node v t0 t1, hmem => by
      have hvw : v ≠ w := by
        intro he
        apply hmem
        show w ∈ v :: _
        rw [← he]
        exact List.mem_cons_self v _
      have hval : flipAt a w v = a v := flipAt_ne a hvw
      cases hav : a v with
      | false =>
          have htail : w ∉ dtPathVars a t0 := by
            intro hmem'
            apply hmem
            rw [dtPathVars_node_false a v t0 t1 hav]
            exact List.mem_cons_of_mem v hmem'
          have := dtEval_flipAt_of_not_mem_path a w t0 htail
          simpa [hval, hav] using this
      | true =>
          have htail : w ∉ dtPathVars a t1 := by
            intro hmem'
            apply hmem
            rw [dtPathVars_node_true a v t0 t1 hav]
            exact List.mem_cons_of_mem v hmem'
          have := dtEval_flipAt_of_not_mem_path a w t1 htail
          simpa [hval, hav] using this

/-- A duplicate-free list longer than another has a member outside it. -/
private theorem exists_not_mem_of_short {n : Nat}
    (L : List (Fin n)) (hnd : L.Nodup) (P : List (Fin n))
    (hlt : P.length < L.length) :
    ∃ w ∈ L, w ∉ P := by
  by_contra hno
  have hsub : L ⊆ P := by
    intro w hw
    by_contra hnp
    exact hno ⟨w, hw, hnp⟩
  have := (List.Nodup.subperm hnd hsub).length_le
  omega

/-! ## The family depth-floor boundary and theorem -/

/-- The `h x h` boundary: full view, empty restriction family, floor `h * h`. -/
def fullPHPBoundary (h : Nat) : PHPDepthFloorBoundary h h where
  view := fullPHPView h
  restrictionFamily := [emptyRestriction h]
  depthFloor := h * h

/-- **The family Boolean depth floor (evasiveness of satisfiable PHP).**
For every `h`, any decision tree computing the `h x h` pigeonhole Boolean
function under the empty restriction has depth at least `h * h` — the first
family instance of `PHPDepthFloorStatement` beyond the `1 x 1` boundary, at
the maximal floor.  Elementary sensitivity argument; see the module header
for scope (empty restriction family only; not a Frege/PHP bound). -/
theorem fullPHPBoundary_depthFloor (h : Nat) :
    PHPDepthFloorStatement (fullPHPBoundary h) := by
  intro ρ hρ T hT
  have hρe : ρ = emptyRestriction h := by
    simpa [fullPHPBoundary] using hρ
  subst hρe
  show h * h ≤ dtDepth T
  by_contra hlt
  push_neg at hlt
  -- The tree computes the unrestricted formula on every assignment.
  have hcomp : ∀ a : Assignment (Nat.succ (h * h)),
      dtEval a T = eval a (restrictedPHPFormula (fullPHPView h)) := by
    intro a
    have := hT a (agree_emptyRestriction a)
    rwa [eval_restrict _ _ _ (agree_emptyRestriction a)] at this
  -- Some PHP variable is unqueried on the identity path.
  have hpath : (dtPathVars (idAssignment h) T).length < h * h := by
    have := dtPathVars_length_le_depth (idAssignment h) T
    omega
  obtain ⟨w, hwmem, hwnot⟩ := exists_not_mem_of_short (allPHPVars h h)
    (allPHPVars_nodup h h) (dtPathVars (idAssignment h) T)
    (by rwa [allPHPVars_length])
  have hwlt : w.val < h * h := mem_allPHPVars_val_lt hwmem
  -- Flipping it leaves the output unchanged but flips the function.
  have hsame := dtEval_flipAt_of_not_mem_path (idAssignment h) w T hwnot
  have htrue : dtEval (idAssignment h) T = true := by
    rw [hcomp, eval_idAssignment_true]
  have hfalse : dtEval (flipAt (idAssignment h) w) T = false := by
    rw [hcomp, eval_flip_idAssignment_false w hwlt]
  rw [htrue, hfalse] at hsame
  exact Bool.noConfusion hsame

/-! ## Non-vacuity: a correct tree exists -/

/-- Build a decision tree computing an arbitrary Boolean function by querying
the given variables in order. -/
def dtOfFun {n : Nat} (f : Assignment n → Bool) :
    List (Fin n) → Assignment n → DTree n
  | [], acc => .leaf (f acc)
  | v :: rest, acc =>
      .node v (dtOfFun f rest (updAcc acc v false))
        (dtOfFun f rest (updAcc acc v true))

theorem dtOfFun_eval {n : Nat} (f : Assignment n → Bool)
    (a : Assignment n) :
    ∀ (order : List (Fin n)) (acc : Assignment n),
      (∀ v : Fin n, v ∈ order ∨ acc v = a v) →
      dtEval a (dtOfFun f order acc) = f a := by
  intro order
  induction order with
  | nil =>
      intro acc hinv
      show f acc = f a
      congr 1
      funext v
      rcases hinv v with hmem | hacc
      · exact absurd hmem (List.not_mem_nil v)
      · exact hacc
  | cons v rest ih =>
      intro acc hinv
      have hstep : ∀ b : Bool, a v = b →
          dtEval a (dtOfFun f rest (updAcc acc v b)) = f a := by
        intro b hb
        apply ih
        intro u
        by_cases huv : u = v
        · right
          subst huv
          simp [updAcc, hb]
        · rcases hinv u with hmem | hacc
          · rcases List.mem_cons.mp hmem with hveq | hrest
            · exact absurd hveq huv
            · exact Or.inl hrest
          · right
            simpa [updAcc, huv] using hacc
      cases hav : a v with
      | false =>
          have := hstep false hav
          simpa [dtOfFun, dtEval, hav] using this
      | true =>
          have := hstep true hav
          simpa [dtOfFun, dtEval, hav] using this

theorem dtOfFun_depth {n : Nat} (f : Assignment n → Bool) :
    ∀ (order : List (Fin n)) (acc : Assignment n),
      dtDepth (dtOfFun f order acc) = order.length
  | [], _ => rfl
  | v :: rest, acc => by
      simp [dtOfFun, dtDepth, dtOfFun_depth f rest, Nat.max_self,
        Nat.add_comm]

/-- **Non-vacuity of the family boundary.**  A decision tree satisfying the
boundary's correctness hypothesis exists (depth `h*h + 1`, querying every
ambient variable), so the floor constrains a nonempty class. -/
theorem fullPHPBoundary_correctTree_exists (h : Nat) :
    ∃ T : DTree (Nat.succ (h * h)),
      (∀ a : Assignment (Nat.succ (h * h)),
        Agree (emptyRestriction h) a →
        dtEval a T =
          eval a (restrict (emptyRestriction h)
            (restrictedPHPFormula (fullPHPView h)))) ∧
      dtDepth T = h * h + 1 := by
  refine ⟨dtOfFun
    (fun a => eval a (restrict (emptyRestriction h)
      (restrictedPHPFormula (fullPHPView h))))
    (finList (Nat.succ (h * h))) (fun _ => false), fun a _ => ?_, ?_⟩
  · apply dtOfFun_eval
    intro v
    exact Or.inl (mem_finList _ v)
  · rw [dtOfFun_depth, finList_length]

end PHPBooleanDepthFloor
end PvNP
