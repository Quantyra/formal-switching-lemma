import PvNP.PHPCNFCoverage

/-!
# Parameterized PHP falsified-clause search floor of `2h`

The falsified-clause search problem for the `p x h` pigeonhole view, its
parameterized output type, and the search-query depth floor `2 * h` (believed
tight; tightness was checked only by informal exhaustive search at the
`2 x 1` and `3 x 2` instances and is NOT formalized here)
via a stateful adversary: answer `false`, except answer `true` when the
queried variable is the last unrecorded variable of its pigeon and all its
other variables are recorded `false`.  Every forced `true` costs `h` recorded
variables on one pigeon, and a valid collision output needs forced trues on
two distinct pigeons, hence at least `2 * h` queries.

The adversary is packaged through a REUSABLE generic stateful floor lemma
(`queryTree_depth_floor_of_stateful_adversary`), extending the stateless
generic depth-3 lemma of `RestrictedPHPFloor`.

## HONEST SCOPE STATEMENT (read this)

* This is a decision-tree/query depth floor for the falsified-clause SEARCH
  problem of the pigeonhole family.  It is NOT a Frege/PHP proof-size or
  proof-depth lower bound, NOT an NP or circuit lower bound, and NOT a
  statement about P vs NP.  A positive Boolean depth floor for the
  identically false PHP formula would be false and is not claimed.
* The floor `2 * h` is stated for every `p, h`; genuine (non-vacuous) content
  requires a correct search tree to exist, which holds for `p > h` and is
  witnessed concretely at the `3 x 2` instance below.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPSearchFloor

open CNFModel
open RestrictedPHPFloor

/-! ## Parameterized falsified-clause outputs -/

/-- Outputs of the `p x h` PHP falsified-clause search problem: a pigeon whose
clause is falsified, or a same-hole collision. -/
inductive PHPFalsifiedClause (p h : Nat) where
  | pigeon (i : Fin p)
  | collision (i k : Fin p) (j : Fin h)
  deriving DecidableEq, Repr

namespace PHPFalsifiedClause

/-- Validity: the named clause of the `p x h` PHP CNF is falsified. -/
def Valid {p h : Nat} (a : Assignment (Nat.succ (p * h))) :
    PHPFalsifiedClause p h → Prop
  | pigeon i => ∀ j : Fin h, a (phpVar p h i j) = false
  | collision i k j =>
      i ≠ k ∧ a (phpVar p h i j) = true ∧ a (phpVar p h k j) = true

end PHPFalsifiedClause

/-! ## `phpVar` arithmetic -/

theorem phpVar_val_lt {p h : Nat} (i : Fin p) (j : Fin h) :
    i.val * h + j.val < p * h := by
  have h1 : i.val * h + j.val < (i.val + 1) * h := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left j.isLt _
  have h2 : (i.val + 1) * h ≤ p * h :=
    Nat.mul_le_mul_right h (Nat.succ_le_of_lt i.isLt)
  exact Nat.lt_of_lt_of_le h1 h2

theorem phpVar_val {p h : Nat} (i : Fin p) (j : Fin h) :
    (phpVar p h i j).val = i.val * h + j.val := by
  show (i.val * h + j.val) % Nat.succ (p * h) = i.val * h + j.val
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (phpVar_val_lt i j))

private theorem hpos_of_lt_mul {p h v : Nat} (hv : v < p * h) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with h0 | h1
  · subst h0; omega
  · exact h1

/-- Pigeon index of an ambient PHP variable. -/
def pigeonOf {p h : Nat} (v : Fin (Nat.succ (p * h))) (hv : v.val < p * h) :
    Fin p :=
  ⟨v.val / h, (Nat.div_lt_iff_lt_mul (hpos_of_lt_mul hv)).mpr hv⟩

/-- Hole index of an ambient PHP variable. -/
def holeOf {p h : Nat} (v : Fin (Nat.succ (p * h))) (hv : v.val < p * h) :
    Fin h :=
  ⟨v.val % h, Nat.mod_lt _ (hpos_of_lt_mul hv)⟩

theorem phpVar_pigeonOf_holeOf {p h : Nat} (v : Fin (Nat.succ (p * h)))
    (hv : v.val < p * h) :
    phpVar p h (pigeonOf v hv) (holeOf v hv) = v := by
  apply Fin.ext
  rw [phpVar_val]
  show v.val / h * h + v.val % h = v.val
  rw [Nat.mul_comm]
  exact Nat.div_add_mod v.val h

private theorem mul_add_div_eq {i j h : Nat} (hh : 0 < h) (hj : j < h) :
    (i * h + j) / h = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right j i hh, Nat.div_eq_of_lt hj]
  omega

private theorem mul_add_mod_eq {i j h : Nat} (hj : j < h) :
    (i * h + j) % h = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hj

theorem pigeonOf_phpVar {p h : Nat} (i : Fin p) (j : Fin h)
    (hv : (phpVar p h i j).val < p * h) :
    pigeonOf (phpVar p h i j) hv = i := by
  apply Fin.ext
  show (phpVar p h i j).val / h = i.val
  rw [phpVar_val]
  exact mul_add_div_eq (hpos_of_lt_mul (h := h) (by rw [phpVar_val] at hv; exact hv)) j.isLt

theorem holeOf_phpVar {p h : Nat} (i : Fin p) (j : Fin h)
    (hv : (phpVar p h i j).val < p * h) :
    holeOf (phpVar p h i j) hv = j := by
  apply Fin.ext
  show (phpVar p h i j).val % h = j.val
  rw [phpVar_val]
  exact mul_add_mod_eq j.isLt

theorem phpVar_lt {p h : Nat} (i : Fin p) (j : Fin h) :
    (phpVar p h i j).val < p * h := by
  rw [phpVar_val]
  exact phpVar_val_lt i j

theorem phpVar_inj {p h : Nat} {i i' : Fin p} {j j' : Fin h}
    (heq : phpVar p h i j = phpVar p h i' j') : i = i' ∧ j = j' := by
  have hval : i.val * h + j.val = i'.val * h + j'.val := by
    have := congrArg Fin.val heq
    rwa [phpVar_val, phpVar_val] at this
  have hh : 0 < h := Nat.pos_of_ne_zero (by
    intro h0
    subst h0
    exact absurd j.isLt (Nat.not_lt_zero _))
  constructor
  · apply Fin.ext
    have := congrArg (· / h) hval
    simpa [mul_add_div_eq hh j.isLt, mul_add_div_eq hh j'.isLt] using this
  · apply Fin.ext
    have := congrArg (· % h) hval
    simpa [mul_add_mod_eq j.isLt, mul_add_mod_eq j'.isLt] using this

/-! ## `finList` support lemmas -/

theorem mem_finList (n : Nat) (v : Fin n) : v ∈ finList n := by
  rw [finList, List.mem_pmap]
  exact ⟨v.val, List.mem_range.mpr v.isLt, rfl⟩

theorem finList_nodup (n : Nat) : (finList n).Nodup := by
  rw [finList]
  refine List.Nodup.pmap ?_ (List.nodup_range n)
  intro a ha b hb hab
  exact congrArg Fin.val hab

theorem finList_length (n : Nat) : (finList n).length = n := by
  rw [finList, List.length_pmap, List.length_range]

/-- A duplicate-free list of predicate-satisfying variables bounds the
predicate count over all variables. -/
theorem length_le_countP_of_nodup {n : Nat} (L : List (Fin n))
    (hnd : L.Nodup) (pred : Fin n → Bool)
    (hall : ∀ v ∈ L, pred v = true) :
    L.length ≤ (finList n).countP pred := by
  rw [List.countP_eq_length_filter]
  have hsub : L ⊆ (finList n).filter pred := by
    intro v hv
    rw [List.mem_filter]
    exact ⟨mem_finList n v, hall v hv⟩
  exact (List.Nodup.subperm hnd hsub).length_le

private theorem countP_le_of_flip {α : Type _} [DecidableEq α] (v : α)
    (p q : α → Bool) (hagree : ∀ x, x ≠ v → q x = p x) :
    ∀ l : List α, l.countP q ≤ l.countP p + l.count v
  | [] => Nat.le_refl _
  | x :: l => by
      have ih := countP_le_of_flip v p q hagree l
      by_cases hxv : x = v
      · subst hxv
        rw [List.countP_cons, List.countP_cons, List.count_cons_self]
        have hq : (if q x = true then 1 else 0) ≤ 1 := by split <;> omega
        have hp : 0 ≤ (if p x = true then 1 else 0) := Nat.zero_le _
        omega
      · rw [List.countP_cons, List.countP_cons,
          List.count_cons_of_ne (fun h => hxv h.symm)]
        rw [hagree x hxv]
        omega

/-! ## Generic stateful adversary floor -/

/-- **Reusable generic stateful adversary floor.**  Given an adversary state
with an invariant preserved by updates, a computable answer function steering
which branch is followed, a step measure increasing by at most one per query,
and leaf refutability below the budget, every correct output-valued query tree
has worst-case depth at least the budget minus the starting measure.  This is
generic certificate-search infrastructure only; it is not a Boolean or
Frege/PHP lower bound. -/
theorem queryTree_depth_floor_of_stateful_adversary {n : Nat} {α : Type}
    {State : Type}
    (Valid : Assignment n → α → Prop) (Inv : State → Prop)
    (answer : State → Fin n → Bool) (update : State → Fin n → State)
    (Consistent : State → Assignment n → Prop) (measure : State → Nat)
    (budget : Nat)
    (hInv_update : ∀ s v, Inv s → Inv (update s v))
    (hmeasure_update : ∀ s v, measure (update s v) ≤ measure s + 1)
    (hconsistent_update : ∀ s v a, Consistent (update s v) a →
      Consistent s a ∧ a v = answer s v)
    (hleaf : ∀ s, Inv s → measure s < budget → ∀ out : α,
      ∃ a : Assignment n, Consistent s a ∧ ¬ Valid a out) :
    ∀ (T : QueryTree n α) (s : State), Inv s →
      (∀ a : Assignment n, Consistent s a → Valid a (queryEval a T)) →
      budget ≤ measure s + queryDepth T := by
  intro T
  induction T with
  | leaf out =>
      intro s hInv hT
      by_cases hm : budget ≤ measure s
      · exact Nat.le_trans hm (Nat.le_add_right _ _)
      · exfalso
        obtain ⟨a, hca, hnv⟩ := hleaf s hInv (Nat.lt_of_not_le hm) out
        exact hnv (by simpa [queryEval] using hT a hca)
  | node v t0 t1 ih0 ih1 =>
      intro s hInv hT
      have hdepth : queryDepth (QueryTree.node v t0 t1) =
          max (queryDepth t0) (queryDepth t1) + 1 := rfl
      cases hb : answer s v with
      | false =>
          have hcorrect : ∀ a, Consistent (update s v) a →
              Valid a (queryEval a t0) := by
            intro a hca
            obtain ⟨hcs, hav⟩ := hconsistent_update s v a hca
            rw [hb] at hav
            have hval := hT a hcs
            rw [show queryEval a (QueryTree.node v t0 t1) = queryEval a t0 from
              by simp [queryEval, hav]] at hval
            exact hval
          have hIH := ih0 (update s v) (hInv_update s v hInv) hcorrect
          have hup := hmeasure_update s v
          have hd : queryDepth t0 ≤ max (queryDepth t0) (queryDepth t1) :=
            Nat.le_max_left _ _
          omega
      | true =>
          have hcorrect : ∀ a, Consistent (update s v) a →
              Valid a (queryEval a t1) := by
            intro a hca
            obtain ⟨hcs, hav⟩ := hconsistent_update s v a hca
            rw [hb] at hav
            have hval := hT a hcs
            rw [show queryEval a (QueryTree.node v t0 t1) = queryEval a t1 from
              by simp [queryEval, hav]] at hval
            exact hval
          have hIH := ih1 (update s v) (hInv_update s v hInv) hcorrect
          have hup := hmeasure_update s v
          have hd : queryDepth t1 ≤ max (queryDepth t0) (queryDepth t1) :=
            Nat.le_max_right _ _
          omega

/-! ## The PHP forced-true adversary -/

/-- Adversary state: a partial record of answered variables. -/
def PHPState (p h : Nat) := Fin (Nat.succ (p * h)) → Option Bool

/-- The queried variable is the last unrecorded variable of its pigeon and all
its other variables are recorded `false`. -/
def phpForced (p h : Nat) (s : PHPState p h) (v : Fin (Nat.succ (p * h)))
    (hv : v.val < p * h) : Bool :=
  (finList h).all (fun j' =>
    decide (j' = holeOf v hv) ||
      decide (s (phpVar p h (pigeonOf v hv) j') = some false))

/-- Adversary answer: repeat recorded answers; otherwise `false`, except
`true` on a forced last pigeon variable.  Ambient non-PHP variables are always
answered `false`. -/
def phpAnswer (p h : Nat) (s : PHPState p h) (v : Fin (Nat.succ (p * h))) :
    Bool :=
  match s v with
  | some b => b
  | none => if hv : v.val < p * h then phpForced p h s v hv else false

/-- Adversary update: record the answer at a newly queried variable. -/
def phpUpdate (p h : Nat) (s : PHPState p h) (v : Fin (Nat.succ (p * h))) :
    PHPState p h :=
  match s v with
  | some _ => s
  | none => fun w => if w = v then some (phpAnswer p h s v) else s w

/-- Consistency: the assignment agrees with every recorded answer. -/
def PHPConsistent (p h : Nat) (s : PHPState p h)
    (a : Assignment (Nat.succ (p * h))) : Prop :=
  ∀ v b, s v = some b → a v = b

/-- Measure: number of recorded variables. -/
def phpMeasure (p h : Nat) (s : PHPState p h) : Nat :=
  (finList (Nat.succ (p * h))).countP (fun v => (s v).isSome)

/-- Adversary invariant: every recorded `true` is a forced last pigeon
variable (its pigeon's other variables are recorded `false`), and no pigeon is
fully recorded `false`. -/
def PHPInv (p h : Nat) (s : PHPState p h) : Prop :=
  (∀ v : Fin (Nat.succ (p * h)), s v = some true →
      ∃ hv : v.val < p * h,
        ∀ j : Fin h, j ≠ holeOf v hv →
          s (phpVar p h (pigeonOf v hv) j) = some false) ∧
    (∀ i : Fin p, ∃ j : Fin h, s (phpVar p h i j) ≠ some false)

theorem phpForced_eq_true_iff {p h : Nat} (s : PHPState p h)
    (v : Fin (Nat.succ (p * h))) (hv : v.val < p * h) :
    phpForced p h s v hv = true ↔
      ∀ j' : Fin h, j' ≠ holeOf v hv →
        s (phpVar p h (pigeonOf v hv) j') = some false := by
  rw [phpForced, List.all_eq_true]
  constructor
  · intro hall j' hj'
    rcases Bool.or_eq_true _ _ |>.mp (hall j' (mem_finList h j')) with h1 | h2
    · exact absurd (of_decide_eq_true h1) hj'
    · exact of_decide_eq_true h2
  · intro hcond j' _
    by_cases hj' : j' = holeOf v hv
    · simp [hj']
    · simp [hj', hcond j' hj']

theorem phpForced_eq_false_exists {p h : Nat} (s : PHPState p h)
    (v : Fin (Nat.succ (p * h))) (hv : v.val < p * h)
    (hb : phpForced p h s v hv = false) :
    ∃ j' : Fin h, j' ≠ holeOf v hv ∧
      s (phpVar p h (pigeonOf v hv) j') ≠ some false := by
  by_contra hno
  have hcond : ∀ j' : Fin h, j' ≠ holeOf v hv →
      s (phpVar p h (pigeonOf v hv) j') = some false := by
    intro j' hj'
    by_contra hs
    exact hno ⟨j', hj', hs⟩
  rw [(phpForced_eq_true_iff s v hv).mpr hcond] at hb
  exact Bool.noConfusion hb

/-! ## Adversary hypotheses discharged -/

private theorem phpUpdate_eq_of_some {p h : Nat} {s : PHPState p h}
    {v : Fin (Nat.succ (p * h))} {b : Bool} (hsv : s v = some b) :
    phpUpdate p h s v = s := by
  unfold phpUpdate
  rw [hsv]

private theorem phpUpdate_eq_of_none {p h : Nat} {s : PHPState p h}
    {v : Fin (Nat.succ (p * h))} (hsv : s v = none) :
    phpUpdate p h s v =
      fun w => if w = v then some (phpAnswer p h s v) else s w := by
  unfold phpUpdate
  rw [hsv]

theorem phpMeasure_update_le {p h : Nat} (s : PHPState p h)
    (v : Fin (Nat.succ (p * h))) :
    phpMeasure p h (phpUpdate p h s v) ≤ phpMeasure p h s + 1 := by
  rcases hsv : s v with _ | b
  · rw [phpUpdate_eq_of_none hsv]
    have hflip : ∀ x, x ≠ v →
        (((fun w => if w = v then some (phpAnswer p h s v) else s w) x).isSome) =
          ((s x).isSome) := by
      intro x hx
      simp [hx]
    calc (finList (Nat.succ (p * h))).countP
          (fun x => ((fun w => if w = v then some (phpAnswer p h s v) else s w) x).isSome)
        ≤ (finList (Nat.succ (p * h))).countP (fun x => (s x).isSome) +
            (finList (Nat.succ (p * h))).count v :=
          countP_le_of_flip v _ _ hflip _
      _ ≤ (finList (Nat.succ (p * h))).countP (fun x => (s x).isSome) + 1 := by
          have := (List.nodup_iff_count_le_one.mp
            (finList_nodup (Nat.succ (p * h)))) v
          omega
  · rw [phpUpdate_eq_of_some hsv]
    exact Nat.le_succ _

theorem phpConsistent_update {p h : Nat} (s : PHPState p h)
    (v : Fin (Nat.succ (p * h))) (a : Assignment (Nat.succ (p * h)))
    (hc : PHPConsistent p h (phpUpdate p h s v) a) :
    PHPConsistent p h s a ∧ a v = phpAnswer p h s v := by
  rcases hsv : s v with _ | b
  · rw [phpUpdate_eq_of_none hsv] at hc
    constructor
    · intro w b' hw
      by_cases hwv : w = v
      · subst hwv
        rw [hsv] at hw
        exact Option.noConfusion hw
      · exact hc w b' (by simpa [hwv] using hw)
    · exact hc v _ (by simp)
  · rw [phpUpdate_eq_of_some hsv] at hc
    refine ⟨hc, ?_⟩
    have hav := hc v b hsv
    rw [hav]
    unfold phpAnswer
    rw [hsv]

theorem phpInv_update {p h : Nat} (s : PHPState p h)
    (v : Fin (Nat.succ (p * h))) (hInv : PHPInv p h s) :
    PHPInv p h (phpUpdate p h s v) := by
  obtain ⟨h1, h2⟩ := hInv
  rcases hsv : s v with _ | b
  case some => rw [phpUpdate_eq_of_some hsv]; exact ⟨h1, h2⟩
  case none =>
  rw [phpUpdate_eq_of_none hsv]
  set s' : PHPState p h :=
    fun w => if w = v then some (phpAnswer p h s v) else s w with hs'
  have hs'_ne : ∀ w, w ≠ v → s' w = s w := by
    intro w hw
    simp [hs', hw]
  have hs'_v : s' v = some (phpAnswer p h s v) := by
    simp [hs']
  -- Old recorded-`true` conditions survive: their witnesses are recorded
  -- `false` in `s`, hence differ from the unrecorded `v`.
  have hold : ∀ w, s w = some true →
      ∃ hw : w.val < p * h,
        ∀ j : Fin h, j ≠ holeOf w hw →
          s' (phpVar p h (pigeonOf w hw) j) = some false := by
    intro w hwt
    obtain ⟨hw, hcond⟩ := h1 w hwt
    refine ⟨hw, fun j hj => ?_⟩
    have hne : phpVar p h (pigeonOf w hw) j ≠ v := by
      intro he
      have := hcond j hj
      rw [he, hsv] at this
      exact Option.noConfusion this
    rw [hs'_ne _ hne]
    exact hcond j hj
  by_cases hv : v.val < p * h
  · have hvij : phpVar p h (pigeonOf v hv) (holeOf v hv) = v :=
      phpVar_pigeonOf_holeOf v hv
    have hans : phpAnswer p h s v = phpForced p h s v hv := by
      unfold phpAnswer
      rw [hsv]
      rw [dif_pos hv]
    cases hb : phpForced p h s v hv with
    | true =>
        have hforced := (phpForced_eq_true_iff s v hv).mp hb
        constructor
        · intro w hwt
          by_cases hwv : w = v
          · subst hwv
            refine ⟨hv, fun j hj => ?_⟩
            have hne : phpVar p h (pigeonOf w hv) j ≠ w := by
              intro he
              exact hj (phpVar_inj (he.trans hvij.symm)).2
            rw [hs'_ne _ hne]
            exact hforced j hj
          · exact hold w (by rw [hs'_ne _ hwv] at hwt; exact hwt)
        · intro i'
          by_cases hii : i' = pigeonOf v hv
          · subst hii
            refine ⟨holeOf v hv, ?_⟩
            rw [hvij, hs'_v, hans, hb]
            simp
          · obtain ⟨j₀, hj₀⟩ := h2 i'
            refine ⟨j₀, ?_⟩
            have hne : phpVar p h i' j₀ ≠ v := by
              intro he
              exact hii (phpVar_inj (he.trans hvij.symm)).1
            rw [hs'_ne _ hne]
            exact hj₀
    | false =>
        obtain ⟨j', hj'ne, hj'⟩ := phpForced_eq_false_exists s v hv hb
        constructor
        · intro w hwt
          by_cases hwv : w = v
          · subst hwv
            rw [hs'_v, hans, hb] at hwt
            exact absurd hwt (by simp)
          · exact hold w (by rw [hs'_ne _ hwv] at hwt; exact hwt)
        · intro i'
          by_cases hii : i' = pigeonOf v hv
          · subst hii
            refine ⟨j', ?_⟩
            have hne : phpVar p h (pigeonOf v hv) j' ≠ v := by
              intro he
              exact hj'ne (phpVar_inj (he.trans hvij.symm)).2
            rw [hs'_ne _ hne]
            exact hj'
          · obtain ⟨j₀, hj₀⟩ := h2 i'
            refine ⟨j₀, ?_⟩
            have hne : phpVar p h i' j₀ ≠ v := by
              intro he
              exact hii (phpVar_inj (he.trans hvij.symm)).1
            rw [hs'_ne _ hne]
            exact hj₀
  · have hans : phpAnswer p h s v = false := by
      unfold phpAnswer
      rw [hsv]
      rw [dif_neg hv]
    constructor
    · intro w hwt
      by_cases hwv : w = v
      · subst hwv
        rw [hs'_v, hans] at hwt
        exact absurd hwt (by simp)
      · exact hold w (by rw [hs'_ne _ hwv] at hwt; exact hwt)
    · intro i'
      obtain ⟨j₀, hj₀⟩ := h2 i'
      refine ⟨j₀, ?_⟩
      have hne : phpVar p h i' j₀ ≠ v := by
        intro he
        exact hv (by rw [← he]; exact phpVar_lt i' j₀)
      rw [hs'_ne _ hne]
      exact hj₀

/-! ## Leaf refutability -/

private theorem option_eq_some_false {o : Option Bool}
    (hn : o ≠ none) (ht : o ≠ some true) : o = some false := by
  rcases o with _ | b
  · exact absurd rfl hn
  · cases b
    · rfl
    · exact absurd rfl ht

/-- The default completion of a partial record. -/
private def completeD {p h : Nat} (s : PHPState p h) :
    Assignment (Nat.succ (p * h)) :=
  fun w => (s w).getD false

private theorem completeD_consistent {p h : Nat} (s : PHPState p h) :
    PHPConsistent p h s (completeD s) := by
  intro w b hw
  simp [completeD, hw]

theorem phpLeaf_refutable {p h : Nat} (s : PHPState p h)
    (hInv : PHPInv p h s) (hm : phpMeasure p h s < 2 * h)
    (out : PHPFalsifiedClause p h) :
    ∃ a : Assignment (Nat.succ (p * h)),
      PHPConsistent p h s a ∧ ¬ PHPFalsifiedClause.Valid a out := by
  obtain ⟨h1, h2⟩ := hInv
  cases out with
  | pigeon i =>
      by_cases htrue : ∃ j : Fin h, s (phpVar p h i j) = some true
      · obtain ⟨j, hj⟩ := htrue
        refine ⟨completeD s, completeD_consistent s, ?_⟩
        intro hval
        have := hval j
        simp [completeD, hj] at this
      · by_cases hnone : ∃ j : Fin h, s (phpVar p h i j) = none
        · obtain ⟨j, hj⟩ := hnone
          refine ⟨fun w => if w = phpVar p h i j then true else (s w).getD false,
            ?_, ?_⟩
          · intro w b hw
            by_cases hwv : w = phpVar p h i j
            · rw [hwv, hj] at hw
              exact Option.noConfusion hw
            · simp [hwv, hw]
          · intro hval
            have := hval j
            simp at this
        · exfalso
          obtain ⟨j₀, hj₀⟩ := h2 i
          exact hj₀ (option_eq_some_false
            (fun hn => hnone ⟨j₀, hn⟩) (fun ht => htrue ⟨j₀, ht⟩))
  | collision i k j =>
      by_cases hti : s (phpVar p h i j) = some true
      · by_cases htk : s (phpVar p h k j) = some true
        · by_cases hik : i = k
          · refine ⟨completeD s, completeD_consistent s, ?_⟩
            intro hval
            exact hval.1 hik
          · exfalso
            obtain ⟨hvi, hci⟩ := h1 _ hti
            obtain ⟨hvk, hck⟩ := h1 _ htk
            rw [pigeonOf_phpVar i j hvi] at hci
            rw [holeOf_phpVar i j hvi] at hci
            rw [pigeonOf_phpVar k j hvk] at hck
            rw [holeOf_phpVar k j hvk] at hck
            have hreci : ∀ j' : Fin h, (s (phpVar p h i j')).isSome = true := by
              intro j'
              by_cases hjj : j' = j
              · subst hjj; rw [hti]; rfl
              · rw [hci j' hjj]; rfl
            have hreck : ∀ j' : Fin h, (s (phpVar p h k j')).isSome = true := by
              intro j'
              by_cases hjj : j' = j
              · subst hjj; rw [htk]; rfl
              · rw [hck j' hjj]; rfl
            set L : List (Fin (Nat.succ (p * h))) :=
              (finList h).map (phpVar p h i) ++ (finList h).map (phpVar p h k)
              with hL
            have hnd : L.Nodup := by
              refine List.Nodup.append ?_ ?_ ?_
              · exact List.Nodup.map
                  (fun j1 j2 he => (phpVar_inj he).2) (finList_nodup h)
              · exact List.Nodup.map
                  (fun j1 j2 he => (phpVar_inj he).2) (finList_nodup h)
              · intro x hx1 hx2
                rcases List.mem_map.mp hx1 with ⟨j1, _, he1⟩
                rcases List.mem_map.mp hx2 with ⟨j2, _, he2⟩
                exact hik (phpVar_inj (he1.trans he2.symm)).1
            have hall : ∀ v ∈ L, (s v).isSome = true := by
              intro v hv
              rcases List.mem_append.mp hv with hv | hv
              · rcases List.mem_map.mp hv with ⟨j', _, he⟩
                rw [← he]
                exact hreci j'
              · rcases List.mem_map.mp hv with ⟨j', _, he⟩
                rw [← he]
                exact hreck j'
            have hlen : L.length = 2 * h := by
              rw [hL, List.length_append, List.length_map, List.length_map,
                finList_length]
              omega
            have := length_le_countP_of_nodup L hnd _ hall
            rw [hlen] at this
            exact absurd (Nat.lt_of_lt_of_le hm this) (Nat.lt_irrefl _)
        · refine ⟨completeD s, completeD_consistent s, ?_⟩
          intro hval
          have h2' := hval.2.2
          rcases hso : s (phpVar p h k j) with _ | b
          · simp [completeD, hso] at h2'
          · cases b
            · simp [completeD, hso] at h2'
            · exact htk hso
      · refine ⟨completeD s, completeD_consistent s, ?_⟩
        intro hval
        have h2' := hval.2.1
        rcases hso : s (phpVar p h i j) with _ | b
        · simp [completeD, hso] at h2'
        · cases b
          · simp [completeD, hso] at h2'
          · exact hti hso

/-! ## The parameterized floor -/

/-- **Parameterized `p x h` PHP falsified-clause search depth floor of
`2 * h`.**  Any output-valued query tree that always returns a falsified
clause of the `p x h` PHP view makes at least `2 * h` queries in the worst
case.  This is a bounded certificate-search statement for the PHP search
FAMILY; it is not a Frege/PHP lower bound. -/
theorem phpFalsifiedClauseSearchDepthFloor (p h : Nat)
    (T : QueryTree (Nat.succ (p * h)) (PHPFalsifiedClause p h))
    (hT : ∀ a : Assignment (Nat.succ (p * h)),
      PHPFalsifiedClause.Valid a (queryEval a T)) :
    2 * h ≤ queryDepth T := by
  rcases Nat.eq_zero_or_pos h with h0 | hh
  · subst h0
    exact Nat.zero_le _
  · have hInv0 : PHPInv p h (fun _ => none) := by
      constructor
      · intro v hvt
        exact Option.noConfusion hvt
      · intro i
        exact ⟨⟨0, hh⟩, by simp⟩
    have hmain := queryTree_depth_floor_of_stateful_adversary
      PHPFalsifiedClause.Valid (PHPInv p h) (phpAnswer p h) (phpUpdate p h)
      (PHPConsistent p h) (phpMeasure p h) (2 * h)
      (fun s v hs => phpInv_update s v hs)
      (fun s v => phpMeasure_update_le s v)
      (fun s v a hc => phpConsistent_update s v a hc)
      (fun s hs hmlt out => phpLeaf_refutable s hs hmlt out)
      T (fun _ => none) hInv0 (fun a _ => hT a)
    have hm0 : phpMeasure p h (fun _ => none) = 0 := by
      rw [phpMeasure]
      rw [List.countP_eq_zero]
      intro v _
      simp
    omega

/-- The parameterized floor as a family instance of the general statement
shape. -/
theorem phpFalsifiedClauseSearchDepthFloorStatement (p h : Nat) :
    FalsifiedClauseSearchDepthFloorStatement (Nat.succ (p * h))
      (PHPFalsifiedClause p h) PHPFalsifiedClause.Valid (2 * h) :=
  fun T hT => phpFalsifiedClauseSearchDepthFloor p h T hT

/-! ## Non-vacuity at `3 x 2` and the strengthened bespoke floor of four -/

/-- Map the outputs of a query tree. -/
def mapTree {n : Nat} {α β : Type} (f : α → β) :
    QueryTree n α → QueryTree n β
  | .leaf out => .leaf (f out)
  | .node v t0 t1 => .node v (mapTree f t0) (mapTree f t1)

theorem queryEval_mapTree {n : Nat} {α β : Type} (f : α → β)
    (a : Assignment n) :
    ∀ T : QueryTree n α, queryEval a (mapTree f T) = f (queryEval a T)
  | .leaf out => rfl
  | .node v t0 t1 => by
      cases hav : a v <;>
        simp [mapTree, queryEval, hav, queryEval_mapTree f a t0,
          queryEval_mapTree f a t1]

theorem queryDepth_mapTree {n : Nat} {α β : Type} (f : α → β) :
    ∀ T : QueryTree n α, queryDepth (mapTree f T) = queryDepth T
  | .leaf out => rfl
  | .node v t0 t1 => by
      simp [mapTree, queryDepth, queryDepth_mapTree f t0,
        queryDepth_mapTree f t1]

/-- Convert the bespoke `3 x 2` outputs into the parameterized outputs. -/
def toParam32 : ThreeTwoPHPFalsifiedClause → PHPFalsifiedClause 3 2
  | .pigeon0 => .pigeon 0
  | .pigeon1 => .pigeon 1
  | .pigeon2 => .pigeon 2
  | .collision01h0 => .collision 0 1 0
  | .collision01h1 => .collision 0 1 1
  | .collision02h0 => .collision 0 2 0
  | .collision02h1 => .collision 0 2 1
  | .collision12h0 => .collision 1 2 0
  | .collision12h1 => .collision 1 2 1

private theorem fin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  rcases j with ⟨jv, hj⟩
  match jv, hj with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-- Bespoke `3 x 2` validity transfers to the parameterized validity. -/
theorem toParam32_valid (a : Assignment (Nat.succ (3 * 2)))
    (o : ThreeTwoPHPFalsifiedClause)
    (hv : ThreeTwoPHPFalsifiedClause.Valid a o) :
    PHPFalsifiedClause.Valid a (toParam32 o) := by
  cases o with
  | pigeon0 =>
      intro j
      rcases fin2_cases j with hj | hj <;> subst hj
      · rw [show phpVar 3 2 0 0 = threeTwoPHPVar00 from by decide]
        exact hv.1
      · rw [show phpVar 3 2 0 1 = threeTwoPHPVar01 from by decide]
        exact hv.2
  | pigeon1 =>
      intro j
      rcases fin2_cases j with hj | hj <;> subst hj
      · rw [show phpVar 3 2 1 0 = threeTwoPHPVar10 from by decide]
        exact hv.1
      · rw [show phpVar 3 2 1 1 = threeTwoPHPVar11 from by decide]
        exact hv.2
  | pigeon2 =>
      intro j
      rcases fin2_cases j with hj | hj <;> subst hj
      · rw [show phpVar 3 2 2 0 = threeTwoPHPVar20 from by decide]
        exact hv.1
      · rw [show phpVar 3 2 2 1 = threeTwoPHPVar21 from by decide]
        exact hv.2
  | collision01h0 =>
      exact ⟨by decide,
        by rw [show phpVar 3 2 0 0 = threeTwoPHPVar00 from by decide]; exact hv.1,
        by rw [show phpVar 3 2 1 0 = threeTwoPHPVar10 from by decide]; exact hv.2⟩
  | collision01h1 =>
      exact ⟨by decide,
        by rw [show phpVar 3 2 0 1 = threeTwoPHPVar01 from by decide]; exact hv.1,
        by rw [show phpVar 3 2 1 1 = threeTwoPHPVar11 from by decide]; exact hv.2⟩
  | collision02h0 =>
      exact ⟨by decide,
        by rw [show phpVar 3 2 0 0 = threeTwoPHPVar00 from by decide]; exact hv.1,
        by rw [show phpVar 3 2 2 0 = threeTwoPHPVar20 from by decide]; exact hv.2⟩
  | collision02h1 =>
      exact ⟨by decide,
        by rw [show phpVar 3 2 0 1 = threeTwoPHPVar01 from by decide]; exact hv.1,
        by rw [show phpVar 3 2 2 1 = threeTwoPHPVar21 from by decide]; exact hv.2⟩
  | collision12h0 =>
      exact ⟨by decide,
        by rw [show phpVar 3 2 1 0 = threeTwoPHPVar10 from by decide]; exact hv.1,
        by rw [show phpVar 3 2 2 0 = threeTwoPHPVar20 from by decide]; exact hv.2⟩
  | collision12h1 =>
      exact ⟨by decide,
        by rw [show phpVar 3 2 1 1 = threeTwoPHPVar11 from by decide]; exact hv.1,
        by rw [show phpVar 3 2 2 1 = threeTwoPHPVar21 from by decide]; exact hv.2⟩

/-- **Non-vacuity of the parameterized floor at `3 x 2`.**  A correct
parameterized search tree exists (the audited fixed bespoke tree, with mapped
outputs). -/
theorem phpFalsifiedClause32_correctTree_exists :
    ∃ T : QueryTree (Nat.succ (3 * 2)) (PHPFalsifiedClause 3 2),
      ∀ a : Assignment (Nat.succ (3 * 2)),
        PHPFalsifiedClause.Valid a (queryEval a T) :=
  ⟨mapTree toParam32 threeTwoPHPFalsifiedClauseQueryTree, fun a => by
    rw [queryEval_mapTree]
    exact toParam32_valid a _
      (threeTwoPHPFalsifiedClauseSearchCorrect_of_evalSelector
        threeTwoPHPFalsifiedClauseQueryTree
        threeTwoPHPFalsifiedClauseQueryTree_evalSelector a)⟩

/-- **Strengthened bespoke `3 x 2` floor of FOUR** (the S2066 floor of three
was not tight; `2 * h = 4` is, by exhaustive search, the exact optimum for
this instance, though tightness is not formalized here). -/
theorem threeTwoPHPFalsifiedClauseSearchDepthFloor_four
    (T : QueryTree (Nat.succ (3 * 2)) ThreeTwoPHPFalsifiedClause)
    (hT : ∀ a : Assignment (Nat.succ (3 * 2)),
      ThreeTwoPHPFalsifiedClause.Valid a (queryEval a T)) :
    4 ≤ queryDepth T := by
  have h4 := phpFalsifiedClauseSearchDepthFloor 3 2 (mapTree toParam32 T)
    (fun a => by
      rw [queryEval_mapTree]
      exact toParam32_valid a _ (hT a))
  rw [queryDepth_mapTree] at h4
  exact h4

end PHPSearchFloor
end PvNP
