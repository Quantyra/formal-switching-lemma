import PvNP.PHPMatchingExtensionEncode
import Mathlib.Data.Finset.Sort

/-!
# GA-3 Stage 2: the star code and the graded per-stage bound (S2187)

Third formal stage of the GA-3 extension-encode rung (S2187 story): the
counting namespace for the encode's G2/G3 components, in the located
design's shape (UF Lemma 6.1 / Beame §5 stars bookkeeping) and the
packet's **syntactic no-support-global form** (pin 3.4): every bound is
closed arithmetic in `w`, `ℓ`, `s`, `j` alone — no DNF, support, or depth
variables occur.

* `tagLast`/`starDataL`/`unstar` — the 2-per-star flattening: a sequence
  of nonempty blocks of `[w]`-positions flattens to one entry per star
  (its position and a last-of-block bit), and the flattening is
  **losslessly decodable** (`unstar_starDataL`) — UF Lemma 6.1's
  injection, proved as a round trip.
* `starData` — the `Finset`-block layer (β-vectors as position sets,
  per the program's L1 convention: marks are σ-positions), with
  `starData_length` (one entry per star) and `starData_inj`.
* **Pin 3.3, standalone code bound** (`mcode_family_card_le`): any
  family of well-formed codes of total star count `j` has at most
  `(2w)^j` members.
* **Pin 3.3 graded form / pin 3.4 syntactic form**
  (`mcode_answers_family_card_le`): any family of (code, answer-stream)
  pairs — the answer stream being `s` names in the square free-vertex
  namespace `[2ℓ]` — of total star count `j` has at most
  `(2w)^j · (2ℓ)^s` members. The `ℓ`-dependence through the answer
  namespace is the DISCLOSED tier-2 content of the located design; the
  tier-3 no-go does not fire (no standalone `h`-power, no support
  variables — syntactically visible in the statement).

**State bounds are abstract code-space cardinalities; no theorem yet
places the realized matching-encode image inside the family.**

Term identification is replay-derived, never code content (pin 3.3's
rider): nothing in this namespace mentions the DNF, and the decoder
consumes positions and block bits only. Pure counting infrastructure:
no trace lemma is used or extended here, no probability statement, no
injectivity claim about the encode itself (GA-4), not a switching lemma,
not Gate A closure, not Frege/PHP, NP/circuit, or P-versus-NP.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingCodeBound

open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode

/-! ## The 2-per-star flattening on list blocks -/

/-- Tag each position of a block, marking the block's last star. -/
def tagLast {w : Nat} : List (Fin w) → List (Fin w × Bool)
  | [] => []
  | [x] => [(x, true)]
  | x :: y :: rest => (x, false) :: tagLast (y :: rest)

theorem tagLast_length {w : Nat} :
    ∀ l : List (Fin w), (tagLast l).length = l.length
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
      rw [show tagLast (x :: y :: rest) =
        (x, false) :: tagLast (y :: rest) from rfl]
      simp [tagLast_length (y :: rest)]

/-- Flatten a block sequence, one entry per star. -/
def starDataL {w : Nat} (bs : List (List (Fin w))) :
    List (Fin w × Bool) :=
  (bs.map tagLast).join

theorem starDataL_nil {w : Nat} :
    starDataL ([] : List (List (Fin w))) = [] := rfl

theorem starDataL_cons {w : Nat} (b : List (Fin w))
    (bs : List (List (Fin w))) :
    starDataL (b :: bs) = tagLast b ++ starDataL bs := rfl

theorem starDataL_length {w : Nat} :
    ∀ bs : List (List (Fin w)),
      (starDataL bs).length = (bs.map List.length).sum
  | [] => rfl
  | b :: bs => by
      rw [starDataL_cons, List.length_append, tagLast_length,
        List.map_cons, List.sum_cons, starDataL_length bs]

/-- The decoder: split the flat star stream at the block bits. -/
def unstar {w : Nat} : List (Fin w × Bool) → List (List (Fin w))
  | [] => []
  | (x, true) :: rest => [x] :: unstar rest
  | (x, false) :: rest =>
      match unstar rest with
      | [] => [[x]]
      | b :: bs => (x :: b) :: bs

/-- One decoded block: the tag of a nonempty block prepends losslessly. -/
theorem unstar_tagLast_append {w : Nat} :
    ∀ (b : List (Fin w)) (rest : List (Fin w × Bool)), b ≠ [] →
      unstar (tagLast b ++ rest) = b :: unstar rest
  | [], _, hne => absurd rfl hne
  | [x], rest, _ => by
      rw [show tagLast [x] = [(x, true)] from rfl]
      rfl
  | x :: y :: b, rest, _ => by
      rw [show tagLast (x :: y :: b) =
        (x, false) :: tagLast (y :: b) from rfl]
      rw [List.cons_append]
      rw [show unstar ((x, false) :: (tagLast (y :: b) ++ rest)) =
        match unstar (tagLast (y :: b) ++ rest) with
        | [] => [[x]]
        | b' :: bs => (x :: b') :: bs from rfl]
      rw [unstar_tagLast_append (y :: b) rest (by simp)]

/-- **UF Lemma 6.1 as a round trip**: the 2-per-star flattening of a
sequence of nonempty blocks decodes back to the sequence. -/
theorem unstar_starDataL {w : Nat} :
    ∀ bs : List (List (Fin w)), (∀ b ∈ bs, b ≠ []) →
      unstar (starDataL bs) = bs
  | [], _ => rfl
  | b :: bs, hne => by
      rw [starDataL_cons,
        unstar_tagLast_append b (starDataL bs)
          (hne b (List.mem_cons_self _ _)),
        unstar_starDataL bs (fun b' hb' =>
          hne b' (List.mem_cons_of_mem _ hb'))]

/-! ## The `Finset`-block layer (β-vectors as position sets) -/

/-- The star data of a β-vector sequence: each block's positions in
increasing order, one entry per star with its last-of-block bit. -/
def starData {w : Nat} (bs : List (Finset (Fin w))) :
    List (Fin w × Bool) :=
  starDataL (bs.map (Finset.sort (· ≤ ·)))

/-- Total star count. -/
def codeSize {w : Nat} (bs : List (Finset (Fin w))) : Nat :=
  (bs.map Finset.card).sum

theorem starData_length {w : Nat} (bs : List (Finset (Fin w))) :
    (starData bs).length = codeSize bs := by
  unfold starData codeSize
  rw [starDataL_length, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  exact Finset.length_sort _

/-- In-range `getD` is `get` (version-stable, by direct induction). -/
theorem getD_eq_get_of_lt {alpha : Type} (l : List alpha) (d : alpha) :
    ∀ (n : Nat) (h : n < l.length), l.getD n d = l.get ⟨n, h⟩ := by
  induction l with
  | nil =>
      intro n h
      cases h
  | cons x xs ih =>
      intro n h
      cases n with
      | zero => rfl
      | succ n' =>
          have h' : n' < xs.length := by simpa using h
          exact ih n' h'

/-- The flattening is injective on well-formed (all-blocks-nonempty)
codes — the standalone 2-per-star content. -/
theorem starData_inj {w : Nat} (bs bs' : List (Finset (Fin w)))
    (hwf : ∀ b ∈ bs, Finset.Nonempty b)
    (hwf' : ∀ b ∈ bs', Finset.Nonempty b)
    (heq : starData bs = starData bs') : bs = bs' := by
  have hne : ∀ l ∈ bs.map (Finset.sort (· ≤ ·)), l ≠ [] := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨b, hb, hlb⟩
    rw [← hlb]
    intro hnil
    rcases hwf b hb with ⟨x, hx⟩
    have hpos : 0 < b.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hcard : (Finset.sort (· ≤ ·) b).length = b.card :=
      Finset.length_sort _
    rw [hnil] at hcard
    simp at hcard
    omega
  have hne' : ∀ l ∈ bs'.map (Finset.sort (· ≤ ·)), l ≠ [] := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨b, hb, hlb⟩
    rw [← hlb]
    intro hnil
    rcases hwf' b hb with ⟨x, hx⟩
    have hpos : 0 < b.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hcard : (Finset.sort (· ≤ ·) b).length = b.card :=
      Finset.length_sort _
    rw [hnil] at hcard
    simp at hcard
    omega
  have hs : bs.map (Finset.sort (· ≤ ·)) =
      bs'.map (Finset.sort (· ≤ ·)) := by
    have h1 := unstar_starDataL (bs.map (Finset.sort (· ≤ ·))) hne
    have h2 := unstar_starDataL (bs'.map (Finset.sort (· ≤ ·))) hne'
    unfold starData at heq
    rw [← h1, ← h2, heq]
  have hts := congrArg (List.map List.toFinset) hs
  rw [List.map_map, List.map_map] at hts
  have hid : ∀ (l : List (Finset (Fin w))),
      l.map (List.toFinset ∘ Finset.sort (· ≤ ·)) = l := by
    intro l
    have : (List.toFinset ∘ Finset.sort (· ≤ ·)) =
        (id : Finset (Fin w) → Finset (Fin w)) := by
      funext b
      exact Finset.sort_toFinset _ _
    rw [this, List.map_id]
  rw [hid bs, hid bs'] at hts
  exact hts

/-! ## Pin 3.3: the standalone code bound -/

/-- A positive total star count yields an inhabitant of the position
namespace. -/
theorem exists_pos_of_codeSize_pos {w : Nat}
    (bs : List (Finset (Fin w))) (hpos : 0 < codeSize bs) :
    Nonempty (Fin w) := by
  unfold codeSize at hpos
  by_contra hempty
  have hall : ∀ x ∈ bs.map Finset.card, x = 0 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨b, _, hbx⟩
    rcases Finset.eq_empty_or_nonempty b with hbe | ⟨y, _⟩
    · rw [← hbx, hbe]
      rfl
    · exact absurd ⟨y⟩ hempty
  have : (bs.map Finset.card).sum = 0 := by
    rw [List.sum_eq_zero hall]
  omega

/-- **Pin 3.3, standalone (UF Lemma 6.1 mirror)**: any family of
well-formed codes with total star count `j` has at most `(2w)^j`
members — one position name and one block bit per star. -/
theorem mcode_family_card_le {w j : Nat}
    (S : Finset (List (Finset (Fin w))))
    (hwf : ∀ bs ∈ S, ∀ b ∈ bs, Finset.Nonempty b)
    (hsz : ∀ bs ∈ S, codeSize bs = j) :
    S.card ≤ (2 * w) ^ j := by
  cases j with
  | zero =>
      have hsub : S ⊆ {[]} := by
        intro bs hbs
        rw [Finset.mem_singleton]
        cases hbse : bs with
        | nil => rfl
        | cons b bs' =>
            exfalso
            have hz := hsz bs hbs
            rw [hbse] at hz
            unfold codeSize at hz
            rw [List.map_cons, List.sum_cons] at hz
            rcases hwf bs hbs b (by rw [hbse]; exact List.mem_cons_self _ _)
              with ⟨x, hx⟩
            have : 0 < b.card := Finset.card_pos.mpr ⟨x, hx⟩
            omega
      calc S.card ≤ ({[]} : Finset (List (Finset (Fin w)))).card :=
            Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
        _ ≤ (2 * w) ^ 0 := by norm_num
  | succ j' =>
      rcases S.eq_empty_or_nonempty with hS | ⟨cs0, hcs0⟩
      · rw [hS]
        simp
      · have hx0 : Nonempty (Fin w) :=
          exists_pos_of_codeSize_pos cs0
            (by rw [hsz cs0 hcs0]; omega)
        rcases hx0 with ⟨x0⟩
        have hmap : ∀ bs ∈ S,
            (fun i : Fin (j' + 1) => (starData bs).getD i (x0, true)) ∈
              (Finset.univ : Finset (Fin (j' + 1) → Fin w × Bool)) := by
          intro bs _
          exact Finset.mem_univ _
        have hinj : Set.InjOn
            (fun bs => fun i : Fin (j' + 1) =>
              (starData bs).getD i (x0, true)) ↑S := by
          intro bs hbs bs' hbs' hfeq
          have hlen : (starData bs).length = j' + 1 := by
            rw [starData_length]
            exact hsz bs hbs
          have hlen' : (starData bs').length = j' + 1 := by
            rw [starData_length]
            exact hsz bs' hbs'
          have hdata : starData bs = starData bs' := by
            apply List.ext_get (by rw [hlen, hlen'])
            intro n h1 h2
            have hn : n < j' + 1 := by omega
            have hraw := congrFun hfeq ⟨n, hn⟩
            have hraw' : (starData bs).getD n (x0, true) =
                (starData bs').getD n (x0, true) := hraw
            rw [getD_eq_get_of_lt _ _ n (by omega),
              getD_eq_get_of_lt _ _ n (by omega)] at hraw'
            exact hraw'
          exact starData_inj bs bs' (hwf bs hbs) (hwf bs' hbs') hdata
        calc S.card ≤
            (Finset.univ : Finset (Fin (j' + 1) → Fin w × Bool)).card :=
              Finset.card_le_card_of_injOn _ hmap hinj
          _ = (2 * w) ^ (j' + 1) := by
              rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
                Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
              ring

/-! ## Pin 3.3 graded / pin 3.4 syntactic: the per-stage product bound -/

/-- **Pin 3.3, graded per-stage bound, in pin 3.4's syntactic
no-support-global form**: any family of (code, answer-stream) pairs —
`s` answer names in the square free-vertex namespace `[2ℓ]` — with total
star count `j` has at most `(2w)^j · (2ℓ)^s` members. Closed arithmetic
in `w`, `ℓ`, `s`, `j` only; the `ℓ`-dependence through the answer
namespace is the disclosed tier-2 content of the located design. -/
theorem mcode_answers_family_card_le {w j ell s : Nat}
    (S : Finset (List (Finset (Fin w)) × (Fin s → Fin (2 * ell))))
    (hwf : ∀ cs ∈ S, ∀ b ∈ cs.1, Finset.Nonempty b)
    (hsz : ∀ cs ∈ S, codeSize cs.1 = j) :
    S.card ≤ (2 * w) ^ j * (2 * ell) ^ s := by
  cases j with
  | zero =>
      have hmap : ∀ cs ∈ S, cs.2 ∈
          (Finset.univ : Finset (Fin s → Fin (2 * ell))) := by
        intro cs _
        exact Finset.mem_univ _
      have hfst : ∀ cs ∈ S, cs.1 = [] := by
        intro cs hcs
        cases hbse : cs.1 with
        | nil => rfl
        | cons b bs' =>
            exfalso
            have hz := hsz cs hcs
            rw [hbse] at hz
            unfold codeSize at hz
            rw [List.map_cons, List.sum_cons] at hz
            rcases hwf cs hcs b (by rw [hbse]; exact List.mem_cons_self _ _)
              with ⟨x, hx⟩
            have : 0 < b.card := Finset.card_pos.mpr ⟨x, hx⟩
            omega
      have hinj : Set.InjOn (fun cs => cs.2)
          (↑S : Set (List (Finset (Fin w)) × (Fin s → Fin (2 * ell)))) := by
        intro cs hcs cs' hcs' heq
        have h1 := hfst cs hcs
        have h2 := hfst cs' hcs'
        cases cs with
        | mk a b =>
            cases cs' with
            | mk a' b' =>
                simp only at h1 h2 heq
                rw [h1, h2, heq]
      calc S.card ≤
          (Finset.univ : Finset (Fin s → Fin (2 * ell))).card :=
            Finset.card_le_card_of_injOn _ hmap hinj
        _ = (2 * ell) ^ s := by
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin]
        _ ≤ (2 * w) ^ 0 * (2 * ell) ^ s := by
            rw [pow_zero, one_mul]
  | succ j' =>
      rcases S.eq_empty_or_nonempty with hS | ⟨cs0, hcs0⟩
      · rw [hS]
        simp
      · have hx0 : Nonempty (Fin w) :=
          exists_pos_of_codeSize_pos cs0.1
            (by rw [hsz cs0 hcs0]; omega)
        rcases hx0 with ⟨x0⟩
        have hmap : ∀ cs ∈ S,
            ((fun i : Fin (j' + 1) => (starData cs.1).getD i (x0, true)),
              cs.2) ∈
              (Finset.univ :
                Finset ((Fin (j' + 1) → Fin w × Bool) ×
                  (Fin s → Fin (2 * ell)))) := by
          intro cs _
          exact Finset.mem_univ _
        have hinj : Set.InjOn
            (fun cs =>
              ((fun i : Fin (j' + 1) => (starData cs.1).getD i (x0, true)),
                cs.2))
            (↑S : Set (List (Finset (Fin w)) ×
              (Fin s → Fin (2 * ell)))) := by
          intro cs hcs cs' hcs' hfeq
          have hfeq1 := congrArg Prod.fst hfeq
          have hfeq2 := congrArg Prod.snd hfeq
          simp only at hfeq1 hfeq2
          have hlen : (starData cs.1).length = j' + 1 := by
            rw [starData_length]
            exact hsz cs hcs
          have hlen' : (starData cs'.1).length = j' + 1 := by
            rw [starData_length]
            exact hsz cs' hcs'
          have hdata : starData cs.1 = starData cs'.1 := by
            apply List.ext_get (by rw [hlen, hlen'])
            intro n h1 h2
            have hn : n < j' + 1 := by omega
            have hraw := congrFun hfeq1 ⟨n, hn⟩
            have hraw' : (starData cs.1).getD n (x0, true) =
                (starData cs'.1).getD n (x0, true) := hraw
            rw [getD_eq_get_of_lt _ _ n (by omega),
              getD_eq_get_of_lt _ _ n (by omega)] at hraw'
            exact hraw'
          have hfsteq : cs.1 = cs'.1 :=
            starData_inj cs.1 cs'.1 (hwf cs hcs) (hwf cs' hcs') hdata
          cases cs with
          | mk a b =>
              cases cs' with
              | mk a' b' =>
                  simp only at hfsteq hfeq2
                  rw [hfsteq, hfeq2]
        calc S.card ≤
            (Finset.univ :
              Finset ((Fin (j' + 1) → Fin w × Bool) ×
                (Fin s → Fin (2 * ell)))).card :=
              Finset.card_le_card_of_injOn _ hmap hinj
          _ = (2 * w) ^ (j' + 1) * (2 * ell) ^ s := by
              simp only [Finset.card_univ, Fintype.card_prod,
                Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
              ring

/-! ## Definitional non-vacuity -/

/-- A concrete round trip on a two-block code over `Fin 2` — the
flattening and its decode, kernel-checked. -/
theorem starData_roundtrip_instance :
    unstar (starDataL ([[0], [0, 1]] : List (List (Fin 2)))) =
      [[0], [0, 1]] := by
  decide

end PHPMatchingCodeBound
end PvNP
