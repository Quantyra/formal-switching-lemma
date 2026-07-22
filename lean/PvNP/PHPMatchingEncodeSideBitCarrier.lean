import PvNP.PHPMatchingEncodeAnswerRedesign
import PvNP.PHPMatchingAnswerTransport
import PvNP.PHPMatchingExtensionEncode

/-!
# S2217: side-bit carrier target

This module records the redesigned, ell-independent carrier shape.  It is not
GA-4 injectivity of the bad domain into that carrier, and it proves no
switching lemma, Frege lower bound, P-vs-NP statement, or `v0.11.0` result.
There is no residual-package grinding here.  The `Fin 4` ratio `6/16` is only
a regression pin in the separate ratio interface.  The factor `4` below is
the redesign **target** shape, independent of `ell`.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeSideBitCarrier

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingAnswerTransport

/-- A step answer is definitionally the endpoint opposite the query vertex. -/
theorem stepAnswer_eq {p h : Nat} (st : VStep p h) :
    stepAnswer st = match st.vertex with
      | .inl _ => Sum.inr st.pair.2
      | .inr _ => Sum.inl st.pair.1 := rfl

/-- Every answer-stream vertex is an endpoint of one of the walked pairs. -/
theorem answerStream_mem_pairVertices {p h : Nat}
    (es : List (VEvent p h)) (v : Vertex p h)
    (hv : v ∈ answerStream es) :
    ∃ pair ∈ (eventsSteps es).map VStep.pair,
      v = Sum.inl pair.1 ∨ v = Sum.inr pair.2 := by
  rcases List.mem_map.mp hv with ⟨st, hst, rfl⟩
  refine ⟨st.pair, List.mem_map.mpr ⟨st, hst, rfl⟩, ?_⟩
  rcases st with ⟨vertex, pair⟩
  cases vertex <;> simp [stepAnswer]

/-- One bit records which side supplied the query vertex. -/
def stepSideBit {p h : Nat} (st : VStep p h) : Bool :=
  match st.vertex with
  | .inl _ => true
  | .inr _ => false

/-- Recover the far endpoint from a pair and its query-side bit. -/
def farEndpointFromSide {p h : Nat} (pair : Fin p × Fin h) (side : Bool) :
    Vertex p h :=
  if side then Sum.inr pair.2 else Sum.inl pair.1

theorem farEndpointFromSide_stepSideBit {p h : Nat} (st : VStep p h) :
    farEndpointFromSide st.pair (stepSideBit st) = stepAnswer st := by
  rcases st with ⟨vertex, pair⟩
  cases vertex <;> rfl

/-- Abstract redesigned carrier bound.  The side stream contributes at most
`2^t ≤ 2^(2j) = 4^j`; this theorem does not construct an injection from the
bad domain into the carrier. -/
theorem mcode_sidebit_grade_card_le
    {h w j t ell : Nat} (htj : t ≤ 2 * j)
    (S : Finset (MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool)))
    (hG1 : ∀ p ∈ S, p.1 ∈ honestMatchingSpace h h (ell - j))
    (hG2wf : ∀ p ∈ S, ∀ b ∈ p.2.1, Finset.Nonempty b)
    (hG2sz : ∀ p ∈ S, codeSize p.2.1 = j)
    (_hinj : Set.InjOn
      (fun p : MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool) => p)
      (↑S : Set (MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool)))) :
    S.card ≤ (honestMatchingSpace h h (ell - j)).card *
      (2 * w) ^ j * 4 ^ j := by
  let codes : Finset (List (Finset (Fin w))) := S.image (fun p => p.2.1)
  let bits : Finset (Fin t → Bool) := Finset.univ
  let target := (honestMatchingSpace h h (ell - j)).product
    (codes.product bits)
  have hsub : S ⊆ target := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨hG1 p hp, Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_univ _⟩⟩
  have hcodes : codes.card ≤ (2 * w) ^ j := by
    apply mcode_family_card_le
    · intro bs hbs b hb
      rcases Finset.mem_image.mp hbs with ⟨p, hp, rfl⟩
      exact hG2wf p hp b hb
    · intro bs hbs
      rcases Finset.mem_image.mp hbs with ⟨p, hp, rfl⟩
      exact hG2sz p hp
  have hbits : bits.card ≤ 4 ^ j := by
    rw [show bits.card = 2 ^ t by
      simp [bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]]
    calc
      2 ^ t ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by omega) htj
      _ = 4 ^ j := by rw [pow_mul]; norm_num
  have hcodesbits : (codes.product bits).card ≤ (2 * w) ^ j * 4 ^ j := by
    calc
      (codes.product bits).card = codes.card * bits.card :=
        Finset.card_product _ _
      _ ≤ (2 * w) ^ j * 4 ^ j := Nat.mul_le_mul hcodes hbits
  calc
    S.card ≤ target.card := Finset.card_le_card hsub
    _ = (honestMatchingSpace h h (ell - j)).card *
        (codes.product bits).card := Finset.card_product _ _
    _ ≤ (honestMatchingSpace h h (ell - j)).card *
        ((2 * w) ^ j * 4 ^ j) := Nat.mul_le_mul_left _ hcodesbits
    _ = (honestMatchingSpace h h (ell - j)).card *
        (2 * w) ^ j * 4 ^ j := by simp [Nat.mul_assoc]

/-- S2217 summary: endpoint recovery plus the abstract `C = 4` target bound.
The fixed `Fin 4` ratio is deliberately not a consequence of this theorem. -/
theorem sidebit_carrier_s2217_summary :
    (∀ {p h : Nat} (st : VStep p h),
      farEndpointFromSide st.pair (stepSideBit st) = stepAnswer st) ∧
    (∀ {h w j t ell : Nat} (htj : t ≤ 2 * j)
      (S : Finset (MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool)))
      (hG1 : ∀ p ∈ S, p.1 ∈ honestMatchingSpace h h (ell - j))
      (hG2wf : ∀ p ∈ S, ∀ b ∈ p.2.1, Finset.Nonempty b)
      (hG2sz : ∀ p ∈ S, codeSize p.2.1 = j)
      (hinj : Set.InjOn
        (fun p : MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool) => p)
        (↑S : Set (MatchingMap h h × List (Finset (Fin w)) × (Fin t → Bool)))),
      S.card ≤ (honestMatchingSpace h h (ell - j)).card *
        (2 * w) ^ j * 4 ^ j) :=
  ⟨farEndpointFromSide_stepSideBit, mcode_sidebit_grade_card_le⟩

end PHPMatchingEncodeSideBitCarrier
end PvNP
