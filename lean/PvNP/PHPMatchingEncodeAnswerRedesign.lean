import PvNP.PHPMatchingEncodeConditionalFiber
import PvNP.PHPMatchingAnswerTransport

/-!
# S2211: answer-code redesign decision and first formal probe

**REDESIGN, not pivot.**  The next encode replaces
`G3 : Fin t → Fin (2 * ell)` with an `ell`-independent alphabet.  The path-code
pivot is rejected because its ratio worsens with `t`.  The current `G3`/mcode
package remains a stop-loss until the redesign lands.

This module records two positive pieces of reusable infrastructure: the
uniform relation between answer length `t` and star grade `j`, and the pure
honest-times-mcode cardinal bound that has no `(2 * ell) ^ t` factor.

Non-claims: this is not general GA-4, does not prove G3 elimination, and is not
v0.11.0.  The package stop-loss stands.  The Fin4 cardinality-6 result remains
an oracle only.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace PHPMatchingEncodeAnswerRedesign

open Classical
open PHPMatchingComposition
open PHPMatchingCanonicalMDT
open PHPMatchingVertexTree
open PHPMatchingExtensionEncode
open PHPMatchingCodeBound
open PHPMatchingAnswerTransport
open PHPMatchingDeterministicEncode
open PHPMatchingEncodeInjectivity

/-- Vertices appearing as endpoints of sigma-pairs in a walk. -/
def sigmaJoinVertices {p h : Nat} (blocks : List (VBlock p h)) :
    List (Vertex p h) :=
  (blockSigmas blocks).join.bind fun e => [Sum.inl e.1, Sum.inr e.2]

/-- S2211 re-export: trace answers remain in the base free-vertex namespace. -/
theorem answerStream_mem_freeVertices_s2211 {p h : Nat} (fuel : Nat)
    (mu : MatchingMap p h) (pending : List (Vertex p h)) (D : MDNF p h)
    (feed : List (Vertex p h)) (v : Vertex p h)
    (hv : v ∈ answerStream (vevents fuel mu pending D feed)) :
    v ∈ freeVertices mu :=
  answerStream_mem_freeVertices fuel mu pending D feed v hv

/-- On the deep deterministic encode path, the feed is exactly the trace's
answer stream. -/
theorem deepFeed_eq_answerStream {p h t : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h) (hrho : IsMatching rho)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho)) :
    leftmostLiveDeepFeed rho D t =
      answerStream (vtrace rho D (leftmostLiveDeepFeed rho D t)) :=
  leftmostLiveDeepFeed_eq_answerStream hsq rho D hrho ht

/-- On every deterministic encode image, the star grade is at most the answer
length, and every star accounts for at most two answer steps. -/
theorem encodeMatch_j_le_t {p h w t ell : Nat} (hsq : p = h)
    (rho : MatchingMap p h) (D : MDNF p h)
    (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
    (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
    (hw : ∀ term ∈ D, term.length ≤ w) :
    let code := encodeMatch hsq rho D hrho hell ht hw
    code.j ≤ t ∧ t ≤ 2 * code.j := by
  intro code
  have hbeta := traceBetaDeep_wellFormed_codeSize
    (w := w) rho D hrho ht hw
  have hsteps := leftmostLiveDeepFeed_vtrace_eventsSteps_length
    hsq rho D hrho ht
  have hdrop := vtrace_drop_range (freePigeons rho).card rho D
    (leftmostLiveDeepFeed rho D t)
  have hdropv :
      ((blockSigmas (blocksOf
        (vtrace rho D (leftmostLiveDeepFeed rho D t)))).join).length ≤
          (eventsSteps
            (vtrace rho D (leftmostLiveDeepFeed rho D t))).length ∧
        (eventsSteps
          (vtrace rho D (leftmostLiveDeepFeed rho D t))).length ≤
          2 * ((blockSigmas (blocksOf
            (vtrace rho D (leftmostLiveDeepFeed rho D t)))).join).length := by
    simpa [vtrace] using hdrop
  have hdrop' :
      ((blockSigmas (blocksOf
        (vtrace rho D (leftmostLiveDeepFeed rho D t)))).join).length ≤ t ∧
        t ≤ 2 * ((blockSigmas (blocksOf
          (vtrace rho D (leftmostLiveDeepFeed rho D t)))).join).length := by
    rw [hsteps] at hdropv
    exact hdropv
  have hj : code.j =
      ((blockSigmas (blocksOf
        (vtrace rho D (leftmostLiveDeepFeed rho D t)))).join).length := by
    simpa [code, encodeMatch] using hbeta.2
  simpa [hj] using hdrop'

/-- Counting carrier without ell-dependent G3: a grade contained in honest
matchings times well-formed mcode has size at most
`|honest (ell-j)| * (2w)^j`.  This is the target shape after G3 elimination;
the hypotheses are not established for the general bad domain here. -/
theorem mcode_only_grade_card_le_of_g1g2_inj
    {h w j ell : Nat}
    (S : Finset (MatchingMap h h × List (Finset (Fin w))))
    (hG1 : ∀ p ∈ S, p.1 ∈ honestMatchingSpace h h (ell - j))
    (hG2wf : ∀ p ∈ S, ∀ b ∈ p.2, Finset.Nonempty b)
    (hG2sz : ∀ p ∈ S, codeSize p.2 = j)
    (_hinj : Set.InjOn
      (fun p : MatchingMap h h × List (Finset (Fin w)) => p)
      (↑S : Set (MatchingMap h h × List (Finset (Fin w))))) :
    S.card ≤ (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j := by
  let codes : Finset (List (Finset (Fin w))) := S.image Prod.snd
  let target := (honestMatchingSpace h h (ell - j)).product codes
  have hsub : S ⊆ target := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨hG1 p hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hcodes : codes.card ≤ (2 * w) ^ j := by
    apply mcode_family_card_le
    · intro bs hbs b hb
      rcases Finset.mem_image.mp hbs with ⟨p, hp, rfl⟩
      exact hG2wf p hp b hb
    · intro bs hbs
      rcases Finset.mem_image.mp hbs with ⟨p, hp, rfl⟩
      exact hG2sz p hp
  calc
    S.card ≤ target.card := Finset.card_le_card hsub
    _ = (honestMatchingSpace h h (ell - j)).card * codes.card :=
      Finset.card_product _ _
    _ ≤ (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j :=
      Nat.mul_le_mul_left _ hcodes

/-- S2211 summary pin: the uniform grade range and G3-free counting carrier. -/
theorem answer_redesign_s2211_summary :
    (∀ {p h w t ell : Nat} (hsq : p = h)
      (rho : MatchingMap p h) (D : MDNF p h)
      (hrho : IsMatching rho) (hell : (freePigeons rho).card = ell)
      (ht : t ≤ vmdtDepth (canonicalVMDT D rho))
      (hw : ∀ term ∈ D, term.length ≤ w),
      let code := encodeMatch hsq rho D hrho hell ht hw
      code.j ≤ t ∧ t ≤ 2 * code.j) ∧
    (∀ {h w j ell : Nat}
      (S : Finset (MatchingMap h h × List (Finset (Fin w))))
      (hG1 : ∀ p ∈ S, p.1 ∈ honestMatchingSpace h h (ell - j))
      (hG2wf : ∀ p ∈ S, ∀ b ∈ p.2, Finset.Nonempty b)
      (hG2sz : ∀ p ∈ S, codeSize p.2 = j)
      (hinj : Set.InjOn
        (fun p : MatchingMap h h × List (Finset (Fin w)) => p)
        (↑S : Set (MatchingMap h h × List (Finset (Fin w))))),
      S.card ≤ (honestMatchingSpace h h (ell - j)).card * (2 * w) ^ j) :=
  ⟨fun hsq rho D hrho hell ht hw =>
      encodeMatch_j_le_t hsq rho D hrho hell ht hw,
    mcode_only_grade_card_le_of_g1g2_inj⟩

end PHPMatchingEncodeAnswerRedesign
end PvNP
