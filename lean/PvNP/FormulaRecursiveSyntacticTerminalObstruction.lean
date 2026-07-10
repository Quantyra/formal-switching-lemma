import PvNP.FormulaRecursiveSyntacticTerminalExact
import PvNP.GeneratedIteratedCollapseFinal

/-!
# Small-arity obstruction for syntactic-terminal packed families

This module records a concrete arity-source obstruction for the current packed
family interface.  The small-arity gated literal/true family has the same
formula-side size/depth/class profile as the S2147 exact-threshold gated family,
but its packed ambient arity is fixed to `1`; consequently it is not ambient
adequate for any rounds schedule.

This is only an arity-source obstruction for the current packaging.  It does not
prove product/counting synthesis, threshold improvement, arbitrary
normalization, arbitrary AC0/bounded-depth collapse, PHP switching, Frege/PHP,
NP/circuit lower bounds, P-vs-NP, full B4, or Gate A work.

INTEGRITY: no `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace PvNP
namespace FormulaRecursiveSyntacticTerminalObstruction

open BoundedDepthFrege
open CNFModel
open FormulaRecursiveNonempty
open FormulaRecursiveSyntacticTerminalClassProfile
open FormulaRecursiveSyntacticTerminalExact
open FormulaRecursiveSyntacticTerminalFamily
open FormulaRecursiveSyntacticTerminalRegime
open FormulaSyntacticSimpleBridge

/-! ## Concrete small-arity gated literal/true packed family -/

/-- Variable `0` as a positive literal over ambient arity `1`. -/
def smallArityGatedLiteralTrueLit0 : BDFormula 1 :=
  BDFormula.lit { var := ⟨0, by decide⟩, sign := true }

/-- The small-arity gated formula: one literal at `0`, and `lit0 OR true` at
every positive depth index. -/
def smallArityGatedLiteralTrueFormula : Nat -> BDFormula 1
  | 0 => smallArityGatedLiteralTrueLit0
  | _ + 1 => BDFormula.or [smallArityGatedLiteralTrueLit0, BDFormula.tru]

/-- The concrete gated literal/true packed family with fixed ambient arity `1`. -/
def smallArityGatedLiteralTruePackedFamily : SyntacticTerminalPackedFamily :=
  fun d => ⟨1, smallArityGatedLiteralTrueFormula d⟩

/-- The small-arity gated family always has arity `1`. -/
theorem smallArityGatedLiteralTruePackedFamily_arity (d : Nat) :
    syntacticTerminalPackedFamilyArity smallArityGatedLiteralTruePackedFamily d = 1 := by
  simp [syntacticTerminalPackedFamilyArity, smallArityGatedLiteralTruePackedFamily]

/-- The small-arity gated family has the same size cap profile as the exact-threshold
gated family. -/
theorem smallArityGatedLiteralTrueSizeCap (d : Nat) :
    syntacticTerminalPackedFamilySizeCap smallArityGatedLiteralTruePackedFamily d =
      gatedLiteralTrueThresholdSizeCapIndex d := by
  cases d <;>
    simp [syntacticTerminalPackedFamilySizeCap, syntacticTerminalPackedFamilyFormula,
      smallArityGatedLiteralTruePackedFamily, smallArityGatedLiteralTrueFormula,
      smallArityGatedLiteralTrueLit0, gatedLiteralTrueThresholdSizeCapIndex,
      PvNP.GeneratedIteratedCollapseFinal.formulaSize_lit,
      PvNP.GeneratedIteratedCollapseFinal.formulaSize_or,
      PvNP.GeneratedIteratedCollapseFinal.formulaSize]

/-- The small-arity gated family has exact size cap `1` at depth index `0`. -/
theorem smallArityGatedLiteralTrueSizeCap_zero :
    syntacticTerminalPackedFamilySizeCap smallArityGatedLiteralTruePackedFamily 0 = 1 := by
  simpa [gatedLiteralTrueThresholdSizeCapIndex] using
    smallArityGatedLiteralTrueSizeCap 0

/-- The small-arity gated family has exact size cap `3` at positive depth indices. -/
theorem smallArityGatedLiteralTrueSizeCap_succ (d : Nat) :
    syntacticTerminalPackedFamilySizeCap smallArityGatedLiteralTruePackedFamily (d + 1) = 3 := by
  simpa [gatedLiteralTrueThresholdSizeCapIndex] using
    smallArityGatedLiteralTrueSizeCap (d + 1)

/-- The small-arity gated family has depth `0` at `0` and `1` at successors. -/
theorem smallArityGatedLiteralTrueDepth (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula smallArityGatedLiteralTruePackedFamily d) =
      if d = 0 then 0 else 1 := by
  cases d <;>
    simp [syntacticTerminalPackedFamilyFormula, smallArityGatedLiteralTruePackedFamily,
      smallArityGatedLiteralTrueFormula, smallArityGatedLiteralTrueLit0, depth]

/-- The small-arity gated family has depth `0` at depth index `0`. -/
theorem smallArityGatedLiteralTrueDepth_zero :
    depth (syntacticTerminalPackedFamilyFormula smallArityGatedLiteralTruePackedFamily 0) = 0 := by
  simpa using smallArityGatedLiteralTrueDepth 0

/-- The small-arity gated family has depth `1` at positive depth indices. -/
theorem smallArityGatedLiteralTrueDepth_succ (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula smallArityGatedLiteralTruePackedFamily (d + 1)) = 1 := by
  simpa using smallArityGatedLiteralTrueDepth (d + 1)

/-- The small-arity gated family lies in the restricted syntactic-terminal class. -/
theorem smallArityGatedLiteralTruePackedFamily_class :
    SyntacticTerminalPackedFamilyClass smallArityGatedLiteralTruePackedFamily := by
  intro d
  cases d with
  | zero =>
      constructor
      · simp [syntacticTerminalPackedFamilyFormula,
          smallArityGatedLiteralTruePackedFamily, smallArityGatedLiteralTrueFormula,
          smallArityGatedLiteralTrueLit0, syntacticFormulaSimpleDNF,
          syntacticOrListSimpleDNF]
      · exact NoEmptyFanins.lit _
  | succ d =>
      constructor
      · simp [syntacticTerminalPackedFamilyFormula,
          smallArityGatedLiteralTruePackedFamily, smallArityGatedLiteralTrueFormula,
          smallArityGatedLiteralTrueLit0, syntacticFormulaSimpleDNF,
          syntacticOrListSimpleDNF]
      · refine NoEmptyFanins.or (by simp) ?_
        intro child hchild
        simp at hchild
        rcases hchild with hchild | hchild
        · subst child
          exact NoEmptyFanins.lit _
        · subst child
          exact NoEmptyFanins.tru

/-- The small-arity gated family satisfies the depth bound at every index. -/
theorem smallArityGatedLiteralTruePackedFamily_depthBound :
    SyntacticTerminalPackedFamilyDepthBound smallArityGatedLiteralTruePackedFamily := by
  intro d
  cases d with
  | zero => simp [smallArityGatedLiteralTrueDepth_zero]
  | succ d => simp [smallArityGatedLiteralTrueDepth_succ]

/-- Size profile agreement with the S2147 exact-threshold gated family. -/
theorem smallArityGatedLiteralTrue_sizeProfile_eq_gatedLiteralTrueThreshold
    (roundsOf : Nat -> Nat) (d : Nat) :
    syntacticTerminalPackedFamilySizeCap smallArityGatedLiteralTruePackedFamily d =
      syntacticTerminalPackedFamilySizeCap (gatedLiteralTrueThresholdPackedFamily roundsOf) d := by
  rw [smallArityGatedLiteralTrueSizeCap, gatedLiteralTrueThresholdSizeCap]

/-- Depth profile agreement with the S2147 exact-threshold gated family. -/
theorem smallArityGatedLiteralTrue_depthProfile_eq_gatedLiteralTrueThreshold
    (roundsOf : Nat -> Nat) (d : Nat) :
    depth (syntacticTerminalPackedFamilyFormula smallArityGatedLiteralTruePackedFamily d) =
      depth (syntacticTerminalPackedFamilyFormula
        (gatedLiteralTrueThresholdPackedFamily roundsOf) d) := by
  rw [smallArityGatedLiteralTrueDepth, gatedLiteralTrueThresholdDepth]

/-! ## Ambient-adequacy obstruction -/

/-- A positive size cap gives a coarse threshold strictly larger than `1`. -/
theorem one_lt_syntacticTerminalClassCoarseEntryThreshold_of_pos
    {M rounds : Nat} (hM : 0 < M) :
    1 < syntacticTerminalClassCoarseEntryThreshold M rounds := by
  unfold syntacticTerminalClassCoarseEntryThreshold
  have h64M : 0 < 64 * M := Nat.mul_pos (by decide) hM
  have hpow : 0 < (64 * M) ^ rounds :=
    (Nat.pow_pos h64M : 0 < (64 * M) ^ rounds)
  have htail : 0 < 64 * M * M := Nat.mul_pos h64M hM
  have hx : 1 <= (64 * M) ^ rounds * (64 * M * M) :=
    Nat.succ_le_of_lt (Nat.mul_pos hpow htail)
  have hle : 2 <= 2 * (64 * M) ^ rounds * (64 * M * M) := by
    calc
      2 = 2 * 1 := by simp
      _ <= 2 * ((64 * M) ^ rounds * (64 * M * M)) :=
        Nat.mul_le_mul_left 2 hx
      _ = 2 * (64 * M) ^ rounds * (64 * M * M) := by
        rw [← Nat.mul_assoc]
  exact Nat.lt_of_lt_of_le (by decide : 1 < 2) hle

/-- The small-arity gated family is not ambient adequate for any rounds schedule. -/
theorem smallArityGatedLiteralTruePackedFamily_not_ambientAdequate
    (roundsOf : Nat -> Nat) :
    ¬ SyntacticTerminalPackedFamilyAmbientAdequate
      smallArityGatedLiteralTruePackedFamily roundsOf := by
  intro hAmbient
  have hle := hAmbient 0
  rw [smallArityGatedLiteralTrueSizeCap_zero,
    smallArityGatedLiteralTruePackedFamily_arity] at hle
  exact Nat.not_lt_of_ge hle
    (one_lt_syntacticTerminalClassCoarseEntryThreshold_of_pos (M := 1)
      (rounds := roundsOf 0) (by decide))

/-- Concrete non-vacuity package: formula-side class/size/depth profile facts do
not source ambient adequacy under the current packed-family interface. -/
theorem exists_gatedLiteralTrueProfile_not_ambientAdequate
    (roundsOf : Nat -> Nat) :
    ∃ F : SyntacticTerminalPackedFamily,
      SyntacticTerminalPackedFamilyClass F ∧
      SyntacticTerminalPackedFamilyDepthBound F ∧
      (∀ d, syntacticTerminalPackedFamilySizeCap F d = gatedLiteralTrueThresholdSizeCapIndex d) ∧
      (∀ d, depth (syntacticTerminalPackedFamilyFormula F d) = if d = 0 then 0 else 1) ∧
      (∀ d, syntacticTerminalPackedFamilyArity F d = 1) ∧
      ¬ SyntacticTerminalPackedFamilyAmbientAdequate F roundsOf := by
  refine ⟨smallArityGatedLiteralTruePackedFamily, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smallArityGatedLiteralTruePackedFamily_class
  · exact smallArityGatedLiteralTruePackedFamily_depthBound
  · intro d
    exact smallArityGatedLiteralTrueSizeCap d
  · intro d
    exact smallArityGatedLiteralTrueDepth d
  · intro d
    exact smallArityGatedLiteralTruePackedFamily_arity d
  · exact smallArityGatedLiteralTruePackedFamily_not_ambientAdequate roundsOf

end FormulaRecursiveSyntacticTerminalObstruction
end PvNP
