/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotient.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace MathlibExt.NumberTheory.PrimeCounting

private noncomputable def harmonicLowerApprox (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ))

private noncomputable def harmonicLowerError (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ) + 1)

private noncomputable def invNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by push_cast; rw [mul_inv]

private def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

private def sixMultipliers : Finset ℕ := {1, 2, 3, 6}

private noncomputable def squarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (Nat.totient r : ℝ)⁻¹

private noncomputable def coprimeSquarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r),
    (Nat.totient r : ℝ)⁻¹

private noncomputable def coprimeSixHarmonic (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r 6), (r : ℝ)⁻¹

private noncomputable def C (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ Nat.Coprime k 6), (k : ℝ)⁻¹

private noncomputable def btHarmonicCombination (z : ℕ) : ℝ :=
  coprimeSixHarmonic z + coprimeSixHarmonic (z / 2) +
    (1 / 2 : ℝ) * coprimeSixHarmonic (z / 3) +
    (1 / 2 : ℝ) * coprimeSixHarmonic (z / 6)

private def btSmallSquarefree (n : ℕ) : Prop :=
  ¬4 ∣ n ∧ ¬9 ∣ n ∧ ¬25 ∣ n ∧ ¬49 ∣ n

private instance (n : ℕ) : Decidable (btSmallSquarefree n) := by
  unfold btSmallSquarefree
  infer_instance

private def btSmallTotient (n : ℕ) : ℕ :=
  match n / 10 with
  | 0 => #[0, 1, 1, 2, 2, 4, 2, 6, 4, 6].getD (n % 10) 0
  | 1 => #[4, 10, 4, 12, 6, 8, 8, 16, 6, 18].getD (n % 10) 0
  | 2 => #[8, 12, 10, 22, 8, 20, 12, 18, 12, 28].getD (n % 10) 0
  | 3 => #[8, 30, 16, 20, 16, 24, 12, 36, 18, 24].getD (n % 10) 0
  | 4 => #[16, 40, 12, 42, 20, 24, 22, 46, 16, 42].getD (n % 10) 0
  | 5 => #[20, 32, 24, 52, 18, 40, 24, 36, 28, 58].getD (n % 10) 0
  | 6 => #[16, 60, 30, 36, 32, 48, 20, 66, 32, 44].getD (n % 10) 0
  | 7 => #[24, 70, 24, 72, 36, 40, 36, 60, 24, 78].getD (n % 10) 0
  | 8 => #[32, 54, 40, 82, 24, 64, 42, 56, 40, 88].getD (n % 10) 0
  | 9 => #[24, 72, 44, 60, 46, 72, 32, 96, 42, 60].getD (n % 10) 0
  | _ => 0

private noncomputable def btSmallSquarefreeTotientSum : ℕ → ℝ
  | 0 => 0
  | n + 1 => btSmallSquarefreeTotientSum n +
      if btSmallSquarefree (n + 1) then (btSmallTotient (n + 1) : ℝ)⁻¹ else 0
end MathlibExt.NumberTheory.PrimeCounting
