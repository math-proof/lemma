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

noncomputable def harmonicLowerApprox (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ))

noncomputable def harmonicLowerError (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ) + 1)

noncomputable def invNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by push_cast; rw [mul_inv]

def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

def sixMultipliers : Finset ℕ := {1, 2, 3, 6}

noncomputable def squarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (Nat.totient r : ℝ)⁻¹

noncomputable def coprimeSquarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r),
    (Nat.totient r : ℝ)⁻¹

noncomputable def coprimeSixHarmonic (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r 6), (r : ℝ)⁻¹

noncomputable def C (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ Nat.Coprime k 6), (k : ℝ)⁻¹

noncomputable def btHarmonicCombination (z : ℕ) : ℝ :=
  coprimeSixHarmonic z + coprimeSixHarmonic (z / 2) +
    (1 / 2 : ℝ) * coprimeSixHarmonic (z / 3) +
    (1 / 2 : ℝ) * coprimeSixHarmonic (z / 6)

def btSmallSquarefree (n : ℕ) : Prop :=
  ¬4 ∣ n ∧ ¬9 ∣ n ∧ ¬25 ∣ n ∧ ¬49 ∣ n

end MathlibExt.NumberTheory.PrimeCounting
