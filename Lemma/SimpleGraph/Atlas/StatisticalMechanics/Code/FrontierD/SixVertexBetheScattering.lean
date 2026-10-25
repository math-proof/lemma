import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
open Finset StatMech StatMech.FrontierD


/--
[sixVertexScatteringDenominator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean)
-/
@[path]
private lemma sixVertexScatteringDenominator_eq_eq
  {c x y : ℝ} :
-- imply
  sixVertexScatteringDenominator c x y = (sixVertexThetaDenominator c x y : ℂ) + (Real.sin x - Real.sin y : ℝ) * Complex.I := by
-- proof
  apply StatMech.FrontierD.sixVertexScatteringDenominator_eq c x y

/--
[sixVertexScatteringDenominator_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean)
-/
@[path]
private lemma sixVertexScatteringDenominator_ne_zero_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexScatteringDenominator c x y ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexScatteringDenominator_ne_zero hc x y

/--
[sixVertexTheta_exp_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean)
-/
@[path]
private lemma sixVertexTheta_exp_identity_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Complex.exp (-Complex.I * sixVertexTheta c x y) = Complex.exp (Complex.I * (x - y)) * star (sixVertexScatteringDenominator c x y) / sixVertexScatteringDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_exp_identity hc x y

/--
[exp_two_pi_mul_centralQuantumNumber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean)
-/
@[path]
private lemma exp_two_pi_mul_centralQuantumNumber_eq
  {n : ℕ}
  {j : Fin n} :
-- imply
  Complex.exp (Complex.I * (2 * Real.pi * sixVertexCentralQuantumNumber j)) = (-1 : ℂ) ^ (n - 1) := by
-- proof
  apply StatMech.FrontierD.exp_two_pi_mul_centralQuantumNumber j

/--
[SixVertexSatisfiesBetheEquations.multiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean)
-/
@[path]
private lemma multiplicative_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexSatisfiesBetheEquations c N n p) :
-- imply
  SixVertexSatisfiesMultiplicativeBetheEquations c N n p := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesBetheEquations.multiplicative hp

/--
[exp_neg_I_sum_sixVertexTheta_eq_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean)
-/
@[path]
private lemma exp_neg_I_sum_sixVertexTheta_eq_product_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin n → ℝ}
  {j : Fin n}
-- given
  (hc : 2 < c) :
-- imply
  Complex.exp (-Complex.I * ∑ k, sixVertexTheta c (p j) (p k)) = ∏ k, Complex.exp (Complex.I * (p j - p k)) * star (sixVertexScatteringDenominator c (p j) (p k)) / sixVertexScatteringDenominator c (p j) (p k) := by
-- proof
  apply StatMech.FrontierD.exp_neg_I_sum_sixVertexTheta_eq_product hc p j


-- created on 2026-10-23
