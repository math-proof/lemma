import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
open StatMech StatMech.FrontierA


/--
[quantumIsingTrotterReducedParameter_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductReduction.lean)
-/
@[path]
private lemma quantumIsingTrotterReducedParameter_one_le_eq
  {n : Nat}
  {k : Real}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hn : 0 < n)
  (hx1 : beta * h / (2 * n) < 1) :
-- imply
  1 ≤ quantumIsingTrotterReducedParameter beta h n k := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterReducedParameter_one_le beta h n k hbeta hh hn hx1

/--
[quantumIsingTrotterReducedParameter_one_lt_of_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductReduction.lean)
-/
@[path]
private lemma quantumIsingTrotterReducedParameter_one_lt_of_cos_eq
  {n : Nat}
  {k : Real}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hn : 0 < n)
  (hx1 : beta * h / (2 * n) < 1)
  (hk : -1 < Real.cos k) :
-- imply
  1 < quantumIsingTrotterReducedParameter beta h n k := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterReducedParameter_one_lt_of_cos beta h n k hbeta hh hn hx1 hk

/--
[cos_quantumIsingShiftedAntiperiodicAngle_gt_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductReduction.lean)
-/
@[path]
private lemma cos_quantumIsingShiftedAntiperiodicAngle_gt_neg_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {i : Nat}
-- given
  (hi : i < L) :
-- imply
  -1 < Real.cos (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi) := by
-- proof
  apply StatMech.FrontierA.cos_quantumIsingShiftedAntiperiodicAngle_gt_neg_one L i hi

/--
[quantumIsingNormalizedSpinSector_eleven_sq_eq_spectralRootProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductReduction.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_eleven_sq_eq_spectralRootProduct_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingNormalizedSpinSector beta h L 1 1 ^ 2 = ∏ i ∈ Finset.range L, ((((1 - (beta * h / (2 * L)) ^ 2) * quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi))) ^ L * (1 + (quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)))⁻¹ ^ L) ^ 2 : Real) : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_eleven_sq_eq_spectralRootProduct beta h L hbeta hh hx1

/--
[two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductReduction.lean)
-/
@[path]
private lemma two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L 1 1‖ = ∑ i ∈ Finset.range L, ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) + (L : Real) * Real.arcosh (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)) + 2 * Real.log (1 + (quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (1 : Real) / 2) / L - Real.pi)))⁻¹ ^ L)) := by
-- proof
  apply StatMech.FrontierA.two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven beta h L hbeta hh hx1


-- created on 2026-10-23
