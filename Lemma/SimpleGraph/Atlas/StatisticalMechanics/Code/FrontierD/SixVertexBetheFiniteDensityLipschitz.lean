import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz
open StatMech StatMech.FrontierD


/--
[sixVertexThetaLeftKernelLipschitzBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexThetaLeftKernelLipschitzBound_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexThetaLeftKernelLipschitzBound c := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaLeftKernelLipschitzBound_pos hc

/--
[sixVertexThetaDerivativeDenominator_uniform_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_uniform_lower_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  4 * (sixVertexAnisotropyMagnitude c - 1) ^ 2 <= sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_uniform_lower hc x y

/--
[sixVertexThetaDerivativeDenominator_lipschitz_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_lipschitz_left_eq
  {c : Real}
  {x z y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexThetaDerivativeDenominator c x y - sixVertexThetaDerivativeDenominator c z y| <= (4 * (sixVertexAnisotropyMagnitude c + 1) + 2) * |x - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_lipschitz_left hc x z y

/--
[sixVertexThetaLeftKernel_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma sixVertexThetaLeftKernel_lipschitz_eq
  {c : Real}
  {x z y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c x y - 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c z y| <= sixVertexThetaLeftKernelLipschitzBound c * |x - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaLeftKernel_lipschitz hc x z y

/--
[lipschitzWith_sixVertexFiniteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexFiniteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n <= N) :
-- imply
  LipschitzWith (sixVertexFiniteRootDensityLipschitzConstant c) (sixVertexFiniteRootDensity c N n p) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexFiniteRootDensity hc hN hn p

/--
[abs_sixVertexFiniteRootDensity_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma abs_sixVertexFiniteRootDensity_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n <= N) :
-- imply
  |sixVertexFiniteRootDensity c N n p x| <= sixVertexFiniteRootDensityUniformBound c := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexFiniteRootDensity_le hc hN hn p x

/--
[abs_gap_mul_finiteRootDensity_sub_inv_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma abs_gap_mul_finiteRootDensity_sub_inv_width_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n + 1 <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |(p j.succ - p j.castSucc) * sixVertexFiniteRootDensity c N (n + 1) p (p j.castSucc) - 1 / N| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (p j.succ - p j.castSucc) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_gap_mul_finiteRootDensity_sub_inv_width_le hc hN hn hopen hsol j

/--
[abs_gap_mul_finiteRootDensity_right_sub_inv_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma abs_gap_mul_finiteRootDensity_right_sub_inv_width_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n + 1 <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |(p j.succ - p j.castSucc) * sixVertexFiniteRootDensity c N (n + 1) p (p j.succ) - 1 / N| <= 2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (p j.succ - p j.castSucc) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_gap_mul_finiteRootDensity_right_sub_inv_width_le hc hN hn hopen hsol j

/--
[intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {a b : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N) :
-- imply
  ∫ x in a..b, sixVertexFiniteRootDensity c N n p x = sixVertexBetheCountingFunction c N n p b - sixVertexBetheCountingFunction c N n p a := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub hc hN p a b

/--
[intervalIntegral_sixVertexFiniteRootDensity_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_boundary_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  ∫ x in p (Fin.last n) - 2 * Real.pi..p 0, sixVertexFiniteRootDensity c N (n + 1) p x = ((N : Real) - 2 * (n + 1 : Real) + 1) / N := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity_boundary hc hN hsol


-- created on 2026-10-23
