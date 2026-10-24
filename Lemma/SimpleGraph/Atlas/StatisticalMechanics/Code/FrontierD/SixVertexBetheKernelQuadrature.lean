import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature
open StatMech StatMech.FrontierD


/--
[sixVertexRootDensityWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_le_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityWeight c y <= (sixVertexAnisotropyMagnitude c + 1) / sixVertexRootDensityScale c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_le hc y

/--
[sixVertexRootDensityWeight_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_lipschitz_eq
  {c : Real}
  {y z : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityWeight c y - sixVertexRootDensityWeight c z| <= (1 / sixVertexRootDensityScale c) * |y - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_lipschitz hc y z

/--
[sixVertexRootDensityKernel_div_weight_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_div_weight_lipschitz_eq
  {c : Real}
  {x y z : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y - sixVertexRootDensityKernel c x z / sixVertexRootDensityWeight c z| <= sixVertexThetaLeftKernelLipschitzBound c * |y - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_div_weight_lipschitz hc x y z

/--
[abs_sixVertexRootDensityKernel_div_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma abs_sixVertexRootDensityKernel_div_weight_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y| <= sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRootDensityKernel_div_weight_le hc x y

/--
[abs_kernel_mul_finiteDensity_cellMass_sub_integral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma abs_kernel_mul_finiteDensity_cellMass_sub_integral_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x a b u mass : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n <= N)
  (hab : a <= b)
  (hu : u ∈ Set.Icc a b)
  (hmass : ∫ y in a..b, sixVertexFiniteRootDensity c N n p y = mass) :
-- imply
  |sixVertexRootDensityKernel c x u * mass - ∫ y in a..b, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N n p y| <= sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * (b - a) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_kernel_mul_finiteDensity_cellMass_sub_integral_le hc hN hn p x a b u mass hab hu hmass

/--
[abs_kernel_div_width_sub_finiteDensity_cellIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma abs_kernel_div_width_sub_finiteDensity_cellIntegral_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {x : Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n + 1 <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |sixVertexRootDensityKernel c x (p j.castSucc) / N - ∫ y in p j.castSucc..p j.succ, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y| <= sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * (p j.succ - p j.castSucc) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_kernel_div_width_sub_finiteDensity_cellIntegral_le hc hN hn hopen hsol x j

/--
[abs_kernel_div_width_sub_finiteDensity_rightCellIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma abs_kernel_div_width_sub_finiteDensity_rightCellIntegral_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {x : Real}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n + 1 <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |sixVertexRootDensityKernel c x (p j.succ) / N - ∫ y in p j.castSucc..p j.succ, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y| <= sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * (p j.succ - p j.castSucc) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_kernel_div_width_sub_finiteDensity_rightCellIntegral_le hc hN hn hopen hsol x j

/--
[abs_kernel_div_width_sub_finiteDensity_boundaryIntegral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheKernelQuadrature.lean)
-/
@[path]
private lemma abs_kernel_div_width_sub_finiteDensity_boundaryIntegral_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |sixVertexRootDensityKernel c x (p 0) / N - ∫ y in p (Fin.last n) - 2 * Real.pi..p 0, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y| <= sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * (p 0 - (p (Fin.last n) - 2 * Real.pi)) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_kernel_div_width_sub_finiteDensity_boundaryIntegral_le hc hN hhalf hopen hsol x


-- created on 2026-10-23
