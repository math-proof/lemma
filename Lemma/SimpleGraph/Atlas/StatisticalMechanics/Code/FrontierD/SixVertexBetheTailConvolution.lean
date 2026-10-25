import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailConvolution.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexBetheIntegratingFactor_add_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sixVertexBetheIntegratingFactor_add_two_pi_eq
  {c x : Real} :
-- imply
  sixVertexBetheIntegratingFactor c (x + 2 * Real.pi) = sixVertexBetheIntegratingFactor c x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheIntegratingFactor_add_two_pi c x

/--
[sixVertexThetaDerivativeDenominator_add_two_pi_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_add_two_pi_left_eq
  {c x y : Real} :
-- imply
  sixVertexThetaDerivativeDenominator c (x + 2 * Real.pi) y = sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_add_two_pi_left c x y

/--
[sixVertexThetaDerivativeDenominator_add_two_pi_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_add_two_pi_right_eq
  {c x y : Real} :
-- imply
  sixVertexThetaDerivativeDenominator c x (y + 2 * Real.pi) = sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_add_two_pi_right c x y

/--
[sixVertexRootDensityKernel_add_two_pi_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_add_two_pi_left_eq
  {c x y : Real} :
-- imply
  sixVertexRootDensityKernel c (x + 2 * Real.pi) y = sixVertexRootDensityKernel c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_add_two_pi_left c x y

/--
[sixVertexRootDensityKernel_add_two_pi_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_add_two_pi_right_eq
  {c x y : Real} :
-- imply
  sixVertexRootDensityKernel c x (y + 2 * Real.pi) = sixVertexRootDensityKernel c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_add_two_pi_right c x y

/--
[periodic_sixVertexRootDensityKernel_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma periodic_sixVertexRootDensityKernel_right_eq
  {c x : Real} :
-- imply
  Function.Periodic (sixVertexRootDensityKernel c x) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.periodic_sixVertexRootDensityKernel_right c x

/--
[sixVertexFiniteRootDensity_add_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sixVertexFiniteRootDensity_add_two_pi_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {x : Real} :
-- imply
  sixVertexFiniteRootDensity c N n p (x + 2 * Real.pi) = sixVertexFiniteRootDensity c N n p x := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteRootDensity_add_two_pi c N n p x

/--
[periodic_sixVertexFiniteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma periodic_sixVertexFiniteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real} :
-- imply
  Function.Periodic (sixVertexFiniteRootDensity c N n p) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.periodic_sixVertexFiniteRootDensity c N n p

/--
[lipschitzWith_sixVertexRootDensityKernel_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexRootDensityKernel_right_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexRootDensityKernelLipschitzNNReal c) (sixVertexRootDensityKernel c x) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexRootDensityKernel_right hc x

/--
[sum_cyclicRootPartition_eq_sum_roots_of_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma sum_cyclicRootPartition_eq_sum_roots_of_periodic_eq
  {n : Nat}
  {p : Fin (n + 1) → Real}
  {f : Real → Real}
-- given
  (hf : Function.Periodic f (2 * Real.pi)) :
-- imply
  ∑ k ∈ Finset.range (n + 1), f (sixVertexCyclicRootPartition p k) = ∑ j, f (p j) := by
-- proof
  apply StatMech.FrontierD.sum_cyclicRootPartition_eq_sum_roots_of_periodic p hf

/--
[intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {x : Real} :
-- imply
  ∫ y in sixVertexCyclicRootPartition p 0.. sixVertexCyclicRootPartition p (n + 1), sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y = ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_cyclic_kernel_mul_finiteDensity_eq_fullCircle c p x

/--
[intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle_eq
  {c : Real}
  {N n : Nat}
  {f : Real -> Real}
-- given
  (p : Fin (n + 1) -> Real)
  (hf : Function.Periodic f (2 * Real.pi)) :
-- imply
  ∫ y in sixVertexCyclicRootPartition p 0.. sixVertexCyclicRootPartition p (n + 1), f y * sixVertexFiniteRootDensity c N (n + 1) p y = ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c N (n + 1) p y := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_cyclic_mul_finiteDensity_eq_fullCircle c p hf

/--
[abs_empiricalKernel_sub_finiteDensityIntegral_le_of_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma abs_empiricalKernel_sub_finiteDensityIntegral_le_of_mesh_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {mesh : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : n + 1 ≤ N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hmesh : ∀ k < n + 1, sixVertexCyclicRootPartition p (k + 1) - sixVertexCyclicRootPartition p k ≤ mesh) :
-- imply
  |(∑ j, sixVertexRootDensityKernel c x (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y| ≤ sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * mesh * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalKernel_sub_finiteDensityIntegral_le_of_mesh hc hN hcount hhalf hopen hsol hmesh x

/--
[abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) -> Real}
  {f : Real -> Real}
  {C : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi)) :
-- imply
  |(∑ j, f (p j)) / N - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c N (n + 1) p y| <= (C : Real) * sixVertexFiniteRootDensityUniformBound c * (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_le_tail hc htail hN hhalf hopen hsol hf hlip hperiodic

/--
[abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_pos_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_pos_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {f : Real -> Real}
  {C : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hn : 0 < n)
  (hhalf : N = 2 * n)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi)) :
-- imply
  |(∑ j, f (p j)) / N - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c N n p y| <= (C : Real) * sixVertexFiniteRootDensityUniformBound c * (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_pos_le_tail hc htail hN hn hhalf hopen hsol hf hlip hperiodic

/--
[abs_empiricalKernel_sub_finiteDensityIntegral_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean)
-/
@[path]
private lemma abs_empiricalKernel_sub_finiteDensityIntegral_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  |(∑ j, sixVertexRootDensityKernel c x (p j)) / N - ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y| <= sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_empiricalKernel_sub_finiteDensityIntegral_le_tail hc htail hN hhalf hopen hsol x


-- created on 2026-10-23
