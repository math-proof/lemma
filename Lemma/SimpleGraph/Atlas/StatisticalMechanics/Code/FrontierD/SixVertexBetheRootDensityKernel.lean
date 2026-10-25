import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityKernel.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexRootDensityScale_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityScale_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexRootDensityScale c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityScale_pos hc

/--
[sixVertexRootDensityWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_pos_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexRootDensityWeight c x := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_pos hc x

/--
[sixVertexRootDensityKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_pos_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexRootDensityKernel c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_pos hc x y

/--
[sixVertexRootDensityKernelFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityKernelFloor_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexRootDensityKernelFloor c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernelFloor_pos hc

/--
[sixVertexBetheIntegratingFactor_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexBetheIntegratingFactor_bounds_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexAnisotropyMagnitude c - 1 ≤ sixVertexBetheIntegratingFactor c x ∧ sixVertexBetheIntegratingFactor c x ≤ sixVertexAnisotropyMagnitude c + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheIntegratingFactor_bounds hc x

/--
[sixVertexThetaDerivativeDenominator_uniform_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_uniform_upper_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexThetaDerivativeDenominator c x y ≤ 4 * (sixVertexAnisotropyMagnitude c + 1) ^ 2 + 4 := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_uniform_upper hc x y

/--
[sixVertexRootDensityKernelFloor_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityKernelFloor_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityKernelFloor c ≤ sixVertexRootDensityKernel c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernelFloor_le hc x y

/--
[sixVertexRootDensityKernel_div_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_div_weight_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y = -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_div_weight hc x y

/--
[sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityKernel c x y = -sixVertexRootDensityWeight c x * (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c x y) := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative hc x y

/--
[intervalIntegral_sixVertexRootDensityKernel_div_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexRootDensityKernel_div_weight_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y = 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexRootDensityKernel_div_weight hc x

/--
[sixVertexRootDensityContractionRate_mem_Ico](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityContractionRate_mem_Ico_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityContractionRate c ∈ Set.Ico 0 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityContractionRate_mem_Ico hc

/--
[sixVertexRootDensity_reciprocalWeight_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensity_reciprocalWeight_lower_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityScale c / (sixVertexAnisotropyMagnitude c + 1) ≤ 1 / sixVertexRootDensityWeight c y := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensity_reciprocalWeight_lower hc y

/--
[intervalIntegral_one_div_sixVertexRootDensityWeight_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma intervalIntegral_one_div_sixVertexRootDensityWeight_lower_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  2 * Real.pi * (sixVertexRootDensityScale c / (sixVertexAnisotropyMagnitude c + 1)) ≤ ∫ y in -Real.pi..Real.pi, 1 / sixVertexRootDensityWeight c y := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_one_div_sixVertexRootDensityWeight_lower hc

/--
[sixVertexRootDensityKernel_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_contraction_eq
  {c : Real}
  {e : Real → Real}
  {E : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (he : Continuous e)
  (hE : 0 ≤ E)
  (hmass : (∫ y in -Real.pi..Real.pi, e y / sixVertexRootDensityWeight c y) = 0)
  (hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E) :
-- imply
  |(1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, (sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y) * e y| ≤ sixVertexRootDensityContractionRate c * E := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_contraction hc he hE hmass hbound x


-- created on 2026-10-23
