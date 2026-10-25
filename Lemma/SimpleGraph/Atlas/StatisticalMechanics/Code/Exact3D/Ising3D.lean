import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
open MeasureTheory StatMech StatMech.Exact3D


/--
[ising3DOrigin_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DOrigin_mem_box_eq
  {n : ℕ} :
-- imply
  ising3DOrigin ∈ box 3 n := by
-- proof
  apply StatMech.Exact3D.ising3DOrigin_mem_box n

/--
[ising3DXAxisRay_mem_box_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DXAxisRay_mem_box_self_eq
  {n : ℕ} :
-- imply
  ising3DXAxisRay n ∈ box 3 n := by
-- proof
  apply StatMech.Exact3D.ising3DXAxisRay_mem_box_self n

/--
[ising3DXAxisRay_mem_box_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DXAxisRay_mem_box_le_eq
  {n N : ℕ}
-- given
  (h : n ≤ N) :
-- imply
  ising3DXAxisRay n ∈ box 3 N := by
-- proof
  apply StatMech.Exact3D.ising3DXAxisRay_mem_box_le h

/--
[ising3DXAxisRay_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DXAxisRay_zero_eq :
-- imply
  ising3DXAxisRay 0 = ising3DOrigin := by
-- proof
  apply StatMech.Exact3D.ising3DXAxisRay_zero

/--
[ising3DYAxisRay_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DYAxisRay_zero_eq :
-- imply
  ising3DYAxisRay 0 = ising3DOrigin := by
-- proof
  apply StatMech.Exact3D.ising3DYAxisRay_zero

/--
[ising3DZAxisRay_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DZAxisRay_zero_eq :
-- imply
  ising3DZAxisRay 0 = ising3DOrigin := by
-- proof
  apply StatMech.Exact3D.ising3DZAxisRay_zero

/--
[blockRepresentative_ising3DXAxisRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockRepresentative_ising3DXAxisRay_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockRepresentative scale (ising3DXAxisRay n) = ising3DXAxisRay (scale.L * n) := by
-- proof
  apply StatMech.Exact3D.blockRepresentative_ising3DXAxisRay scale n

/--
[blockRepresentative_ising3DYAxisRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockRepresentative_ising3DYAxisRay_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockRepresentative scale (ising3DYAxisRay n) = ising3DYAxisRay (scale.L * n) := by
-- proof
  apply StatMech.Exact3D.blockRepresentative_ising3DYAxisRay scale n

/--
[blockRepresentative_ising3DZAxisRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockRepresentative_ising3DZAxisRay_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockRepresentative scale (ising3DZAxisRay n) = ising3DZAxisRay (scale.L * n) := by
-- proof
  apply StatMech.Exact3D.blockRepresentative_ising3DZAxisRay scale n

/--
[blockIndexOf_ising3DXAxisRay_scale_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockIndexOf_ising3DXAxisRay_scale_mul_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockIndexOf scale (ising3DXAxisRay (scale.L * n)) = ising3DXAxisRay n := by
-- proof
  apply StatMech.Exact3D.blockIndexOf_ising3DXAxisRay_scale_mul scale n

/--
[blockIndexOf_ising3DYAxisRay_scale_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockIndexOf_ising3DYAxisRay_scale_mul_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockIndexOf scale (ising3DYAxisRay (scale.L * n)) = ising3DYAxisRay n := by
-- proof
  apply StatMech.Exact3D.blockIndexOf_ising3DYAxisRay_scale_mul scale n

/--
[blockIndexOf_ising3DZAxisRay_scale_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockIndexOf_ising3DZAxisRay_scale_mul_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockIndexOf scale (ising3DZAxisRay (scale.L * n)) = ising3DZAxisRay n := by
-- proof
  apply StatMech.Exact3D.blockIndexOf_ising3DZAxisRay_scale_mul scale n

/--
[blockRemainder_ising3DXAxisRay_scale_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockRemainder_ising3DXAxisRay_scale_mul_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockRemainder scale (ising3DXAxisRay (scale.L * n)) = ising3DOrigin := by
-- proof
  apply StatMech.Exact3D.blockRemainder_ising3DXAxisRay_scale_mul scale n

/--
[blockRemainder_ising3DYAxisRay_scale_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockRemainder_ising3DYAxisRay_scale_mul_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockRemainder scale (ising3DYAxisRay (scale.L * n)) = ising3DOrigin := by
-- proof
  apply StatMech.Exact3D.blockRemainder_ising3DYAxisRay_scale_mul scale n

/--
[blockRemainder_ising3DZAxisRay_scale_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma blockRemainder_ising3DZAxisRay_scale_mul_eq
  {scale : BlockScale}
  {n : ℕ} :
-- imply
  blockRemainder scale (ising3DZAxisRay (scale.L * n)) = ising3DOrigin := by
-- proof
  apply StatMech.Exact3D.blockRemainder_ising3DZAxisRay_scale_mul scale n

/--
[twoPointOnXAxis_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma twoPointOnXAxis_zero_eq
  {β : ℝ} :
-- imply
  twoPointOnXAxis β 0 = 1 := by
-- proof
  apply StatMech.Exact3D.twoPointOnXAxis_zero β

/--
[freeTwoPointOnXAxis_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma freeTwoPointOnXAxis_zero_eq
  {β : ℝ} :
-- imply
  freeTwoPointOnXAxis β 0 = 1 := by
-- proof
  apply StatMech.Exact3D.freeTwoPointOnXAxis_zero β

/--
[Ising3DModel_twoPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_twoPoint_eq_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  TwoPointFunction Ising3DModel β x y = ising3DPlusTwoPoint β x y := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_twoPoint_eq β x y

/--
[Ising3DModel_betaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_betaC_eq_eq :
-- imply
  Ising3DModel.betaC = Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_betaC_eq

/--
[ising3DPlusTwoPoint_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DPlusTwoPoint_symm_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  ising3DPlusTwoPoint β x y = ising3DPlusTwoPoint β y x := by
-- proof
  apply StatMech.Exact3D.ising3DPlusTwoPoint_symm β x y

/--
[ising3DPlusTwoPoint_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DPlusTwoPoint_self_eq
  {β : ℝ}
  {x : Ising3DSite} :
-- imply
  ising3DPlusTwoPoint β x x = 1 := by
-- proof
  apply StatMech.Exact3D.ising3DPlusTwoPoint_self β x

/--
[ising3DFreeTwoPoint_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DFreeTwoPoint_symm_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  ising3DFreeTwoPoint β x y = ising3DFreeTwoPoint β y x := by
-- proof
  apply StatMech.Exact3D.ising3DFreeTwoPoint_symm β x y

/--
[ising3DFreeTwoPoint_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DFreeTwoPoint_self_eq
  {β : ℝ}
  {x : Ising3DSite} :
-- imply
  ising3DFreeTwoPoint β x x = 1 := by
-- proof
  apply StatMech.Exact3D.ising3DFreeTwoPoint_self β x

/--
[abs_spin_mul_spin_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma abs_spin_mul_spin_le_one_eq
  {ω : ConfigSpace Ising3DSite}
  {x y : Ising3DSite} :
-- imply
  |Ising.spin ω x * Ising.spin ω y| ≤ 1 := by
-- proof
  apply StatMech.Exact3D.abs_spin_mul_spin_le_one ω x y

/--
[ising3DPlusTwoPoint_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DPlusTwoPoint_abs_le_one_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  |ising3DPlusTwoPoint β x y| ≤ 1 := by
-- proof
  apply StatMech.Exact3D.ising3DPlusTwoPoint_abs_le_one β x y

/--
[ising3DFreeTwoPoint_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma ising3DFreeTwoPoint_abs_le_one_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  |ising3DFreeTwoPoint β x y| ≤ 1 := by
-- proof
  apply StatMech.Exact3D.ising3DFreeTwoPoint_abs_le_one β x y

/--
[Ising3DModel_twoPoint_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_twoPoint_abs_le_one_eq
  {β : ℝ}
  {x y : Ising3DSite} :
-- imply
  |TwoPointFunction Ising3DModel β x y| ≤ 1 := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_twoPoint_abs_le_one β x y

/--
[Ising3DModel_inverseDecayRate_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_inverseDecayRate_xAxis_eq_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  inverseDecayRate Ising3DModel β ising3DOrigin ising3DXAxisRay n = plusInverseDecayRateOnXAxis β n := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_inverseDecayRate_xAxis_eq β n

/--
[Ising3DModel_lowerInverseCorrelationLength_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_lowerInverseCorrelationLength_xAxis_eq_eq
  {β : ℝ} :
-- imply
  lowerInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = plusLowerInverseCorrelationLengthOnXAxis β := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_lowerInverseCorrelationLength_xAxis_eq β

/--
[Ising3DModel_upperInverseCorrelationLength_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_upperInverseCorrelationLength_xAxis_eq_eq
  {β : ℝ} :
-- imply
  upperInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = plusUpperInverseCorrelationLengthOnXAxis β := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_upperInverseCorrelationLength_xAxis_eq β

/--
[Ising3DModel_liminfCorrelationLength_xAxis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean)
-/
@[path]
private lemma Ising3DModel_liminfCorrelationLength_xAxis_eq_eq
  {β : ℝ} :
-- imply
  liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay = plusLiminfCorrelationLengthOnXAxis β := by
-- proof
  apply StatMech.Exact3D.Ising3DModel_liminfCorrelationLength_xAxis_eq β


-- created on 2026-10-23
