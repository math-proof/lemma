import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
open StatMech StatMech.FrontierD


/--
[intervalIntegral_cos_int_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierOrthogonality.lean)
-/
@[path]
private lemma intervalIntegral_cos_int_mul_eq
  {z : Int} :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((z : Real) * beta)) = if z = 0 then 2 * Real.pi else 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_cos_int_mul z

/--
[intervalIntegral_sin_int_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierOrthogonality.lean)
-/
@[path]
private lemma intervalIntegral_sin_int_mul_eq
  {z : Int} :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.sin ((z : Real) * beta)) = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sin_int_mul z

/--
[intervalIntegral_cos_nat_mul_mul_cos_nat_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierOrthogonality.lean)
-/
@[path]
private lemma intervalIntegral_cos_nat_mul_mul_cos_nat_mul_eq
  {m n : Nat}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((m : Real) * beta) * Real.cos ((n : Real) * beta)) = if m = n then Real.pi else 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_cos_nat_mul_mul_cos_nat_mul hm hn

/--
[intervalIntegral_sin_nat_mul_mul_cos_nat_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierOrthogonality.lean)
-/
@[path]
private lemma intervalIntegral_sin_nat_mul_mul_cos_nat_mul_eq
  {m n : Nat} :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.sin ((m : Real) * beta) * Real.cos ((n : Real) * beta)) = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sin_nat_mul_mul_cos_nat_mul m n

/--
[intervalIntegral_cos_nat_mul_sub_mul_cos_nat_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierOrthogonality.lean)
-/
@[path]
private lemma intervalIntegral_cos_nat_mul_sub_mul_cos_nat_mul_eq
  {m n : Nat}
  {alpha : Real}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  (∫ beta in -Real.pi..Real.pi, Real.cos ((m : Real) * (alpha - beta)) * Real.cos ((n : Real) * beta)) = if m = n then Real.pi * Real.cos ((m : Real) * alpha) else 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_cos_nat_mul_sub_mul_cos_nat_mul hm hn alpha


-- created on 2026-10-23
