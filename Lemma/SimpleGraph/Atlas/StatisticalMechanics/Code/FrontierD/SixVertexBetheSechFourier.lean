import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierD


/--
[integral_Ioi_cpow_div_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma integral_Ioi_cpow_div_one_add_eq
  {u : Complex} :
-- imply
  (∫ y : Real in Set.Ioi 0, (y : Complex) ^ (u - 1) / (1 + y)) = Complex.betaIntegral u (1 - u) := by
-- proof
  apply StatMech.FrontierD.integral_Ioi_cpow_div_one_add u

/--
[integral_cexp_mul_div_one_add_rexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma integral_cexp_mul_div_one_add_rexp_eq
  {u : Complex} :
-- imply
  (∫ x : Real, Complex.exp (u * x) / (1 + Real.exp x)) = Complex.betaIntegral u (1 - u) := by
-- proof
  apply StatMech.FrontierD.integral_cexp_mul_div_one_add_rexp u

/--
[betaIntegral_one_sub_eq_pi_div_sin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma betaIntegral_one_sub_eq_pi_div_sin_eq
  {u : Complex}
-- given
  (hu0 : 0 < u.re)
  (hu1 : u.re < 1) :
-- imply
  Complex.betaIntegral u (1 - u) = Real.pi / Complex.sin (Real.pi * u) := by
-- proof
  apply StatMech.FrontierD.betaIntegral_one_sub_eq_pi_div_sin hu0 hu1

/--
[betaIntegral_half_sub_mul_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma betaIntegral_half_sub_mul_I_eq
  {t : Real} :
-- imply
  Complex.betaIntegral ((1 : Complex) / 2 - (t / Real.pi) * Complex.I) (1 - ((1 : Complex) / 2 - (t / Real.pi) * Complex.I)) = Real.pi / Real.cosh t := by
-- proof
  apply StatMech.FrontierD.betaIntegral_half_sub_mul_I t

/--
[integral_fourier_sech](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma integral_fourier_sech_eq
  {lam : Real}
  {n : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∫ x : Real, Complex.exp ((-2 * Real.pi * (x * n) : Real) * Complex.I) / Real.cosh (Real.pi ^ 2 * x / lam)) = (lam / Real.pi : Real) / Real.cosh (n * lam) := by
-- proof
  apply StatMech.FrontierD.integral_fourier_sech hlam n

/--
[continuous_sixVertexSechProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma continuous_sixVertexSechProfile_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Continuous (sixVertexSechProfile lam) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexSechProfile hlam

/--
[fourier_sixVertexSechProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma fourier_sixVertexSechProfile_eq
  {lam : Real}
  {n : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  𝓕 (sixVertexSechProfile lam) n = (1 / (2 * Real.cosh (n * lam)) : Real) := by
-- proof
  apply StatMech.FrontierD.fourier_sixVertexSechProfile hlam n

/--
[summable_one_div_two_cosh_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma summable_one_div_two_cosh_nat_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n : Nat => ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex)) := by
-- proof
  apply StatMech.FrontierD.summable_one_div_two_cosh_nat hlam

/--
[summable_fourier_sixVertexSechProfile_int](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma summable_fourier_sixVertexSechProfile_int_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n : Int => FourierTransform.fourier (sixVertexSechProfile lam) (n : Real)) := by
-- proof
  apply StatMech.FrontierD.summable_fourier_sixVertexSechProfile_int hlam

/--
[isBigO_one_div_cosh_mul_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma isBigO_one_div_cosh_mul_cocompact_eq
  {a : Real}
-- given
  (ha : 0 < a) :
-- imply
  (fun x : Real => ((1 / Real.cosh (a * x) : Real) : Complex)) =O[cocompact Real] fun x : Real => := by
-- proof
  apply StatMech.FrontierD.isBigO_one_div_cosh_mul_cocompact ha

/--
[isBigO_sixVertexSechProfile_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma isBigO_sixVertexSechProfile_cocompact_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexSechProfile lam =O[cocompact Real] fun x : Real => := by
-- proof
  apply StatMech.FrontierD.isBigO_sixVertexSechProfile_cocompact hlam

/--
[sixVertexSechProfile_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma sixVertexSechProfile_poisson_eq
  {lam : Real}
  {x : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (∑' n : Int, sixVertexSechProfile lam (x + n)) = ∑' n : Int, ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex) * fourier n (x : UnitAddCircle) := by
-- proof
  apply StatMech.FrontierD.sixVertexSechProfile_poisson hlam x

/--
[ofReal_sixVertexFourierRootDensity_eq_tsum_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma ofReal_sixVertexFourierRootDensity_eq_tsum_phase_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  (sixVertexFourierRootDensity lam alpha : Complex) = ∑' n : Int, sixVertexSechPhaseTerm lam alpha n := by
-- proof
  apply StatMech.FrontierD.ofReal_sixVertexFourierRootDensity_eq_tsum_phase hlam alpha

/--
[summable_sixVertexSechProfile_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma summable_sixVertexSechProfile_shift_eq
  {lam : Real}
  {x : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (fun n : Int => sixVertexSechProfile lam (x + n)) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexSechProfile_shift hlam x

/--
[sixVertexFourierRootDensity_eq_tsum_sechProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma sixVertexFourierRootDensity_eq_tsum_sechProfile_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexFourierRootDensity lam alpha = ∑' n : Int, Real.pi / (2 * lam) / Real.cosh (Real.pi ^ 2 * (alpha / (2 * Real.pi) + n) / lam) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierRootDensity_eq_tsum_sechProfile hlam alpha

/--
[sixVertexFourierRootDensity_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma sixVertexFourierRootDensity_pos_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  0 < sixVertexFourierRootDensity lam alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierRootDensity_pos hlam alpha

/--
[sixVertexFourierPhysicalDensity_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensity_pos_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexFourierPhysicalDensity c hc x := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensity_pos hc x

/--
[sixVertexFourierPhysicalDensityFamily_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensityFamily_pos_eq
  {a b : Real}
  {z : Set.Icc a b × Real}
-- given
  (ha : 2 < a) :
-- imply
  0 < sixVertexFourierPhysicalDensityFamily (b := b) ha z := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensityFamily_pos ha z

/--
[exists_uniformLower_sixVertexFourierPhysicalDensityFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma exists_uniformLower_sixVertexFourierPhysicalDensityFamily_eq
  {a b : Real}
-- given
  (ha : 2 < a)
  (hab : a ≤ b) :
-- imply
  ∃ rhoLower : Real, 0 < rhoLower ∧ ∀ (t : Set.Icc a b) (x : Real), rhoLower ≤ sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha) t x := by
-- proof
  apply StatMech.FrontierD.exists_uniformLower_sixVertexFourierPhysicalDensityFamily ha hab

/--
[fourier_sech](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean)
-/
@[path]
private lemma fourier_sech_eq
  {lam : Real}
  {n : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  FourierTransform.fourier (fun x : Real => ((1 / Real.cosh (Real.pi ^ 2 * x / lam) : Real) : Complex)) n = (lam / Real.pi : Real) / Real.cosh (n * lam) := by
-- proof
  apply StatMech.FrontierD.fourier_sech hlam n


-- created on 2026-10-23
