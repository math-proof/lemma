import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[hasDerivAt_triangularIsingSymbol_along_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingSymbol_along_ray_eq
  {J beta p q : Real} :
-- imply
  HasDerivAt (fun b => triangularIsingSymbol b b (b * J) p q) (triangularIsingRaySymbolDeriv J beta p q) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingSymbol_along_ray J beta p q

/--
[triangularIsingRaySymbolDeriv_sub_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingRaySymbolDeriv_sub_zero_eq
  {J beta p q : Real} :
-- imply
  triangularIsingRaySymbolDeriv J beta p q - triangularIsingRaySymbolDeriv J beta 0 0 = 2 * Real.cosh (2 * beta) * ((1 - Real.cos p) + (1 - Real.cos q)) + 2 * J * Real.cosh (2 * beta * J) * (1 - Real.cos (p + q)) := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolDeriv_sub_zero J beta p q

/--
[triangularIsingRaySymbolDeriv_zero_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingRaySymbolDeriv_zero_at_root_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  triangularIsingRaySymbolDeriv J beta 0 0 = 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolDeriv_zero_at_root hbeta hroot

/--
[differentiable_triangularIsingRaySymbolDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma differentiable_triangularIsingRaySymbolDeriv_eq
  {J p q : Real} :
-- imply
  Differentiable Real (fun b => triangularIsingRaySymbolDeriv J b p q) := by
-- proof
  apply StatMech.FrontierA.differentiable_triangularIsingRaySymbolDeriv J p q

/--
[exists_triangularIsingCriticalRay_local_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma exists_triangularIsingCriticalRay_local_bounds_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  ∃ U : Set Real, U ∈ nhds beta ∧ IsOpen U ∧ ∃ m K : Real, 0 < m ∧ 0 < K ∧ ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))) := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingCriticalRay_local_bounds hbeta hJ hroot

/--
[hasDerivAt_log_triangularIsingSymbol_along_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma hasDerivAt_log_triangularIsingSymbol_along_ray_eq
  {J b p q : Real}
-- given
  (hpos : 0 < triangularIsingSymbol b b (b * J) p q) :
-- imply
  HasDerivAt (fun t => Real.log (triangularIsingSymbol t t (t * J) p q)) (triangularIsingRayLogDeriv J b p q) b := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_log_triangularIsingSymbol_along_ray hpos

/--
[triangularIsingRayLogDeriv_abs_le_criticalMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv_abs_le_criticalMajorant_eq
  {beta J m K b x y : Real}
-- given
  (hm : 0 < m)
  (hK : 0 < K)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0)
  (hy0 : y ≠ 0)
  (hlower : m * ((b - beta) ^ 2 + ((1 - Real.cos x) + (1 - Real.cos y))) <= triangularIsingSymbol b b (b * J) x y)
  (hderiv : |triangularIsingRaySymbolDeriv J b x y| <= K * (2 * |b - beta| + ((1 - Real.cos x) + (1 - Real.cos y)))) :
-- imply
  |triangularIsingRayLogDeriv J b x y| <= triangularIsingCriticalFirstMajorant m K x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv_abs_le_criticalMajorant hm hK hx hy hx0 hy0 hlower hderiv

/--
[triangularIsingCriticalFirstMajorant_inner_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingCriticalFirstMajorant_inner_intervalIntegrable_eq
  {m K : Real}
  {x : Real} :
-- imply
  IntervalIntegrable (triangularIsingCriticalFirstMajorant m K x) volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalFirstMajorant_inner_intervalIntegrable x

/--
[triangularIsingCriticalFirstMajorant_inner_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingCriticalFirstMajorant_inner_integral_eq
  {m K x : Real} :
-- imply
  (∫ y in (-Real.pi)..Real.pi, triangularIsingCriticalFirstMajorant m K x y) = (K / m) * (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x * (∫ y in (-Real.pi)..Real.pi, StatMech.Onsager.ons_criticalOneDimMajorant y) + 2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalFirstMajorant_inner_integral m K x

/--
[triangularIsingCriticalFirstOuterMajorant_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingCriticalFirstOuterMajorant_intervalIntegrable_eq
  {m K : Real} :
-- imply
  IntervalIntegrable (triangularIsingCriticalFirstOuterMajorant m K) volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalFirstOuterMajorant_intervalIntegrable

/--
[triangularIsingRaySymbolAbsBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingRaySymbolAbsBound_pos_eq
  {J b : Real} :
-- imply
  0 < triangularIsingRaySymbolAbsBound J b := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolAbsBound_pos J b

/--
[triangularIsingSymbol_le_rayAbsBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingSymbol_le_rayAbsBound_eq
  {J b p q : Real} :
-- imply
  triangularIsingSymbol b b (b * J) p q <= triangularIsingRaySymbolAbsBound J b := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_le_rayAbsBound J b p q

/--
[triangularIsingCriticalLogBound_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingCriticalLogBound_intervalIntegrable_eq
  {m J b : Real} :
-- imply
  IntervalIntegrable (triangularIsingCriticalLogBound m J b) volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalLogBound_intervalIntegrable

/--
[triangularIsing_logSymbol_abs_le_criticalLogBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsing_logSymbol_abs_le_criticalLogBound_eq
  {beta J m b x y : Real}
-- given
  (hm : 0 < m)
  (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
  (hy0 : y ≠ 0)
  (hlower : m * ((b - beta) ^ 2 + ((1 - Real.cos x) + (1 - Real.cos y))) <= triangularIsingSymbol b b (b * J) x y) :
-- imply
  |Real.log (triangularIsingSymbol b b (b * J) x y)| <= triangularIsingCriticalLogBound m J b y := by
-- proof
  apply StatMech.FrontierA.triangularIsing_logSymbol_abs_le_criticalLogBound hm hy hy0 hlower

/--
[triangularIsingSymbol_pos_of_critical_local_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingSymbol_pos_of_critical_local_bounds_eq
  {beta J m K : Real}
  {U : Set Real}
  {b x y : Real}
-- given
  (hm : 0 < m)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  0 < triangularIsingSymbol b b (b * J) x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_pos_of_critical_local_bounds hm hbounds hb hx hx0

/--
[continuous_triangularIsing_log_right_of_critical_local_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma continuous_triangularIsing_log_right_of_critical_local_bounds_eq
  {beta J m K b x : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  Continuous (fun y => Real.log (triangularIsingSymbol b b (b * J) x y)) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsing_log_right_of_critical_local_bounds hm hbounds hb hx hx0

/--
[continuous_triangularIsing_logDeriv_right_of_critical_local_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma continuous_triangularIsing_logDeriv_right_of_critical_local_bounds_eq
  {beta J m K b x : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  Continuous (fun y => triangularIsingRayLogDeriv J b x y) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsing_logDeriv_right_of_critical_local_bounds hm hbounds hb hx hx0

/--
[continuous_triangularIsing_criticalInnerLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma continuous_triangularIsing_criticalInnerLog_eq
  {beta J m K b : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U) :
-- imply
  Continuous (fun x => ∫ y in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol b b (b * J) x y)) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsing_criticalInnerLog hm hbounds hb

/--
[hasDerivAt_triangularIsing_criticalInnerIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsing_criticalInnerIntegral_eq
  {beta J m K b x : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hK : 0 < K)
  (hUopen : IsOpen U)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  HasDerivAt (fun t => ∫ y in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol t t (t * J) x y)) (∫ y in (-Real.pi)..Real.pi, triangularIsingRayLogDeriv J b x y) b := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsing_criticalInnerIntegral hm hK hUopen hbounds hb hx hx0

/--
[triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable_eq
  {J b : Real} :
-- imply
  AEStronglyMeasurable (fun x => ∫ y in (-Real.pi)..Real.pi, triangularIsingRayLogDeriv J b x y) (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
-- proof
  apply StatMech.FrontierA.triangularIsing_criticalInnerLogDeriv_aestronglyMeasurable J b

/--
[triangularIsing_criticalInnerLogDeriv_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsing_criticalInnerLogDeriv_norm_le_eq
  {beta J m K b x : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hK : 0 < K)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  ‖∫ y in (-Real.pi)..Real.pi, triangularIsingRayLogDeriv J b x y‖ <= triangularIsingCriticalFirstOuterMajorant m K x := by
-- proof
  apply StatMech.FrontierA.triangularIsing_criticalInnerLogDeriv_norm_le hm hK hbounds hb hx hx0

/--
[hasDerivAt_triangularIsing_criticalDoubleIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsing_criticalDoubleIntegral_eq
  {beta J m K b : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hK : 0 < K)
  (hUopen : IsOpen U)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U) :
-- imply
  HasDerivAt (fun t => ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol t t (t * J) x y)) (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, triangularIsingRayLogDeriv J b x y) b := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsing_criticalDoubleIntegral hm hK hUopen hbounds hb

/--
[continuousAt_triangularIsing_criticalInnerLogDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma continuousAt_triangularIsing_criticalInnerLogDeriv_eq
  {beta J m K b x : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hK : 0 < K)
  (hUopen : IsOpen U)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  ContinuousAt (fun t => ∫ y in (-Real.pi)..Real.pi, triangularIsingRayLogDeriv J t x y) b := by
-- proof
  apply StatMech.FrontierA.continuousAt_triangularIsing_criticalInnerLogDeriv hm hK hUopen hbounds hb hx hx0

/--
[continuousAt_triangularIsing_criticalDoubleLogDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma continuousAt_triangularIsing_criticalDoubleLogDeriv_eq
  {beta J m K b : Real}
  {U : Set Real}
-- given
  (hm : 0 < m)
  (hK : 0 < K)
  (hUopen : IsOpen U)
  (hbounds : ∀ b ∈ U, ∀ p q : Real, m * ((b - beta) ^ 2 + ((1 - Real.cos p) + (1 - Real.cos q))) <= triangularIsingSymbol b b (b * J) p q ∧ |triangularIsingRaySymbolDeriv J b p q| <= K * (2 * |b - beta| + ((1 - Real.cos p) + (1 - Real.cos q))))
  (hb : b ∈ U) :
-- imply
  ContinuousAt (fun t => ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, triangularIsingRayLogDeriv J t x y) b := by
-- proof
  apply StatMech.FrontierA.continuousAt_triangularIsing_criticalDoubleLogDeriv hm hK hUopen hbounds hb

/--
[triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  ContDiffAt Real 1 (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root hbeta hJ hroot

/--
[triangularIsingFreeEnergyValue_contDiffAt_one_of_nonnegative_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyValue_contDiffAt_one_of_nonnegative_root_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : 0 <= J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  ContDiffAt Real 1 (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyValue_contDiffAt_one_of_nonnegative_root hbeta hJ hroot


-- created on 2026-10-23
