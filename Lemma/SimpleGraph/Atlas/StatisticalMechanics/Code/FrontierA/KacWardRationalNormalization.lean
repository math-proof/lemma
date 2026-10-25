import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
open StatMech StatMech.FrontierA


/--
[kwRatCommonDenominator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma kwRatCommonDenominator_pos_eq
  {n : ℕ}
  {q : Fin n → ℚ × ℚ} :
-- imply
  0 < kwRatCommonDenominator q := by
-- proof
  apply StatMech.FrontierA.kwRatCommonDenominator_pos q

/--
[kwRatCommonDenominator_first_den_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma kwRatCommonDenominator_first_den_dvd_eq
  {n : ℕ}
  {q : Fin n → ℚ × ℚ}
  {i : Fin n} :
-- imply
  (q i).1.den ∣ kwRatCommonDenominator q := by
-- proof
  apply StatMech.FrontierA.kwRatCommonDenominator_first_den_dvd q i

/--
[kwRatCommonDenominator_second_den_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma kwRatCommonDenominator_second_den_dvd_eq
  {n : ℕ}
  {q : Fin n → ℚ × ℚ}
  {i : Fin n} :
-- imply
  (q i).2.den ∣ kwRatCommonDenominator q := by
-- proof
  apply StatMech.FrontierA.kwRatCommonDenominator_second_den_dvd q i

/--
[exists_int_eq_nat_mul_ratCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma exists_int_eq_nat_mul_ratCast_eq
  {q : ℚ}
  {D : ℕ}
-- given
  (hD : q.den ∣ D) :
-- imply
  ∃ z : ℤ, (D : ℝ) * (q : ℝ) = (z : ℝ) := by
-- proof
  apply StatMech.FrontierA.exists_int_eq_nat_mul_ratCast q D hD

/--
[kwRatVertex_clear_denominators](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma kwRatVertex_clear_denominators_eq
  {n : ℕ}
  {q : Fin n → ℚ × ℚ} :
-- imply
  ∃ p : Fin n → ℤ × ℤ, ∀ i : Fin n, (kwRatCommonDenominator q : ℝ) * kwRatVertex q i = kwIntComplex (p i) := by
-- proof
  apply StatMech.FrontierA.kwRatVertex_clear_denominators q

/--
[kwPositiveScaleLinearEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma kwPositiveScaleLinearEquiv_apply_eq
  {s : ℝ}
  {z : ℂ}
-- given
  (hs : 0 < s) :
-- imply
  kwPositiveScaleLinearEquiv s hs z = (s : ℂ) * z := by
-- proof
  apply StatMech.FrontierA.kwPositiveScaleLinearEquiv_apply s hs z

/--
[Complex.arg_posReal_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma arg_posReal_mul_eq
  {s : ℝ}
  {z : ℂ}
-- given
  (hs : 0 < s)
  (hz : z ≠ 0) :
-- imply
  Complex.arg ((s : ℂ) * z) = Complex.arg z := by
-- proof
  apply StatMech.FrontierA.Complex.arg_posReal_mul s hs z hz

/--
[kwVectorTurnPhase_pos_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma kwVectorTurnPhase_pos_scale_eq
  {s : ℝ}
  {z w : ℂ}
-- given
  (hs : 0 < s)
  (hz : z ≠ 0)
  (hw : w ≠ 0) :
-- imply
  kwVectorTurnPhase ((s : ℂ) * z) ((s : ℂ) * w) = kwVectorTurnPhase z w := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_pos_scale s hs z w hz hw

/--
[KWFiniteSimplePolygon.phaseCycle_mapPositiveScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma phaseCycle_mapPositiveScale_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {s : ℝ}
-- given
  (hs : 0 < s) :
-- imply
  kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle (polygon.mapLinearEquiv (kwPositiveScaleLinearEquiv s hs)).edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_mapPositiveScale polygon s hs

/--
[KWFiniteSimplePolygon.exists_integral_positive_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma exists_integral_positive_scale_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {q : Fin n → ℚ × ℚ}
-- given
  (hvertex : polygon.vertex = kwRatVertex q) :
-- imply
  ∃ (D : ℕ) (hD : 0 < D) (p : Fin n → ℤ × ℤ), let scaled := polygon.mapLinearEquiv (kwPositiveScaleLinearEquiv (D : ℝ) (by exact_mod_cast hD)) ∀ i : Fin n, scaled.vertex i = kwIntComplex (p i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_integral_positive_scale polygon q hvertex

/--
[KWFiniteSimplePolygon.exists_integral_phaseModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean)
-/
@[path]
private lemma exists_integral_phaseModel_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0) :
-- imply
  ∃ (p : Fin n → ℤ × ℤ) (integral : KWFiniteSimplePolygon n), integral.vertex = (fun i ↦ kwIntComplex (p i)) ∧ kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle integral.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_integral_phaseModel polygon hcross


-- created on 2026-10-23
