import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
open Filter MeasureTheory Topology Complex StatMech StatMech.FrontierA


/--
[triangularIsingRaySymbolComplex_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRaySymbolComplex_ofReal_eq
  {beta J p q : Real} :
-- imply
  triangularIsingRaySymbolComplex J beta p q = (triangularIsingSymbol beta beta (beta * J) p q : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolComplex_ofReal beta J p q

/--
[triangularIsingRayGap_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRayGap_pos_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  0 < triangularIsingRayGap beta J := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayGap_pos hbeta hcrit

/--
[triangularIsingRayGap_le_symbol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRayGap_le_symbol_eq
  {beta J : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  triangularIsingRayGap beta J <= triangularIsingSymbol beta beta (beta * J) p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayGap_le_symbol hbeta p q

/--
[continuous_triangularIsingComplexControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma continuous_triangularIsingComplexControl_eq
  {beta J : Real} :
-- imply
  Continuous (triangularIsingComplexControl beta J) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingComplexControl beta J

/--
[triangularIsingComplexControl_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexControl_ofReal_eq
  {beta J : Real} :
-- imply
  triangularIsingComplexControl beta J beta = 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexControl_ofReal beta J

/--
[triangularIsingComplexRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexRadius_pos_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  0 < triangularIsingComplexRadius beta J := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexRadius_pos hbeta hcrit

/--
[triangularIsingComplexNeighborhood_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexNeighborhood_isOpen_eq
  {beta J : Real} :
-- imply
  IsOpen (triangularIsingComplexNeighborhood beta J) := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexNeighborhood_isOpen beta J

/--
[triangularIsingComplexNeighborhood_mem_nhds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexNeighborhood_mem_nhds_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  triangularIsingComplexNeighborhood beta J ∈ nhds (beta : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexNeighborhood_mem_nhds hbeta hcrit

/--
[triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control_eq
  {beta J : Real}
  {z : Complex}
  {p q : Real} :
-- imply
  ‖triangularIsingRaySymbolComplex J z p q - (triangularIsingSymbol beta beta (beta * J) p q : Complex)‖ <= triangularIsingComplexControl beta J z := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control beta J z p q

/--
[triangularIsingComplexRadius_le_gap_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexRadius_le_gap_half_eq
  {beta J : Real} :
-- imply
  triangularIsingComplexRadius beta J <= triangularIsingRayGap beta J / 2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexRadius_le_gap_half beta J

/--
[triangularIsingComplexRadius_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexRadius_le_one_eq
  {beta J : Real} :
-- imply
  triangularIsingComplexRadius beta J <= 1 := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexRadius_le_one beta J

/--
[triangularIsingComplex_factor_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplex_factor_bounds_eq
  {beta J : Real}
  {z : Complex}
-- given
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  ‖Complex.cosh (2 * z)‖ < := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplex_factor_bounds hz

/--
[triangularIsingRaySymbolComplex_re_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRaySymbolComplex_re_pos_eq
  {beta J : Real}
  {z : Complex}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  0 < (triangularIsingRaySymbolComplex J z p q).re := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolComplex_re_pos hbeta hcrit hz p q

/--
[triangularIsingRaySymbolComplex_mem_slitPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRaySymbolComplex_mem_slitPlane_eq
  {beta J : Real}
  {z : Complex}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  triangularIsingRaySymbolComplex J z p q ∈ Complex.slitPlane := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolComplex_mem_slitPlane hbeta hcrit hz p q

/--
[triangularIsingRaySymbolComplex_norm_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingRaySymbolComplex_norm_lower_eq
  {beta J : Real}
  {z : Complex}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  triangularIsingRayGap beta J / 2 < ‖triangularIsingRaySymbolComplex J z p q‖ := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolComplex_norm_lower hbeta hcrit hz p q

/--
[triangularIsingLogRaySymbolComplexDeriv_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingLogRaySymbolComplexDeriv_norm_le_eq
  {beta J : Real}
  {z : Complex}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  ‖triangularIsingLogRaySymbolComplexDeriv J z p q‖ <= triangularIsingComplexDerivBound beta J / (triangularIsingRayGap beta J / 2) := by
-- proof
  apply StatMech.FrontierA.triangularIsingLogRaySymbolComplexDeriv_norm_le hbeta hcrit hz p q

/--
[hasDerivAt_triangularIsingRaySymbolComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingRaySymbolComplex_eq
  {J : Real}
  {z : Complex}
  {p q : Real} :
-- imply
  HasDerivAt (fun w => triangularIsingRaySymbolComplex J w p q) (triangularIsingRaySymbolComplexDeriv J z p q) z := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingRaySymbolComplex J z p q

/--
[hasDerivAt_log_triangularIsingRaySymbolComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma hasDerivAt_log_triangularIsingRaySymbolComplex_eq
  {beta J : Real}
  {z : Complex}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  HasDerivAt (fun w => Complex.log (triangularIsingRaySymbolComplex J w p q)) (triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_log_triangularIsingRaySymbolComplex hbeta hcrit hz p q

/--
[continuous_triangularIsingComplexLog_momenta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma continuous_triangularIsingComplexLog_momenta_eq
  {beta J : Real}
  {z : Complex}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  Continuous (fun x : Real × Real => Complex.log (triangularIsingRaySymbolComplex J z x.1 x.2)) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingComplexLog_momenta hbeta hcrit hz

/--
[continuous_triangularIsingComplexLogDeriv_momenta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma continuous_triangularIsingComplexLogDeriv_momenta_eq
  {beta J : Real}
  {z : Complex}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  Continuous (fun x : Real × Real => triangularIsingLogRaySymbolComplexDeriv J z x.1 x.2) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingComplexLogDeriv_momenta hbeta hcrit hz

/--
[continuous_triangularIsingComplexInnerLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma continuous_triangularIsingComplexInnerLog_eq
  {beta J : Real}
  {z : Complex}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  Continuous (fun p => ∫ q in (-Real.pi)..Real.pi, Complex.log (triangularIsingRaySymbolComplex J z p q)) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingComplexInnerLog hbeta hcrit hz

/--
[continuous_triangularIsingComplexInnerLogDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma continuous_triangularIsingComplexInnerLogDeriv_eq
  {beta J : Real}
  {z : Complex}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  Continuous (fun p => ∫ q in (-Real.pi)..Real.pi, triangularIsingLogRaySymbolComplexDeriv J z p q) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingComplexInnerLogDeriv hbeta hcrit hz

/--
[hasDerivAt_triangularIsingComplexInnerIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingComplexInnerIntegral_eq
  {beta J : Real}
  {z : Complex}
  {p : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  HasDerivAt (fun w => ∫ q in (-Real.pi)..Real.pi, Complex.log (triangularIsingRaySymbolComplex J w p q)) (∫ q in (-Real.pi)..Real.pi, triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingComplexInnerIntegral p hbeta hcrit hz

/--
[hasDerivAt_triangularIsingComplexDoubleIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingComplexDoubleIntegral_eq
  {beta J : Real}
  {z : Complex}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  HasDerivAt (fun w => ∫ p in (-Real.pi)..Real.pi, ∫ q in (-Real.pi)..Real.pi, Complex.log (triangularIsingRaySymbolComplex J w p q)) (∫ p in (-Real.pi)..Real.pi, ∫ q in (-Real.pi)..Real.pi, triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingComplexDoubleIntegral hbeta hcrit hz

/--
[differentiableOn_triangularIsingFreeEnergyRayComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma differentiableOn_triangularIsingFreeEnergyRayComplex_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  DifferentiableOn Complex (triangularIsingFreeEnergyRayComplex J) (triangularIsingComplexNeighborhood beta J) := by
-- proof
  apply StatMech.FrontierA.differentiableOn_triangularIsingFreeEnergyRayComplex hbeta hcrit

/--
[analyticAt_triangularIsingFreeEnergyRayComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma analyticAt_triangularIsingFreeEnergyRayComplex_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  AnalyticAt Complex (triangularIsingFreeEnergyRayComplex J) beta := by
-- proof
  apply StatMech.FrontierA.analyticAt_triangularIsingFreeEnergyRayComplex hbeta hcrit

/--
[triangularIsingComplexLog_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexLog_ofReal_eq
  {beta J b : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  Complex.log (triangularIsingRaySymbolComplex J b p q) = (Real.log (triangularIsingSymbol b b (b * J) p q) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexLog_ofReal hbeta hcrit hb p q

/--
[triangularIsingComplexDoubleIntegral_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingComplexDoubleIntegral_ofReal_eq
  {beta J b : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  (∫ p in (-Real.pi)..Real.pi, ∫ q in (-Real.pi)..Real.pi, Complex.log (triangularIsingRaySymbolComplex J b p q)) = Complex.ofReal (∫ p in (-Real.pi)..Real.pi, ∫ q in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol b b (b * J) p q)) := by
-- proof
  apply StatMech.FrontierA.triangularIsingComplexDoubleIntegral_ofReal hbeta hcrit hb

/--
[triangularIsingFreeEnergyRayComplex_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyRayComplex_ofReal_eq
  {beta J b : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
  (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
-- imply
  triangularIsingFreeEnergyRayComplex J b = (triangularIsingFreeEnergyValue b b (b * J) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyRayComplex_ofReal hbeta hcrit hb

/--
[triangularIsingFreeEnergyValue_analyticAt_of_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyValue_analyticAt_of_noncritical_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  AnalyticAt Real (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta hcrit

/--
[triangularIsingFreeEnergyValue_analyticAt_of_gt_neg_one_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyValue_analyticAt_of_gt_neg_one_noncritical_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (_hJ : -1 < J)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  AnalyticAt Real (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyValue_analyticAt_of_gt_neg_one_noncritical hbeta _hJ hcrit

/--
[triangularIsingCriticalRate_ne_one_of_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingCriticalRate_ne_one_of_le_neg_one_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : J <= -1) :
-- imply
  triangularIsingCriticalRate beta (beta * J) ≠ 1 := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalRate_ne_one_of_le_neg_one hbeta hJ

/--
[triangularIsingFreeEnergyValue_analyticAt_of_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyValue_analyticAt_of_le_neg_one_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : J <= -1) :
-- imply
  AnalyticAt Real (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyValue_analyticAt_of_le_neg_one hbeta hJ

/--
[triangularIsingFreeEnergyValue_analyticAt_of_nonnegative_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean)
-/
@[path]
private lemma triangularIsingFreeEnergyValue_analyticAt_of_nonnegative_noncritical_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (_hJ : 0 <= J)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  AnalyticAt Real (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergyValue_analyticAt_of_nonnegative_noncritical hbeta _hJ hcrit


-- created on 2026-10-23
