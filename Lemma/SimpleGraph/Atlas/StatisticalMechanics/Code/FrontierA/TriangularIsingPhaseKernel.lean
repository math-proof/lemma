import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingPhaseKernel.Part3
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[triangularIsingSymbol_pos_of_nonnegative_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingSymbol_pos_of_nonnegative_noncritical_eq
  {beta J : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : 0 <= J)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  0 < triangularIsingSymbol beta beta (beta * J) p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_pos_of_nonnegative_noncritical hbeta hJ hcrit p q

/--
[triangularIsing_logSymbol_analyticAt_of_nonnegative_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsing_logSymbol_analyticAt_of_nonnegative_noncritical_eq
  {beta J : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : 0 <= J)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  AnalyticAt Real (fun b : Real => Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsing_logSymbol_analyticAt_of_nonnegative_noncritical hbeta hJ hcrit p q

/--
[triangularIsing_logSymbol_analyticAt_of_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsing_logSymbol_analyticAt_of_le_neg_one_eq
  {beta J : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : J <= -1) :
-- imply
  AnalyticAt Real (fun b : Real => Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsing_logSymbol_analyticAt_of_le_neg_one hbeta hJ p q

/--
[triangularIsingSymbol_pos_at_root_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingSymbol_pos_at_root_of_ne_zero_eq
  {beta J p q : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hp : |p| <= Real.pi)
  (hq : |q| <= Real.pi)
  (hne : p ≠ 0 ∨ q ≠ 0) :
-- imply
  0 < triangularIsingSymbol beta beta (beta * J) p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_pos_at_root_of_ne_zero hbeta hroot hp hq hne

/--
[triangularIsing_logSymbol_analyticAt_at_root_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsing_logSymbol_analyticAt_at_root_of_ne_zero_eq
  {beta J p q : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hp : |p| <= Real.pi)
  (hq : |q| <= Real.pi)
  (hne : p ≠ 0 ∨ q ≠ 0) :
-- imply
  AnalyticAt Real (fun b : Real => Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsing_logSymbol_analyticAt_at_root_of_ne_zero hbeta hroot hp hq hne

/--
[triangularIsingSymbol_quadratic_upper_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingSymbol_quadratic_upper_at_root_eq
  {beta J p q : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  triangularIsingSymbol beta beta (beta * J) p q <= (Real.sinh (2 * beta) / 2 + |Real.sinh (2 * (beta * J))|) * (p ^ 2 + q ^ 2) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_quadratic_upper_at_root hbeta hroot

/--
[triangularIsingCriticalUpperCoefficient_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalUpperCoefficient_pos_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < Real.sinh (2 * beta) / 2 + := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalUpperCoefficient_pos hbeta

/--
[triangularIsingCriticalInverseSymbol_lower_on_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbol_lower_on_wedge_eq
  {beta J x y : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hx : 0 < x)
  (h2xPi : 2 * x <= Real.pi)
  (hxy : x <= y)
  (hy2x : y <= 2 * x) :
-- imply
  1 / ((Real.sinh (2 * beta) / 2 + |Real.sinh (2 * (beta * J))|) * 5 * x ^ 2) <= triangularIsingCriticalInverseSymbol beta J x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbol_lower_on_wedge hbeta hroot hx h2xPi hxy hy2x

/--
[triangularIsingCriticalInverseSymbol_inner_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbol_inner_lower_eq
  {beta J x : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hx : 0 < x)
  (h2xPi : 2 * x <= Real.pi) :
-- imply
  1 / ((Real.sinh (2 * beta) / 2 + |Real.sinh (2 * (beta * J))|) * 5 * x) <= ∫ y in x..(2 * x), triangularIsingCriticalInverseSymbol beta J x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbol_inner_lower hbeta hroot hx h2xPi

/--
[triangularIsingCriticalInverseSymbolClamp_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbolClamp_continuous_eq
  {beta J c epsilon : Real}
-- given
  (hc : 0 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Continuous (Function.uncurry (triangularIsingCriticalInverseSymbolClamp beta J c epsilon)) := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbolClamp_continuous hc hepsilon

/--
[triangularIsingCriticalInverseSymbolClamp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbolClamp_eq_eq
  {beta J c epsilon p q : Real}
-- given
  (hc : 0 < c)
  (hsize : epsilon ^ 2 <= p ^ 2 + q ^ 2)
  (hlower : c * (p ^ 2 + q ^ 2) <= triangularIsingSymbol beta beta (beta * J) p q) :
-- imply
  triangularIsingCriticalInverseSymbolClamp beta J c epsilon p q = triangularIsingCriticalInverseSymbol beta J p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbolClamp_eq hc hsize hlower

/--
[triangularIsingCriticalInverseSymbol_inner_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbol_inner_continuousOn_eq
  {beta J epsilon : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ContinuousOn (fun x : Real => ∫ y in x..(2 * x), triangularIsingCriticalInverseSymbol beta J x y) (Set.Icc epsilon 1) := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbol_inner_continuousOn hbeta hroot hepsilon

/--
[triangularIsingCriticalInverseSymbol_wedge_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbol_wedge_lower_eq
  {beta J epsilon : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hepsilon : 0 < epsilon)
  (hepsilonOne : epsilon <= 1) :
-- imply
  (1 / (2 * (Real.sinh (2 * beta) / 2 + |Real.sinh (2 * (beta * J))|))) * ((2 / 5 : Real) * Real.log (1 / epsilon)) <= ∫ x in epsilon..1, ∫ y in x..(2 * x), triangularIsingCriticalInverseSymbol beta J x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbol_wedge_lower hbeta hroot hepsilon hepsilonOne

/--
[triangularIsingCriticalInverseSymbol_wedge_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbol_wedge_tendsto_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  Tendsto (fun n : Nat => ∫ x in Real.exp (-(n : Real))..1, ∫ y in x..(2 * x), triangularIsingCriticalInverseSymbol beta J x y) atTop atTop := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbol_wedge_tendsto hbeta hroot


-- created on 2026-10-23
