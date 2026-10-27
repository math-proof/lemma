import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalSecond.Part3
open Filter MeasureTheory Topology StatMech StatMech.FrontierA


/--
[hasDerivAt_triangularIsingRaySymbolDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingRaySymbolDeriv_eq
  {J beta p q : Real} :
-- imply
  HasDerivAt (fun b => triangularIsingRaySymbolDeriv J b p q) (triangularIsingRaySymbolDeriv2 J beta p q) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingRaySymbolDeriv J beta p q

/--
[hasDerivAt_triangularIsingRayLogDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingRayLogDeriv_eq
  {J beta p q : Real}
-- given
  (hne : triangularIsingSymbol beta beta (beta * J) p q ≠ 0) :
-- imply
  HasDerivAt (fun b => triangularIsingRayLogDeriv J b p q) (triangularIsingRayLogDeriv2 J beta p q) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingRayLogDeriv hne

/--
[triangularIsingRaySymbolDeriv2_zero_pos_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRaySymbolDeriv2_zero_pos_at_root_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  0 < triangularIsingRaySymbolDeriv2 J beta 0 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolDeriv2_zero_pos_at_root hbeta hJ hroot

/--
[triangularIsingRaySymbolDeriv2_sub_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRaySymbolDeriv2_sub_zero_eq
  {J beta p q : Real} :
-- imply
  triangularIsingRaySymbolDeriv2 J beta p q - triangularIsingRaySymbolDeriv2 J beta 0 0 = 4 * Real.sinh (2 * beta) * ((1 - Real.cos p) + (1 - Real.cos q)) + 4 * J ^ 2 * Real.sinh (2 * beta * J) * (1 - Real.cos (p + q)) := by
-- proof
  apply StatMech.FrontierA.triangularIsingRaySymbolDeriv2_sub_zero J beta p q

/--
[triangularIsingRayLogDeriv2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2_eq_eq
  {J beta p q : Real}
-- given
  (hne : triangularIsingSymbol beta beta (beta * J) p q ≠ 0) :
-- imply
  triangularIsingRayLogDeriv2 J beta p q = triangularIsingRaySymbolDeriv2 J beta p q / triangularIsingSymbol beta beta (beta * J) p q - (triangularIsingRaySymbolDeriv J beta p q / triangularIsingSymbol beta beta (beta * J) p q) ^ 2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2_eq hne

/--
[exists_triangularIsingRayLogDeriv2_lower_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma exists_triangularIsingRayLogDeriv2_lower_at_root_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  ∃ a C : Real, 0 < a ∧ 0 <= C ∧ ∀ p q : Real, := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingRayLogDeriv2_lower_at_root hbeta hJ hroot

/--
[triangularIsingRayLogDeriv2Clamp_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2Clamp_continuous_eq
  {beta J c epsilon : Real}
-- given
  (hc : 0 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  Continuous (Function.uncurry (triangularIsingRayLogDeriv2Clamp beta J c epsilon)) := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2Clamp_continuous hc hepsilon

/--
[triangularIsingRayLogDeriv2Clamp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2Clamp_eq_eq
  {beta J c epsilon p q : Real}
-- given
  (hc : 0 < c)
  (hepsilon : 0 < epsilon)
  (hsize : epsilon ^ 2 <= p ^ 2 + q ^ 2)
  (hlower : c * (p ^ 2 + q ^ 2) <= triangularIsingSymbol beta beta (beta * J) p q) :
-- imply
  triangularIsingRayLogDeriv2Clamp beta J c epsilon p q = triangularIsingRayLogDeriv2 J beta p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2Clamp_eq hc hepsilon hsize hlower

/--
[triangularIsingRayLogDeriv2_inner_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2_inner_continuousOn_eq
  {beta J epsilon : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ContinuousOn (fun x : Real => ∫ y in x..(2 * x), triangularIsingRayLogDeriv2 J beta x y) (Set.Icc epsilon 1) := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2_inner_continuousOn hbeta hroot hepsilon

/--
[triangularIsingCriticalInverseSymbol_inner_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingCriticalInverseSymbol_inner_intervalIntegrable_eq
  {beta J x : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hx : 0 < x)
  (hxOne : x <= 1) :
-- imply
  IntervalIntegrable (fun y : Real => triangularIsingCriticalInverseSymbol beta J x y) volume x (2 * x) := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalInverseSymbol_inner_intervalIntegrable hbeta hroot hx hxOne

/--
[triangularIsingRayLogDeriv2_inner_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2_inner_intervalIntegrable_eq
  {beta J x : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hx : 0 < x)
  (hxOne : x <= 1) :
-- imply
  IntervalIntegrable (fun y : Real => triangularIsingRayLogDeriv2 J beta x y) volume x (2 * x) := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2_inner_intervalIntegrable hbeta hroot hx hxOne

/--
[triangularIsingRayLogDeriv2_wedge_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2_wedge_lower_eq
  {beta J epsilon a C : Real}
-- given
  (hbeta : 0 < beta)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
  (hC : 0 <= C)
  (hlower : ∀ p q : Real, |p| <= Real.pi -> |q| <= Real.pi -> (p ≠ 0 ∨ q ≠ 0) -> a * triangularIsingCriticalInverseSymbol beta J p q - C <= triangularIsingRayLogDeriv2 J beta p q)
  (hepsilon : 0 < epsilon)
  (hepsilonOne : epsilon <= 1) :
-- imply
  a * (∫ x in epsilon..1, ∫ y in x..(2 * x), triangularIsingCriticalInverseSymbol beta J x y) - C <= ∫ x in epsilon..1, ∫ y in x..(2 * x), triangularIsingRayLogDeriv2 J beta x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2_wedge_lower hbeta hroot hC hlower hepsilon hepsilonOne

/--
[triangularIsingRayLogDeriv2_wedge_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingRayLogDeriv2_wedge_tendsto_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  Tendsto (fun n : Nat => ∫ x in Real.exp (-(n : Real))..1, ∫ y in x..(2 * x), triangularIsingRayLogDeriv2 J beta x y) atTop atTop := by
-- proof
  apply StatMech.FrontierA.triangularIsingRayLogDeriv2_wedge_tendsto hbeta hJ hroot

/--
[triangularIsingFreeEnergySecondWedge_tendsto_atBot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalSecond.lean)
-/
@[path]
private lemma triangularIsingFreeEnergySecondWedge_tendsto_atBot_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  Tendsto (fun n : Nat => -(1 / (8 * Real.pi ^ 2)) * (∫ x in Real.exp (-(n : Real))..1, ∫ y in x..(2 * x), triangularIsingRayLogDeriv2 J beta x y)) atTop atBot := by
-- proof
  apply StatMech.FrontierA.triangularIsingFreeEnergySecondWedge_tendsto_atBot hbeta hJ hroot


-- created on 2026-10-23
