import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardShearPhaseHomotopy.Part2
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.consecutive_turn_ne_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean)
-/
@[path]
private lemma consecutive_turn_ne_pi_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {k : Fin n} :
-- imply
  (Complex.arg (polygon.edgeVector (k + 1)) : Real.Angle) - (Complex.arg (polygon.edgeVector k) : Real.Angle) ≠ (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.consecutive_turn_ne_pi polygon k

/--
[kwDoubleShearLinearEquiv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean)
-/
@[path]
private lemma kwDoubleShearLinearEquiv_zero_eq
  {tx ty : ℝ}
  {z : ℂ} :
-- imply
  kwDoubleShearLinearEquiv tx ty 0 z = z := by
-- proof
  apply StatMech.FrontierA.kwDoubleShearLinearEquiv_zero tx ty z

/--
[kwDoubleShearLinearEquiv_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean)
-/
@[path]
private lemma kwDoubleShearLinearEquiv_one_eq
  {tx ty : ℝ}
  {z : ℂ} :
-- imply
  kwDoubleShearLinearEquiv tx ty 1 z = kwShearY ty (kwShearX tx z) := by
-- proof
  apply StatMech.FrontierA.kwDoubleShearLinearEquiv_one tx ty z

/--
[continuous_kwDoubleShearLinearEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean)
-/
@[path]
private lemma continuous_kwDoubleShearLinearEquiv_apply_eq
  {tx ty : ℝ}
  {z : ℂ} :
-- imply
  Continuous (fun t : ℝ ↦ kwDoubleShearLinearEquiv tx ty t z) := by
-- proof
  apply StatMech.FrontierA.continuous_kwDoubleShearLinearEquiv_apply tx ty z

/--
[continuousOn_kwDoubleShear_edge_arg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean)
-/
@[path]
private lemma continuousOn_kwDoubleShear_edge_arg_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {tx ty : ℝ}
  {k : Fin n} :
-- imply
  ContinuousOn (fun t : ℝ ↦ (Complex.arg (kwDoubleShearLinearEquiv tx ty t (polygon.edgeVector k)) : Real.Angle)) (Icc 0 1) := by
-- proof
  apply StatMech.FrontierA.continuousOn_kwDoubleShear_edge_arg polygon tx ty k

/--
[KWFiniteSimplePolygon.phaseCycle_mapDoubleShear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean)
-/
@[path]
private lemma phaseCycle_mapDoubleShear_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {tx ty : ℝ} :
-- imply
  kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle (polygon.mapLinearEquiv (kwDoubleShearLinearEquiv tx ty 1)).edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.phaseCycle_mapDoubleShear polygon tx ty


-- created on 2026-10-23
