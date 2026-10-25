import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPhaseCollapse
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[measure_eq_of_clopenDom_coordinate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPhaseCollapse.lean)
-/
@[path]
private lemma measure_eq_of_clopenDom_coordinate_eq_eq
  {d : Nat}
  [Countable E]
  {mu nu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (hdom : mu ≼c nu)
  (hmarg : ∀ e : E, mu.real {omega | omega e = true} = nu.real {omega | omega e = true}) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierB.measure_eq_of_clopenDom_coordinate_eq mu nu hdom hmarg

/--
[integral_spin_eq_two_mul_spinUp_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPhaseCollapse.lean)
-/
@[path]
private lemma integral_spin_eq_two_mul_spinUp_sub_one_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  {x : Site d} :
-- imply
  (∫ omega, spin omega x ∂mu) = 2 * mu.real {omega | omega x = true} - 1 := by
-- proof
  apply StatMech.FrontierB.integral_spin_eq_two_mul_spinUp_sub_one mu x

/--
[minusMeasure_spinUp_eq_one_sub_plusMeasure_spinUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPhaseCollapse.lean)
-/
@[path]
private lemma minusMeasure_spinUp_eq_one_sub_plusMeasure_spinUp_eq
  {d : Nat}
  {n : Nat}
  {beta : Real}
  {x : Site d} :
-- imply
  (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} = 1 - (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} := by
-- proof
  apply StatMech.FrontierB.minusMeasure_spinUp_eq_one_sub_plusMeasure_spinUp n beta x

/--
[minusState_spinUp_eq_one_sub_plusState_spinUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPhaseCollapse.lean)
-/
@[path]
private lemma minusState_spinUp_eq_one_sub_plusState_spinUp_eq
  {d : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (minusState d beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} = 1 - (plusState d beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} := by
-- proof
  apply StatMech.FrontierB.minusState_spinUp_eq_one_sub_plusState_spinUp beta hbeta x

/--
[plusState_spinUp_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPhaseCollapse.lean)
-/
@[path]
private lemma plusState_spinUp_eq_origin_eq
  {d : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (plusState d beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega x = true} = (plusState d beta 0 : Measure (ConfigSpace (Site d))).real {omega | omega (Percolation.origin d) = true} := by
-- proof
  apply StatMech.FrontierB.plusState_spinUp_eq_origin beta hbeta x

/--
[plusState_eq_minusState_of_magnetization_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPhaseCollapse.lean)
-/
@[path]
private lemma plusState_eq_minusState_of_magnetization_eq_zero_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 <= beta)
  (hmag : magnetization d beta = 0) :
-- imply
  (plusState d beta 0 : Measure (ConfigSpace (Site d))) = (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.plusState_eq_minusState_of_magnetization_eq_zero beta hbeta hmag


-- created on 2026-10-23
