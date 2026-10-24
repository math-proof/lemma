import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.CapacityParametrizedCurveSpace
open Filter MeasureTheory Topology StatMech StatMech.SLE


/--
[capacityParametrizedCurveLaws_tendsto_of_tight_of_uniqueCriterion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityParametrizedCurveSpace.lean)
-/
@[path]
private lemma capacityParametrizedCurveLaws_tendsto_of_tight_of_uniqueCriterion_eq
  {target : ProbabilityMeasure CapacityParametrizedPlaneCurve}
-- given
  (laws : Nat -> ProbabilityMeasure CapacityParametrizedPlaneCurve)
  (criterion : ProbabilityMeasure CapacityParametrizedPlaneCurve -> Prop)
  (hTight : IsTightMeasureSet {mu : Measure CapacityParametrizedPlaneCurve | exists n, mu = (laws n : Measure CapacityParametrizedPlaneCurve)})
  (hlimits : forall (phi psi : Nat -> Nat) (limit : ProbabilityMeasure CapacityParametrizedPlaneCurve), StrictMono phi -> StrictMono psi -> Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) -> criterion limit)
  (hunique : forall limit, criterion limit -> limit = target) :
-- imply
  Tendsto laws atTop (nhds target) := by
-- proof
  apply StatMech.SLE.capacityParametrizedCurveLaws_tendsto_of_tight_of_uniqueCriterion laws target criterion hTight hlimits hunique


-- created on 2026-10-23
