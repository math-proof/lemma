/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityParametrizedCurveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.FKIsingInterfaceConvergenceReduction
import Instance.StatisticalMechanics.Code.SLE.CapacityParametrizedCurveSpace
open Filter MeasureTheory Topology


namespace StatMech.SLE

theorem capacityParametrizedCurveLaws_tendsto_of_tight_of_uniqueCriterion
    (laws : Nat -> ProbabilityMeasure CapacityParametrizedPlaneCurve)
    (target : ProbabilityMeasure CapacityParametrizedPlaneCurve)
    (criterion : ProbabilityMeasure CapacityParametrizedPlaneCurve -> Prop)
    (hTight : IsTightMeasureSet
      {mu : Measure CapacityParametrizedPlaneCurve |
        exists n, mu = (laws n : Measure CapacityParametrizedPlaneCurve)})
    (hlimits : forall (phi psi : Nat -> Nat)
      (limit : ProbabilityMeasure CapacityParametrizedPlaneCurve),
      StrictMono phi -> StrictMono psi ->
      Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit) ->
      criterion limit)
    (hunique : forall limit, criterion limit -> limit = target) :
    Tendsto laws atTop (nhds target) :=
  tendsto_of_tight_of_unique_subsequential_criterion
    laws target criterion hTight hlimits hunique

end StatMech.SLE
