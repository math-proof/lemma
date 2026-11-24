module
public import Theorem.StatisticalMechanics.Code.SLE.FKIsingInterfaceConvergenceReduction
public import Abbrev.StatisticalMechanics.Code.SLE.CapacityParametrizedCurveSpace
open Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityParametrizedCurveSpace.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

noncomputable instance capacityParametrizedPlaneCurveMeasurableSpace :
    MeasurableSpace CapacityParametrizedPlaneCurve :=
  borel _

instance capacityParametrizedPlaneCurveBorelSpace :
    BorelSpace CapacityParametrizedPlaneCurve :=
  ⟨rfl⟩


end StatMech.SLE
