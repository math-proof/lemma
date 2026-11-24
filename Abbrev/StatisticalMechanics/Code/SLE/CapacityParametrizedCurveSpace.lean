module
public import Theorem.StatisticalMechanics.Code.SLE.FKIsingInterfaceConvergenceReduction
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

abbrev CapacityParametrizedPlaneCurve := C(NNReal, Complex)

end StatMech.SLE
