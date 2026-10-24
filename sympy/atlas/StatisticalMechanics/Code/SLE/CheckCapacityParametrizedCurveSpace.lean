/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CheckCapacityParametrizedCurveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.SLE.CapacityParametrizedCurveSpace

#synth PolishSpace StatMech.SLE.CapacityParametrizedPlaneCurve
#synth BorelSpace StatMech.SLE.CapacityParametrizedPlaneCurve

#print axioms StatMech.SLE.capacityParametrizedCurveLaws_tendsto_of_tight_of_uniqueCriterion
