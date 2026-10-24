/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CheckPeriodicPlanarParameterMonotonicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity

#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_real_cylinder_monotone_in_p
#print axioms
  StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p
set_option linter.style.longLine false in
#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_monotoneOn_of_cylinderApproximation
set_option linter.style.longLine false in
#print axioms StatMech.FK.PeriodicPlanar.PeriodicGraph.dualCritical_relation_of_cylinderApproximation_noCoexistence
