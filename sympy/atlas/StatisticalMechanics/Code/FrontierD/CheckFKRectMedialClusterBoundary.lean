/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckFKRectMedialClusterBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary

#print axioms StatMech.FrontierD.fkRectMedialComponentToPrimalComponent_surjective
#print axioms StatMech.FrontierD.fkRectNumClusters_le_medialLoopCount
#print axioms StatMech.FrontierD.fkRectEulerHomologyDefect_le_cycleRankInt
#print axioms StatMech.FrontierD.fkRectEulerHomologyDefect_eq_zero_of_cycleRankInt_le_one
#print axioms StatMech.FrontierD.fkRectCycleRankInt_ge_two_of_eulerHomologyDefect_eq_two
