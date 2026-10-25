/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckMonotoneAutomatonNearestConclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
open MeasureTheory Set
open StatMech Lattice FrontierA

#check pairFiniteNearestAt_origin_measure_zero
#check pairFiniteNearestAt_measure_zero
#check pairHasFiniteNearestHighCluster_measure_zero
#check interpolatedHighPair_no_finite_nearest

#print axioms StatMech.FrontierA.pairHasFiniteNearestHighCluster_measure_zero
#print axioms StatMech.FrontierA.interpolatedHighPair_no_finite_nearest


