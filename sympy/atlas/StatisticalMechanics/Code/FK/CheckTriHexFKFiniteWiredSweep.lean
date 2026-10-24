/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CheckTriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep

open StatMech.FK.PeriodicPlanar

#print axioms triHexFK_finiteWiredBoundaryReachRatio_eq
#print axioms triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous
#print axioms TriHexFiniteWiredLevel.starBoundaryReachRatio_eq_triangle
#print axioms triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous
#print axioms hexagonalGraph_adj_triHexPlanarCellTerminal
#print axioms triangularGraph_adj_triHexPlanarCellTerminal
#print axioms triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous
#print axioms triHexPlanarFiniteWiredBoundaryReach_tendsto_iff_homogeneous
