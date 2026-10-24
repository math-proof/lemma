/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CheckLebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph

#print axioms StatMech.Ising.lpReplicaCurrentRel_reflect
#print axioms StatMech.Ising.lpReplicaCurrentGraph_adj_reflect
#print axioms StatMech.Ising.lpReplicaCurrentCoupling_reflect
#print axioms StatMech.Ising.lpReplicaCurrentCoupling_nonneg
#print axioms StatMech.Ising.lpReplicaCurrentGraph_adj_left_right_iff
#print axioms StatMech.Ising.lpReplicaCurrentSeamEdge_injective
#print axioms StatMech.Ising.lpReplicaCurrentSeamEdge_mem
#print axioms StatMech.Ising.lpReplicaCurrent_reflectedMatchingCut
