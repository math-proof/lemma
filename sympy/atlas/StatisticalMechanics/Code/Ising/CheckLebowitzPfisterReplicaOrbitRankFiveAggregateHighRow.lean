/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CheckLebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow

open StatMech.Ising

#print axioms
  lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
#print axioms
  lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow
#print axioms
  lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
#print axioms
  lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target
#print axioms lpReplicaOffdiagDecoratedTargetToAggregate_crossTrace
#print axioms
  lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target
#print axioms sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate
#print axioms lpReplicaAggregateResolvableHighRowRankFiveEmbedding
