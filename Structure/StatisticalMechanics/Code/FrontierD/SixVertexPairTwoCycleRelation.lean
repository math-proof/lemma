/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation


namespace StatMech.FrontierD

noncomputable section

structure SixVertexDirectedSimpleCycle (T : EvenTorus) where
  length : Nat
  length_pos : 0 < length
  edge : Fin length -> SixVertexDirectedTorusEdge T
  head_eq_next_tail : forall i,
    (edge i).head =
      (edge (finitePeriodicSucc length_pos i)).tail
  tail_injective : Function.Injective (fun i => (edge i).tail)
  physical_injective : Function.Injective (fun i => (edge i).physical)

end
end StatMech.FrontierD
