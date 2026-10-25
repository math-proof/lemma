/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation.Part2


namespace StatMech.FrontierD

noncomputable section

structure SixVertexAtMostTwoCycleFamily (T : EvenTorus) where
  count : Nat
  count_le_two : count <= 2
  cycle : Fin count -> SixVertexDirectedSimpleCycle T
  tail_disjoint : forall i j, i != j -> forall a b,
    ((cycle i).edge a).tail != ((cycle j).edge b).tail

end
end StatMech.FrontierD
