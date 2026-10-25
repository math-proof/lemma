/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation.Part2


namespace StatMech.FrontierD

noncomputable section

def SixVertexAtMostTwoCycleFamily.horizontalFlow
    {T : EvenTorus} (family : SixVertexAtMostTwoCycleFamily T)
    (v : T.Vertex) : Int :=
  ∑ i, (family.cycle i).horizontalFlow v

def SixVertexAtMostTwoCycleFamily.verticalFlow
    {T : EvenTorus} (family : SixVertexAtMostTwoCycleFamily T)
    (v : T.Vertex) : Int :=
  ∑ i, (family.cycle i).verticalFlow v

def SixVertexAtMostTwoCycleFamily.empty (T : EvenTorus) :
    SixVertexAtMostTwoCycleFamily T where
  count := 0
  count_le_two := by omega
  cycle := fun i => Fin.elim0 i
  tail_disjoint := by
    intro i
    exact Fin.elim0 i


def sixVertexPairAtMostTwoCycleRelated
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T) : Prop :=
  exists family : SixVertexAtMostTwoCycleFamily T, exists sign : Bool,
    And
      (sixVertexPairUnionHorizontalDelta source target =
        (fun v => if sign then family.horizontalFlow v
          else -family.horizontalFlow v))
      (sixVertexPairUnionVerticalDelta source target =
        (fun v => if sign then family.verticalFlow v
          else -family.verticalFlow v))


def sixVertexPairAtMostTwoCycleFineRelated
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T) : Prop :=
  sixVertexPairAtMostTwoCycleRelated source target /\
    sixVertexHorizontalPairBoundedFineRowProfile
        (source.1.horizontal, source.2.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (target.1.horizontal, target.2.horizontal)

end
end StatMech.FrontierD
