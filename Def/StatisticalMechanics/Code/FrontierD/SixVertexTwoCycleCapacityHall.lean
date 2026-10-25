/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPairFineUnionKey
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    SixVertexPairFineUnionKey T where
  fine := sixVertexHorizontalPairBoundedFineRowProfile
    (pair.1.horizontal, pair.2.horizontal)
  horizontal v := ⟨(pair.1.horizontal v).toNat +
      (pair.2.horizontal v).toNat, by
    cases pair.1.horizontal v <;> cases pair.2.horizontal v <;> decide⟩
  vertical v := ⟨(pair.1.vertical v).toNat +
      (pair.2.vertical v).toNat, by
    cases pair.1.vertical v <;> cases pair.2.vertical v <;> decide⟩


def SixVertexPairFineUnionKeyTwoCycleRelated
    {T : EvenTorus}
    (source target : SixVertexPairFineUnionKey T) : Prop :=
  source.fine = target.fine ∧
    exists family : SixVertexAtMostTwoCycleFamily T, exists sign : Bool,
      ((fun v => (target.horizontal v).val -
          (source.horizontal v).val : T.Vertex -> Int) =
        fun v => if sign then family.horizontalFlow v
          else -family.horizontalFlow v) ∧
      ((fun v => (target.vertical v).val -
          (source.vertical v).val : T.Vertex -> Int) =
        fun v => if sign then family.verticalFlow v
          else -family.verticalFlow v)

end
end StatMech.FrontierD
