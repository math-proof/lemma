/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

theorem rlcConnectorFullRectangleBoxInclusion_injective (scale : Nat) :
    Function.Injective (rlcConnectorFullRectangleBoxInclusion scale) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : FK.boxVerts 2 (2 * scale) => (z : Site 2)) hxy

theorem rlcConnectorFullRectangleBoxInclusion_adjMatch (scale : Nat) :
    FK.ocd_AdjMatch (rlcConnectorFullRectangleGraph scale)
      (FK.boxGraph 2 (2 * scale))
      (rlcConnectorFullRectangleBoxInclusion scale) := by
  intro x y
  rfl


end
end StatMech.FrontierD
