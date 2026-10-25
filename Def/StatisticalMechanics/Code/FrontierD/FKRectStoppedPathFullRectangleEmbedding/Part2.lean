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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

def rlcConnectorFullRectangleBoxInclusion (scale : Nat) :
    RlcConnectorVertex (scale : Int) -> FK.boxVerts 2 (2 * scale) :=
  fun z => ⟨z, by
    have hzRect := z.2
    change z.1 ∈ StatMech.RSW.Box.rect
      (-2 * (scale : Int)) (2 * (scale : Int))
      (-(scale : Int)) (scale : Int) at hzRect
    rw [StatMech.RSW.Box.mem_rect] at hzRect
    rw [mem_box]
    intro i
    fin_cases i <;> simp at hzRect ⊢ <;> omega⟩

end
end StatMech.FrontierD
