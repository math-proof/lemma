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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathFullRectangleEmbedding.Part3
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

def fkRectWindingStoppedRectangleCenter
    (k scale blocks : Nat)
    (hwidth : 12 * scale + 2 < 2 * (k + 3))
    (hblocks : 3 <= blocks) :
    (fkRectWindingBlockVerticalFamily k scale blocks).Vertex :=
  (⟨4 * scale + 1, by
    simp only [fkRectWindingBlockVerticalFamily_width]
    omega⟩, ⟨4 * scale + 1, by
    simp only [fkRectWindingBlockVerticalFamily_height]
    nlinarith⟩)


end
end StatMech.FrontierD
