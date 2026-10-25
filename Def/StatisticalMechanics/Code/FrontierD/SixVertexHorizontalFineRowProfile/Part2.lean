/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairBoundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    SixVertexHorizontalBoundedFineRowProfile T :=
  fun j =>
    (⟨sixVertexHorizontalPairRowNontransitionProfile horizontal j,
      by
        unfold sixVertexHorizontalPairRowNontransitionProfile
        have hfirst := sixVertexHorizontalRowNontransitionCount_le_width
          horizontal.1 j
        have hsecond := sixVertexHorizontalRowNontransitionCount_le_width
          horizontal.2 j
        omega⟩,
     ⟨sixVertexHorizontalPairRowZeroProfile horizontal j,
      by
        unfold sixVertexHorizontalPairRowZeroProfile
        have hfirst := sixVertexHorizontalRowZeroCount_le_width horizontal.1 j
        have hsecond := sixVertexHorizontalRowZeroCount_le_width horizontal.2 j
        omega⟩)

end
end StatMech.FrontierD
