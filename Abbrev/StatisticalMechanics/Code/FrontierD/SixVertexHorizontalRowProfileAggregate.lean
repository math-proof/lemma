/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalPairRowBigradeFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :=
  {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T //
    sixVertexHorizontalPairBigrade horizontal = grade /\
      sixVertexHorizontalPairRowZeroProfile horizontal = rowProfile}

end
end StatMech.FrontierD
