/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part10


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectVertexSquareEquiv (R : FKRectTorus) :
    R.Vertex ≃ FKRectSquareTorus R :=
  Equiv.ofBijective (fkRectVertexSquareClass R)
    ⟨fkRectVertexSquareClass_injective R,
      fkRectVertexSquareClass_surjective R⟩


end
end StatMech.FrontierD
