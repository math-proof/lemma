/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalDiagonalDeficit


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalLowerSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) : Fin (T.width + 1) :=
  ⟨middle.val - 1, by omega⟩

def sixVertexHorizontalUpperSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hlt : middle.val < T.width) : Fin (T.width + 1) :=
  ⟨middle.val + 1, by omega⟩

end
end StatMech.FrontierD
