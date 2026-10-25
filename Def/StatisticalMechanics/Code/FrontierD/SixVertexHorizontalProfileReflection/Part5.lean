/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalFalseForcedColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  Finset.univ.filter fun i =>
    sixVertexHorizontalColumnSeamAllowed horizontal i false ∧
      Not (sixVertexHorizontalColumnSeamAllowed horizontal i true)

end
end StatMech.FrontierD
