/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexReflectOptionalHorizontalCompletionProfile
    {T : EvenTorus} :
    Option (SixVertexHorizontalCompletionProfile T) ->
      Option (SixVertexHorizontalCompletionProfile T)
  | none => none
  | some profile => some (sixVertexReflectHorizontalCompletionProfile profile)


def sixVertexHorizontalComplementSector
    (T : EvenTorus) (sector : Fin (T.width + 1)) : Fin (T.width + 1) :=
  ⟨T.width - sector.val, by omega⟩

end
end StatMech.FrontierD
