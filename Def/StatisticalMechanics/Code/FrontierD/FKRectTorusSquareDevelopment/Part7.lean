/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part6


namespace StatMech.FrontierD

noncomputable section

def fkRectSquareRepresentativeVertex (R : FKRectTorus) (z : Int × Int) :
    R.Vertex :=
  let p := fkRectSquareUndevelopPoint z
  (⟨p.1.natMod R.width, Int.natMod_lt (ne_of_gt R.width_pos)⟩,
    ⟨p.2.natMod R.height, Int.natMod_lt (ne_of_gt R.height_pos)⟩)


def fkRectIntModFin {N : Nat} (hN : 0 < N) (z : Int) : Fin N :=
  ⟨z.natMod N, Int.natMod_lt (ne_of_gt hN)⟩

end
end StatMech.FrontierD
