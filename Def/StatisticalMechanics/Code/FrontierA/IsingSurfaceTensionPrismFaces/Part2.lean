/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

def oddRectangularPrismDobrushinSign (n : Nat) (z : Fin (2 * n + 1)) : Real :=
  if n < z.val then -1 else 1


def oddRectangularPrismDobrushinFaceInteraction (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  oddRectangularPrismFaceSum n fun v =>
    oddRectangularPrismDobrushinSign n v.z * spin sigma v


end
end StatMech.FrontierA
