/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

def oddRectangularPrismFaceSum (n : Nat)
    (f : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real) : Real :=
  (∑ y : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1), f ⟨0, y, z⟩) +
  (∑ y : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1),
      f ⟨Fin.last (2 * n), y, z⟩) +
  (∑ x : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1), f ⟨x, 0, z⟩) +
  (∑ x : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1),
      f ⟨x, Fin.last (2 * n), z⟩) +
  (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1), f ⟨x, y, 0⟩) +
  (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1),
      f ⟨x, y, Fin.last (2 * n)⟩)


def oddRectangularPrismFaceInteraction (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) : Real :=
  oddRectangularPrismFaceSum n (spin sigma)


end
end StatMech.FrontierA
