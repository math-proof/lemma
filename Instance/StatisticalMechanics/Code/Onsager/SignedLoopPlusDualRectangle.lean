/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part2
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

noncomputable instance ons_plusDualFaceVertexFintype (n : Nat) :
    Fintype (ons_PlusDualFaceVertex n) :=
  Fintype.ofEquiv (ons_RectDualVertex (2 * n + 1) (2 * n + 1))
    (ons_plusDualFaceEquivRect n).symm


end
end StatMech.Onsager
