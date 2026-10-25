/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part2


namespace StatMech.Onsager

open BaseCase

def onsAnisotropicVertexEmbed (width height : ℕ)
    (p : Fin width × Fin height) :
    ZMod (width * height) × ZMod (width * height) :=
  ((height * p.1.val : ℕ), (width * p.2.val : ℕ))

end StatMech.Onsager
