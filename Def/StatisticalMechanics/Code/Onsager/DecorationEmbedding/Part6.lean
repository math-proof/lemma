/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Structure.StatisticalMechanics.Code.Onsager.DecorationEmbedding


namespace StatMech.Onsager

def ons_decMicroVertex (L : ℕ) (z : ons_DecMicroPoint L) :
    ZMod (8 * L) × ZMod (8 * L) :=
  ((8 * z.cell.1.val + z.offsetX.val : ℕ),
    (8 * z.cell.2.val + z.offsetY.val : ℕ))

end StatMech.Onsager
