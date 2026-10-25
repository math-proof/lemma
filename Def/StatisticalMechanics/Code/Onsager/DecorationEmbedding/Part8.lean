/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part6


namespace StatMech.Onsager

def ons_decMicroCorridorEdge (L : ℕ) (z : ons_DecMicroPoint L) :
    Sym2 (ons_Dart L) :=
  match z.offsetX.val, z.offsetY.val with
  | 7, 4 => s((z.cell, 0), (ons_dirStep L 0 z.cell, 2))
  | 0, 4 => s((ons_dirStep L 2 z.cell, 0), (z.cell, 2))
  | 1, 4 => s((ons_dirStep L 2 z.cell, 0), (z.cell, 2))
  | 4, 7 => s((z.cell, 1), (ons_dirStep L 1 z.cell, 3))
  | 4, 0 => s((ons_dirStep L 3 z.cell, 1), (z.cell, 3))
  | 4, 1 => s((ons_dirStep L 3 z.cell, 1), (z.cell, 3))
  | 6, 5 => s((z.cell, 0), (z.cell, 1))
  | 6, 6 => s((z.cell, 0), (z.cell, 1))
  | 5, 6 => s((z.cell, 0), (z.cell, 1))
  | 3, 6 => s((z.cell, 1), (z.cell, 2))
  | 2, 6 => s((z.cell, 1), (z.cell, 2))
  | 2, 5 => s((z.cell, 1), (z.cell, 2))
  | 2, 3 => s((z.cell, 2), (z.cell, 3))
  | 2, 2 => s((z.cell, 2), (z.cell, 3))
  | 3, 2 => s((z.cell, 2), (z.cell, 3))
  | _, _ => s((z.cell, 0), (z.cell, 1))

end StatMech.Onsager
