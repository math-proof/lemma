/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part7


namespace StatMech.Onsager

def ons_decInteriorOffsets : Finset (Fin 8 × Fin 8) :=
  {(7, 4), (0, 4), (1, 4), (4, 7), (4, 0), (4, 1),
    (6, 5), (6, 6), (5, 6), (3, 6), (2, 6), (2, 5),
    (2, 3), (2, 2), (3, 2)}

end StatMech.Onsager
