/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerBound.Part4
import Theorem.StatisticalMechanics.Code.Onsager.InsideConnected
import Def.StatisticalMechanics.Code.Onsager.JedBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Def.StatisticalMechanics.Code.Onsager.WalkCellRegion.Part2


namespace StatMech.Onsager.WalkCellRegion

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.InsideConnected StatMech.Onsager.JedBridge


section Walk

variable {m : ℕ}

variable (d : Fin (m + 3) → Fin 4)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)


theorem lexInteriorIndex_spec :
    d (lexInteriorIndex d hclosed hsimple hreflexfree - 1) = 1 ∧
      d (lexInteriorIndex d hclosed hsimple hreflexfree) = 2 ∧
      rayParity d
        ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).1 - 1)
        ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).2 - 1) = 1 :=
  (lexmax_corner_cell_inside d hclosed hsimple hreflexfree).choose_spec


end Walk
end StatMech.Onsager.WalkCellRegion
