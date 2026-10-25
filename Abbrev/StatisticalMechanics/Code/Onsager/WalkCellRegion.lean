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
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellRegion


namespace StatMech.Onsager.WalkCellRegion

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.InsideConnected StatMech.Onsager.JedBridge


section Walk

variable {m : ℕ}

noncomputable abbrev walkP (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    PlanarZ2Subgraph := walkSubgraph d hclosed hsimple

noncomputable abbrev walkRegionGraph (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    SimpleGraph (Site 2) := whb_faceRegion (imageGraph (walkP d hclosed hsimple))


end Walk
end StatMech.Onsager.WalkCellRegion
