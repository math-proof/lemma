/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part6
import Theorem.StatisticalMechanics.Code.Onsager.EdgeUnique
import Theorem.StatisticalMechanics.Code.Onsager.GeneralInterior


namespace StatMech.Onsager.GeneralInterior

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Euc

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.InteriorCells
  StatMech.Onsager.WalkCellRegion StatMech.Onsager.CellCount
  StatMech.Onsager.CellEuler StatMech.Onsager.CellEulerFaithful

variable {n : ℕ} [NeZero n]


section WalkRegion

variable {m : ℕ}


noncomputable def oddComponent (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (c : interiorCells d hclosed) :
    (walkRegionGraph d hclosed hsimple).ConnectedComponent :=
  (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace c.1)


end WalkRegion
end StatMech.Onsager.GeneralInterior
