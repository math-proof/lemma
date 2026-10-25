/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.PressureFull
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume
open Finset Filter Topology


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def psv_Bdry (d n : ℕ) : Finset (Site d) :=
  (vertexBoundary_finite d (n + 1)).toFinset

end Ising
end StatMech
