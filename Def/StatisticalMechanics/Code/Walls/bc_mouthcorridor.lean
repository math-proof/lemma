module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bkm_dccstepopen
open Set
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_mouthcorridor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

variable {d : ℕ}

open StatMech.Percolation


noncomputable def bc_mouthCutConfig (j : Fin d) (L : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : ConfigSpace (Sym2 (Site d)) :=
  removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)


end Walls
end StatMech
