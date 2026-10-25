/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccstepopen
import Theorem.StatisticalMechanics.Code.Walls.bc_wiringforcesopen
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcededgeopen
open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc2_IsLatticeWiring (W : Finset (Sym2 (Site d))) : Prop :=
  ∀ u v : Site d, s(u, v) ∈ W → (hypercubicLattice d).Adj u v


end Walls
end StatMech
