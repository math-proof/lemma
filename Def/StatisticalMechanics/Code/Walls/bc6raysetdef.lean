/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc6_rayInterior (a : Fin d) (R : ℕ) : Set (Site d) :=
  {x | ∃ p : ℕ, (1 ≤ p ∧ p ≤ R) ∧ x = hrHD_rayPt a (p : ℤ)}


end Walls
end StatMech
