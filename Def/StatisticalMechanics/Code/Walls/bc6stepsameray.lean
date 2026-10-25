/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6stepsameray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc6_clusterNbhd (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) : Set (Site d) :=
  ⋃ (t : ℕ) (_ : 1 ≤ t ∧ t ≤ L), cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ))


end Walls
end StatMech
