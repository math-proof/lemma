/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice
open Set Finset


namespace StatMech

namespace Lattice

def hypercubicLattice (d : ℕ) : SimpleGraph (Site d) where
  Adj := NearestNeighbour d
  symm := nearestNeighbour_symm d
  loopless := nearestNeighbour_irrefl d

end Lattice
end StatMech
