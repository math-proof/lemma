/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part3
open Set Finset


namespace StatMech

namespace Lattice

def vertexBoundary (d n : ℕ) : Set (Site d) := box d n \ box d (n - 1)

end Lattice
end StatMech
