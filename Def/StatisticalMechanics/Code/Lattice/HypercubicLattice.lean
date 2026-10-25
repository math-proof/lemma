/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Lattice.HypercubicLattice
open Set Finset


namespace StatMech

namespace Lattice

def NearestNeighbour (d : ℕ) (x y : Site d) : Prop :=
  (∑ i, (x i - y i).natAbs) = 1

end Lattice
end StatMech
