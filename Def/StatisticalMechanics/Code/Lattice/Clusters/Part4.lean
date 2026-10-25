/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Clusters.Part3
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


def cluster (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Set (Site d) :=
  {y | Connected d ω x y}

end Lattice
end StatMech
