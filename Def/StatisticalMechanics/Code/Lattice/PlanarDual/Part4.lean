/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part3
open SimpleGraph


namespace StatMech

namespace Lattice

def rot90Iso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨rot90Equiv, fun {x y} => rot90_adj x y⟩

end Lattice
end StatMech
