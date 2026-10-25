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
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual
open SimpleGraph


namespace StatMech

namespace Lattice

def rot90Fun (x : Site 2) : Site 2 := ![- x 1, x 0]


def rot90Inv (x : Site 2) : Site 2 := ![x 1, - x 0]

end Lattice
end StatMech
