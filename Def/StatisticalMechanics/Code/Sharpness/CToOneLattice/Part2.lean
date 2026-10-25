/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Instance.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part2
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


def sctBoxInLarger (d n m : ℕ) (z : sctBox d m) : Prop := z.1 ∈ box d n

end Sharpness
end StatMech
