/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Instance.StatisticalMechanics.Code.Sharpness.CToOneLattice
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


def sctBoxGraph (d n : ℕ) : SimpleGraph (sctBox d n) :=
  (hypercubicLattice d).induce (box d n)

end Sharpness
end StatMech
