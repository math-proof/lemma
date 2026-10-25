/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


def MengerRoutingCover (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, MengerCore ω


end DisjointPaths
end Percolation
end StatMech
