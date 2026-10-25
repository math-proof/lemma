/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc9core
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc12core
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc12_BoxOriginTrifurcation (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, IsCanonicalTrifurcation d ω 0


end Walls
end StatMech
