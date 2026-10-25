/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def mco_corridorVerts (j : Fin d) (L : ℕ) : Set (Site d) :=
  {y | ∃ m : ℕ, 1 ≤ m ∧ m ≤ L ∧ y = hrHD_rayPt j (m : ℤ)}


end Percolation
end StatMech
