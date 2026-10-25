/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Instance.StatisticalMechanics.Code.Lattice.PlanarTopology.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem card_dual_circuits_le_pow (n : ℕ) (v : Site 2) :
    (dualLattice.finsetWalkLength n v v).card ≤ 4 ^ n := by
  have h : (dualLattice.finsetWalkLength n v v).card ≤ (2 * 2) ^ n :=
    card_circuits_le_pow 2 n v
  simpa using h


end Lattice
end StatMech
