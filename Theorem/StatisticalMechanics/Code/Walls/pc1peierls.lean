/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Walls.pc1peierls
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pc1_axisWalks_card_le (d ℓ : ℕ) :
    (pc1_axisWalks d ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
  unfold pc1_axisWalks
  calc ((axisAnchorPool d ℓ).sigma
          (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card
      ≤ (axisAnchorPool d ℓ).card * (2 * d) ^ ℓ := card_circuits_based_in_le_pow d _ ℓ
    _ ≤ ℓ * (2 * d) ^ ℓ := Nat.mul_le_mul_right _ (axisAnchorPool_card_le d ℓ)


end Lattice
end StatMech
