/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Theorem.StatisticalMechanics.Code.Walls.bc3_distinctwitnessclusters
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_OriginCutLeavesInfinite (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ x : Site d, (cluster d ω x).Infinite → (0 : Site d) ∈ cluster d ω x →
    ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite


end Walls
end StatMech
