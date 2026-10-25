/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc4_core
import Theorem.StatisticalMechanics.Code.Walls.bc5_barrierblocks.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc5_core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc5_BoxCorridorRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ),
      (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      ((cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite ∧
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite ∧
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite) ∧
      bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃


end Walls
end StatMech
