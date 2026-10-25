/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part5
import Theorem.StatisticalMechanics.Code.Walls.rmvremovable.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


def rmv_ReflexCornerResidue : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K →
    ∀ c, ear_IsGlobalExtreme (↑K : Set (Site 2)) c → c ≠ origin 2 →
      ear_leftCell c ∈ (↑K : Set (Site 2)) → ear_downCell c ∈ (↑K : Set (Site 2)) →
      c + ![-1, -1] ∉ (↑K : Set (Site 2)) →
      ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d})


def rmv_AntiReflexCornerResidue : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K →
    ∀ b, ear_IsAntiExtreme (↑K : Set (Site 2)) b → b ≠ origin 2 →
      ear_rightCell b ∈ (↑K : Set (Site 2)) → ear_upCell b ∈ (↑K : Set (Site 2)) →
      b + ![1, 1] ∉ (↑K : Set (Site 2)) →
      ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d})


end Walls
end StatMech
