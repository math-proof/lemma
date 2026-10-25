/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def caa_RunsAlongCandidates (ω : ConfigSpace (Sym2 (Site d))) (x : Fin 3 → Site d)
    (S : Fin 3 → Finset (Fin d)) : Prop :=
  (∀ i : Fin 3, ∀ j ∈ S i, crr_ClusterRunsAlongAxis ω (x i) j) ∧
    (∀ s : Finset (Fin 3), s.card ≤ (s.biUnion S).card)


end Percolation
end StatMech
