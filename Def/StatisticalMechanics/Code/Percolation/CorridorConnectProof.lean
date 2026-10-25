/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Probability.MengerSplice.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConnectProof
open MeasureTheory Set SimpleGraph
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Combinatorics


namespace StatMech

namespace Percolation

variable {d : ℕ}


def cnp_ClusterMeetsCorridor (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ))) ∧
  (cluster d (removeSite 0 ω) x).Infinite


end Percolation
end StatMech
