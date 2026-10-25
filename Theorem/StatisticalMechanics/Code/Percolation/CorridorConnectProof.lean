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
open MeasureTheory Set SimpleGraph
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Combinatorics


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem cnp_mouth_connected_corridorCell (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L + 1) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) :=
  mco_corridorVert_connected ω j (L + 1) m hm1 hmL


theorem cnp_removeSite_le (ω : ConfigSpace (Sym2 (Site d))) (z : Site d) :
    removeSite z ω ≤ ω := by
  intro e
  by_cases h : z ∈ e
  · rw [removeSite_apply_of_mem h]; exact bot_le
  · rw [removeSite_apply_of_notMem h]


end Percolation
end StatMech
