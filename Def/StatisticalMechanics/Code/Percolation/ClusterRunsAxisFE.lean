/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def craf_AxisRoutingPremise (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  Connected d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x (hrHD_rayPt j 1) ∧
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) x
      (hrHD_rayPt j 1) ∧
    (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) x).Infinite


end Percolation
end StatMech
