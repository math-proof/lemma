/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterDomination.Part2
open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}


def clusterSizeLargeEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ¬ ∃ hfin : (cluster d ω (origin d)).Finite,
      hfin.toFinset.card ≤ (boxFinset d (n - 1)).card}


end BeffaraDC
end StatMech
