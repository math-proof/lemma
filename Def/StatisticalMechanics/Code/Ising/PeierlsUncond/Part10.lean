/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part9
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def clusterFamily (n : ℕ) : Finset (Finset (Site d)) :=
  (boxFinset d n).powerset


noncomputable def minusClusterFinset {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) : Finset (Site d) :=
  (minusCluster_glue_plus_finite τ ho).toFinset

end Ising
end StatMech
