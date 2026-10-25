/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin crosses crosses_mk crossEdges
  contourLen connClusterFamily pcc_mem_connClusterFamily clusterFamily_subset_box
  bondFinsetTouch adj_of_mem_bondFinsetTouch bondPairsTouch boxFinset mem_boxFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def realisedContours (d n ℓ : ℕ) : Finset (Finset (Sym2 (Site d))) :=
  ((connClusterFamily (d := d) n).filter
      (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).image
    (fun K : Finset (Site d) => crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n))


def ContourSubsetCountBound (d n ℓ : ℕ) : Prop :=
  (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ


end Lattice
end StatMech
