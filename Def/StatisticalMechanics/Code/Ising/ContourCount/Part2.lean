/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Ising.ContourCount
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crosses crosses_mk crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin IsConnectedCluster pcc_mem_connClusterFamily
  clusterFamily_subset_box clusterFamily mem_boxFinset origin_mem_box)

attribute [local instance] Classical.propDecidable


variable {d : ℕ}


def ContourWalkRealisation (d n ℓ : ℕ) : Prop :=
  ∃ anchors : Finset (Site d), anchors.card ≤ ℓ ∧
    realisedContours d n ℓ ⊆ walkEdgeSets (hypercubicLattice d) anchors ℓ


end Lattice
end StatMech
