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
import Def.StatisticalMechanics.Code.Ising.ContourCount
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crosses crosses_mk crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin IsConnectedCluster pcc_mem_connClusterFamily
  clusterFamily_subset_box clusterFamily mem_boxFinset origin_mem_box)

attribute [local instance] Classical.propDecidable


section Engine

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [SimpleGraph.LocallyFinite G]


theorem card_walkEdgeSets_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (B : Finset V) (ℓ : ℕ) :
    (walkEdgeSets G B ℓ).card ≤ B.card * D ^ ℓ :=
  le_trans Finset.card_image_le (card_circuits_based_in_le G hD B ℓ)

end Engine

variable {d : ℕ}


theorem card_walkEdgeSets_le_pow (B : Finset (Site d)) (ℓ : ℕ) :
    (walkEdgeSets (hypercubicLattice d) B ℓ).card ≤ B.card * (2 * d) ^ ℓ :=
  card_walkEdgeSets_le (hypercubicLattice d) (degree_le d) B ℓ


end Lattice
end StatMech
