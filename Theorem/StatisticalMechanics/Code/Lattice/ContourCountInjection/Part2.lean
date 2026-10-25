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
import Def.StatisticalMechanics.Code.Lattice.ContourCountInjection
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin crosses crosses_mk crossEdges
  contourLen connClusterFamily pcc_mem_connClusterFamily clusterFamily_subset_box
  bondFinsetTouch adj_of_mem_bondFinsetTouch bondPairsTouch boxFinset mem_boxFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem connFamily_fixedLen_card_eq_realised (n ℓ : ℕ) :
    ((connClusterFamily (d := d) n).filter
        (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      = (realisedContours d n ℓ).card := by
  classical
  unfold realisedContours
  rw [Finset.card_image_of_injOn]
  
  refine (connBoxCluster_crossEdges_injOn (n := n)).mono ?_
  intro K hK
  rw [Finset.mem_coe, Finset.mem_filter] at hK
  exact Finset.mem_coe.mpr hK.1


theorem connFamily_fixedLen_card_le_peierls (n ℓ : ℕ) (h : ContourSubsetCountBound d n ℓ) :
    ((connClusterFamily (d := d) n).filter
        (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      ≤ ℓ * (2 * d) ^ ℓ := by
  rw [connFamily_fixedLen_card_eq_realised]
  exact h


theorem singleton_origin_isConnectedCluster :
    IsConnectedCluster ({origin d} : Finset (Site d)) := by
  refine ⟨Finset.mem_singleton_self _, ?_⟩
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact SimpleGraph.Reachable.refl _

end Lattice
end StatMech
