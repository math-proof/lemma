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
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crosses crosses_mk crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin IsConnectedCluster pcc_mem_connClusterFamily
  clusterFamily_subset_box clusterFamily mem_boxFinset origin_mem_box)

attribute [local instance] Classical.propDecidable


section Engine

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [SimpleGraph.LocallyFinite G]


noncomputable def walkEdgeSets (B : Finset V) (ℓ : ℕ) : Finset (Finset (Sym2 V)) :=
  (B.sigma (fun v => G.finsetWalkLength ℓ v v)).image (fun p => p.2.edges.toFinset)


end Engine
end Lattice
end StatMech
