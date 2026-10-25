/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part4
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


@[simp] theorem pfdOpenPlanar_imageGraph (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    imageGraph (pfdOpenPlanar P K hKP) = jei_pushGraph P K := by
  ext a b
  simp only [imageGraph_adj, jei_pushGraph_adj, pfdOpenPlanar]

@[simp] theorem pfdOpenPlanar_graph (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    (pfdOpenPlanar P K hKP).G = K := rfl


theorem pfd_numFaceComponents_eq_faceCount (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
  have h := kwg_card_face_eq_faceCount (pfdOpenPlanar P K hKP)
  simpa only [kwg_Face, pfdOpenPlanar_imageGraph, pfdOpenPlanar_graph] using h


theorem pfd_numDualClusters_eq_faceCount (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    Nat.card (pfdClosedDual P K).ConnectedComponent = faceCount K := by
  rw [pfd_numDualClusters_eq_faceComponents P K hKP,
    pfd_numFaceComponents_eq_faceCount P K hKP]


theorem pfd_clusterEuler (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) :
    Nat.card P.V + Nat.card (pfdClosedDual P K).ConnectedComponent =
      K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 := by
  rw [pfd_numDualClusters_eq_faceCount P K hKP]
  exact euler_relation K


end BeffaraDC
end StatMech
