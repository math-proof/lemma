/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickPlanar.Part2
import Def.StatisticalMechanics.Code.FK.TriHexBrickFaces
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls


theorem hexagonalBrickFaces_adj (t : Site 2) :
    (hypercubicLattice 2).Adj
      (hexagonalBrickFaceLeft t) (hexagonalBrickFaceRight t) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight]


theorem hexagonalBrickFaces_shared (t : Site 2) :
    sharedPrimalEdge (hexagonalBrickFaceLeft t)
        (hexagonalBrickFaceRight t) =
      s(hexagonalBrickVertex (t + hexagonalStep 1, true),
        hexagonalBrickVertex (t - hexagonalStep 1, false)) := by
  rw [show hexagonalBrickFaceRight t =
      hexagonalBrickFaceLeft t + ![1, 0] by
        ext k
        fin_cases k <;>
          simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight] <;> omega]
  unfold hexagonalBrickFaceLeft
  rw [show (![2 * t 0 + t 1 - 2, -t 1] : Site 2) + ![1, 0] =
      ![(2 * t 0 + t 1 - 2) + 1, -t 1] by
        ext k
        fin_cases k <;> simp]
  rw [sharedPrimalEdge_right]
  apply Sym2.eq_iff.mpr
  left
  constructor <;> ext k <;> fin_cases k <;>
    simp [faceCorner10, faceCorner11, hexagonalBrickVertex, hexagonalStep] <;>
    omega


theorem hexagonalBrickFaces_middle_not_adj (t : Site 2) :
    ¬ hexagonalGraph.Adj
      (t + hexagonalStep 1, true) (t - hexagonalStep 1, false) := by
  rw [hexagonalGraph_adj]
  intro hadj
  rcases hadj with hbad | h
  · simp at hbad
  rcases h with ⟨_, _, i, hi⟩
  fin_cases i <;>
    simp [hexagonalStep, funext_iff] at hi <;> omega


theorem triHexPlanarFiniteStar_middle_not_mem_imageGraph
    (n : Nat) (t : Site 2) :
    sharedPrimalEdge (hexagonalBrickFaceLeft t)
        (hexagonalBrickFaceRight t) ∉
      (imageGraph (triHexPlanarFiniteStarPlanar n)).edgeSet := by
  rw [hexagonalBrickFaces_shared, SimpleGraph.mem_edgeSet, imageGraph_adj]
  rintro ⟨u, v, huv, hu, hv⟩
  have hamb := triHexPlanarFiniteStarGraph_adj_hexagonal n huv
  have hu' : triHexPlanarFiniteStarVertexEmbedding n u =
      (t + hexagonalStep 1, true) := by
    apply hexagonalBrickVertex_injective
    exact hu
  have hv' : triHexPlanarFiniteStarVertexEmbedding n v =
      (t - hexagonalStep 1, false) := by
    apply hexagonalBrickVertex_injective
    exact hv
  rw [hu', hv'] at hamb
  exact hexagonalBrickFaces_middle_not_adj t hamb


theorem triHexPlanarFiniteStar_pfdFace_left_eq_right
    (n : Nat) (t : Site 2) :
    BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (hexagonalBrickFaceLeft t) =
      BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (hexagonalBrickFaceRight t) := by
  apply ConnectedComponent.connectedComponentMk_eq_of_adj
  rw [whb_faceRegion_adj]
  exact ⟨hexagonalBrickFaces_adj t,
    triHexPlanarFiniteStar_middle_not_mem_imageGraph n t⟩


end StatMech.FK.PeriodicPlanar
