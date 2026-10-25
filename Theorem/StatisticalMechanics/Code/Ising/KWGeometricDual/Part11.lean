/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part12
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_faceInside_eq_of_regionReachable (P : PlanarZ2Subgraph) {x : P.V}
    (p : P.G.Walk x x) {a b : Site 2}
    (hab : (whb_faceRegion (imageGraph P)).Reachable a b) :
    (fwr_faceInside (kwg_latticeWalk P p) a ↔
      fwr_faceInside (kwg_latticeWalk P p) b) := by
  classical
  rcases hab with ⟨q⟩
  induction q with
  | nil => rfl
  | @cons u v w huv q ih =>
      have hnot : sharedPrimalEdge u v ∉ (kwg_latticeWalk P p).edges := by
        intro hmem
        have hmem' : sharedPrimalEdge u v ∈ (p.map (kwg_imageHom P)).edges := by
          rw [show (kwg_latticeWalk P p).edges =
            (p.map (kwg_imageHom P)).edges from
              SimpleGraph.Walk.edges_mapLe_eq_edges _ _] at hmem
          exact hmem
        have himg : sharedPrimalEdge u v ∈ (imageGraph P).edgeSet := by
          exact (p.map (kwg_imageHom P)).edges_subset_edgeSet hmem'
        exact huv.2 himg
      have hsame : fwr_faceInside (kwg_latticeWalk P p) u ↔
          fwr_faceInside (kwg_latticeWalk P p) v := by
        have hflip := fwr_faceCutFlip (kwg_latticeWalk P p) huv.1
        have hzero : (kwg_latticeWalk P p).edges.count (sharedPrimalEdge u v) = 0 :=
          List.count_eq_zero.mpr hnot
        rw [hzero] at hflip
        simp only [Nat.not_odd_zero, iff_false] at hflip
        tauto
      exact hsame.trans ih


end Ising
end StatMech
