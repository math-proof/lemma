/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Theorem.StatisticalMechanics.Code.Walls.arrreroute.Part5
import Def.StatisticalMechanics.Code.Walls.cycboundary.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem cyc_boundaryCycle_of_noPinch {K : Set (Site 2)}
    (hreach : fbc_BoundaryReachable K) (hnp : cyc_NoPinch K) :
    cyc_BoundaryCycle K := by
  refine ⟨hreach, fun f hf => ?_⟩
  rw [cyc_degree_two_iff_le_two hf]
  exact hnp f hf


theorem cyc_singleton_face00_degree_two :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).degree ![(0:ℤ), 0] = 2 := by
  rw [show (![(0:ℤ), 0] : Site 2) = ![(0:ℤ), (0:ℤ)] from rfl, degree_faceBoundaryGraph]
  unfold faceBoundaryDegree bdInd faceCorner00 faceCorner10 faceCorner11 faceCorner01
  simp only [mem_singletonOrigin]
  norm_num


end Walls
end StatMech
