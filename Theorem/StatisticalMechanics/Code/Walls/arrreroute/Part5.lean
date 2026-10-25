/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean -/

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
import Def.StatisticalMechanics.Code.Walls.arrreroute.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem arr_insert_tromino_eq_square :
    insert (![(1:ℤ), 1] : Site 2) pc2_tromino = arr_square := by
  unfold arr_square pc2_tromino
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto


theorem arr_c_notMem_tromino : (![(1:ℤ), 1] : Site 2) ∉ pc2_tromino := by
  unfold pc2_tromino
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [site2_eq, site2_eq, site2_eq]; omega


theorem arr_attach_square_data :
    (![(1:ℤ), 1] : Site 2) ∉ pc2_tromino ∧
      IsConnectedCluster pc2_tromino ∧
      insert (![(1:ℤ), 1] : Site 2) pc2_tromino = arr_square :=
  ⟨arr_c_notMem_tromino, pc2_tromino_isConnectedCluster, arr_insert_tromino_eq_square⟩


end Walls
end StatMech
