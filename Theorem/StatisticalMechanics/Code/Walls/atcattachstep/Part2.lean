/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atcattachstep.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Def.StatisticalMechanics.Code.Walls.atcattachstep
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem atc_hasRemovableCell_of_conn (h : atc_HasRemovableConnCell) : fbc_HasRemovableCell := by
  intro K hcard hconn hhf
  obtain ⟨c, hcK, hcorigin, ⟨n, hn, hadj⟩, hconn'⟩ := h K hcard hconn
  exact ⟨c, hcK, hcorigin, hconn', atc_holeFree_erase hcK hhf hn hadj⟩

end Walls
end StatMech
