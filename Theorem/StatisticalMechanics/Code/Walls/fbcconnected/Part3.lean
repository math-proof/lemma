module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
public import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
public import Def.StatisticalMechanics.Code.Walls.fbcconnected.Part2
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem fbc_residue_of_inputs (hattach : fbc_AttachStep) (hrem : fbc_HasRemovableCell) :
    fbc_BoundaryConnResidue :=
  fun K hconn hhf => fbc_boundaryReachable_of_inputs hattach hrem K hconn hhf


end Walls
end StatMech
