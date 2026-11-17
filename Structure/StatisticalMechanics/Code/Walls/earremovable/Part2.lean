/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
public import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
public import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part3
public section

open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


structure ear_IsAntiExtreme (K : Set (Site 2)) (b : Site 2) : Prop where
  
  mem : b ∈ K
  
  minimal : ∀ v ∈ K, ear_gKey b ≤ ear_gKey v


end Walls
end StatMech
