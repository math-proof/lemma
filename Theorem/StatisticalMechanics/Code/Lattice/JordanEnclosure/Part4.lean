module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Def.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part3
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

@[simp] theorem faceBoundaryGraph_adj (S : Set (Site 2)) (f g : Site 2) :
    (faceBoundaryGraph S).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ bdEdge S (sharedPrimalEdge f g) := Iff.rfl


theorem faceBoundaryGraph_le (S : Set (Site 2)) :
    faceBoundaryGraph S ≤ hypercubicLattice 2 := fun _ _ h => h.1


end Lattice
end StatMech
