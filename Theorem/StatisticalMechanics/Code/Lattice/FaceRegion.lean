module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Def.StatisticalMechanics.Code.Lattice.FaceRegion
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

@[simp] theorem mem_bdEdgeSet2 (S : Set (Site 2)) (x y : Site 2) :
    s(x, y) ∈ bdEdgeSet2 S ↔ (x ∈ S ↔ y ∉ S) := by
  unfold bdEdgeSet2
  rw [Set.mem_setOf_eq]
  rfl


end Lattice
end StatMech
