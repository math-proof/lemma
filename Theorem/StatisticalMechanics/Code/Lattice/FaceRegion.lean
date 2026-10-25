/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.FaceRegion
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem mem_bdEdgeSet2 (S : Set (Site 2)) (x y : Site 2) :
    s(x, y) ∈ bdEdgeSet2 S ↔ (x ∈ S ↔ y ∉ S) := by
  unfold bdEdgeSet2
  rw [Set.mem_setOf_eq]
  rfl


end Lattice
end StatMech
