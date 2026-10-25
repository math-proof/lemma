/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


@[simp] theorem componentGraph_adj (K : Set (Site 2)) (f a b : Site 2) :
    (componentGraph K f).Adj a b ↔ (faceBoundaryGraph K).Adj a b ∧
      (faceBoundaryGraph K).Reachable f a ∧ (faceBoundaryGraph K).Reachable f b :=
  Iff.rfl


theorem componentGraph_le (K : Set (Site 2)) (f : Site 2) :
    componentGraph K f ≤ faceBoundaryGraph K := fun _ _ h => h.1


theorem componentGraph_neighborSet_eq {K : Set (Site 2)} {f a : Site 2}
    (ha : (faceBoundaryGraph K).Reachable f a) :
    (componentGraph K f).neighborSet a = (faceBoundaryGraph K).neighborSet a := by
  ext b
  simp only [SimpleGraph.mem_neighborSet, componentGraph_adj]
  constructor
  · rintro ⟨hadj, _, _⟩; exact hadj
  · intro hadj; exact ⟨hadj, ha, ha.trans hadj.reachable⟩


theorem componentGraph_neighborSet_empty {K : Set (Site 2)} {f a : Site 2}
    (ha : ¬ (faceBoundaryGraph K).Reachable f a) :
    (componentGraph K f).neighborSet a = ∅ := by
  ext b
  simp only [SimpleGraph.mem_neighborSet, componentGraph_adj, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hra, _⟩; exact ha hra

end Lattice
end StatMech
