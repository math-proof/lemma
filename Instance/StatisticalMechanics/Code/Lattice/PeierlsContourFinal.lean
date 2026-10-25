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
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


noncomputable instance componentGraph_locallyFinite (K : Set (Site 2)) (f : Site 2) :
    LocallyFinite (componentGraph K f) := by
  classical
  intro a
  by_cases ha : (faceBoundaryGraph K).Reachable f a
  · rw [componentGraph_neighborSet_eq ha]
    exact (instLocallyFiniteFaceBoundaryGraph K a)
  · rw [componentGraph_neighborSet_empty ha]
    exact Set.fintypeEmpty


end Lattice
end StatMech
