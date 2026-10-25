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
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


def componentGraph (K : Set (Site 2)) (f : Site 2) : SimpleGraph (Site 2) where
  Adj a b := (faceBoundaryGraph K).Adj a b ∧ (faceBoundaryGraph K).Reachable f a ∧
    (faceBoundaryGraph K).Reachable f b
  symm := by
    constructor
    rintro a b ⟨hadj, hra, hrb⟩
    exact ⟨hadj.symm, hrb, hra⟩
  loopless := by
    refine ⟨fun a => ?_⟩
    rintro ⟨hadj, _, _⟩
    exact (faceBoundaryGraph K).irrefl hadj

end Lattice
end StatMech
