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
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


def TightAxisCircuitData (n ℓ : ℕ) : Prop :=
  ∀ F ∈ realisedContours 2 n ℓ,
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        j < ℓ ∧ axisVertex 2 j ∈ T ∧
        (∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
          e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet)


end Lattice
end StatMech
