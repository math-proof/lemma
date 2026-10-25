/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


def OuterContourFill (n : ℕ) : Prop :=
  ∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧
      ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        FaceBoundaryConnected (↑K : Set (Site 2)) T ∧
        j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T


noncomputable def outerExteriorComponent (S : Set (Site 2)) (n : ℕ) : Set (Site 2) :=
  {x | (latticeOn Sᶜ).Reachable (beacon 2 n) x}


noncomputable def spinCompatibleFill (S : Set (Site 2)) (n : ℕ) : Set (Site 2) :=
  (outerExteriorComponent S n)ᶜ


end Ising
end StatMech
