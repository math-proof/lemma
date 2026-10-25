/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


def OuterContourWinding (n : ℕ) : Prop :=
  ∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧
      ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T ∧
        (∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
          e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet)


def IsHoleFreeBoxCluster (n : ℕ) (K : Finset (Site 2)) : Prop :=
  IsConnectedCluster K ∧
    ∃ (T : Finset (Site 2)) (j : ℕ),
      (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
      j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 j ∈ T ∧
      (∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
        e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet)


noncomputable def holeFreeClusterFamily (n : ℕ) : Finset (Finset (Site 2)) :=
  (clusterFamily (d := 2) n).filter (fun K => IsHoleFreeBoxCluster n K)

end Ising
end StatMech
