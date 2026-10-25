/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem peierlsContourCircuitData_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : PeierlsContourCircuitData n ℓ := by
  intro F hF
  obtain ⟨K, hKconn, hKbox, hKcross, hKlen⟩ := realisedContour_has_cluster hF
  obtain ⟨hfin, hconn, j, hj, haxis⟩ := h K hKconn hKlen
  exact ⟨K, hKbox, hKcross, hKlen, hfin, hconn, j, hj, haxis⟩


theorem axisContourDualCircuit_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : AxisContourDualCircuit 2 n ℓ :=
  axisContourDualCircuit_of_circuitData (peierlsContourCircuitData_of_geometryResidue h)


theorem contourSubsetCountBound_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_circuitData (peierlsContourCircuitData_of_geometryResidue h)


theorem connFamily_fixedLen_card_le_peierls_of_geometryResidue {n ℓ : ℕ}
    (h : ContourGeometryResidue n ℓ) :
    ((connClusterFamily (d := 2) n).filter
        (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card
      ≤ ℓ * (2 * 2) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls_of_circuitData
    (peierlsContourCircuitData_of_geometryResidue h)


theorem peierlsContourCircuitData_of_empty {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : PeierlsContourCircuitData n ℓ := by
  intro F hF
  rw [hempty] at hF
  simp at hF


theorem contourGeometryResidue_of_no_cluster {n ℓ : ℕ}
    (hempty : ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n →
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ≠ ℓ) :
    ContourGeometryResidue n ℓ := by
  intro K hK hlen
  exact absurd hlen (hempty K hK)


theorem contourSubsetCountBound_of_empty_circuitData {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_circuitData (peierlsContourCircuitData_of_empty hempty)


theorem peierls_long_range_order_of_geometryResidue
    (h : ∀ (n ℓ : ℕ), ContourGeometryResidue n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_walkEncoding (by norm_num)
    (fun n ℓ => realisedContourWalkEncoding_of_circuitData
      (peierlsContourCircuitData_of_geometryResidue (h n ℓ)))

end Lattice
end StatMech
