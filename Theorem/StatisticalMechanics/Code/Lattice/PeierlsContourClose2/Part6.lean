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
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem axisContourDualCircuit_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : AxisContourDualCircuit 2 n ℓ := by
  classical
  refine ⟨dualWalkContour, ?_⟩
  intro F hF
  obtain ⟨K, hKbox, hKcross, hKlen, hfin, hconn, j, hj, haxis⟩ := h F hF
  obtain ⟨c, htrail, hcov⟩ := exists_single_dualCircuit_of_connected hfin hconn haxis
  refine ⟨j, hj, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, ?_⟩
  · rw [circuit_length_eq_contourLen hKbox c htrail hcov, hKlen]
  · rw [circuit_decode_eq_contour hKbox c hcov, hKcross]


theorem realisedContourWalkEncoding_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : RealisedContourWalkEncoding 2 n ℓ :=
  realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_circuitData h)


theorem contourSubsetCountBound_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_walkEncoding (realisedContourWalkEncoding_of_circuitData h)


theorem connFamily_fixedLen_card_le_peierls_of_circuitData {n ℓ : ℕ}
    (h : PeierlsContourCircuitData n ℓ) :
    ((connClusterFamily (d := 2) n).filter
        (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card
      ≤ ℓ * (2 * 2) ^ ℓ :=
  connFamily_fixedLen_card_le_peierls n ℓ (contourSubsetCountBound_of_circuitData h)


theorem realisedContour_has_cluster {n ℓ : ℕ} {F : Finset (Sym2 (Site 2))}
    (hF : F ∈ realisedContours 2 n ℓ) :
    ∃ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n ∧
      (↑K : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ := by
  classical
  unfold realisedContours at hF
  rw [Finset.mem_image] at hF
  obtain ⟨K, hKmem, hKeq⟩ := hF
  rw [Finset.mem_filter, StatMech.Ising.pcc_mem_connClusterFamily] at hKmem
  exact ⟨K, StatMech.Ising.pcc_mem_connClusterFamily.mpr hKmem.1,
    StatMech.Ising.clusterFamily_subset_box hKmem.1.1, hKeq, hKmem.2⟩


end Lattice
end StatMech
