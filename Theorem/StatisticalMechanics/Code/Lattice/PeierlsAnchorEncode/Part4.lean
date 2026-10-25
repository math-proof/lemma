/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
import Def.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem perContourDualCircuit_of_axis {n ℓ : ℕ} (h : AxisContourDualCircuit d n ℓ) :
    PerContourDualCircuit d n ℓ := by
  classical
  obtain ⟨decode, hcirc⟩ := h
  refine ⟨axisAnchorPool d ℓ, axisAnchorPool_card_le d ℓ, decode, ?_⟩
  intro F hF
  obtain ⟨j, hj, W, hlen, hdec⟩ := hcirc F hF
  refine ⟨axisVertex d j, ?_, W, hlen, hdec⟩
  
  simp only [axisAnchorPool, Finset.mem_image, Finset.mem_range]
  exact ⟨j, hj, rfl⟩


theorem realisedContourWalkEncoding_of_axisCircuit {n ℓ : ℕ}
    (h : AxisContourDualCircuit d n ℓ) : RealisedContourWalkEncoding d n ℓ :=
  realisedContourWalkEncoding_of_perContour (perContourDualCircuit_of_axis h)


theorem perContourDualCircuit_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : PerContourDualCircuit d n ℓ := by
  refine ⟨∅, by simp, fun _ => ∅, ?_⟩
  intro F hF
  rw [hempty] at hF
  simp at hF


theorem axisContourDualCircuit_of_empty {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : AxisContourDualCircuit d n ℓ := by
  refine ⟨fun _ => ∅, ?_⟩
  intro F hF
  rw [hempty] at hF
  simp at hF


theorem contourSubsetCountBound_of_empty_axis {n ℓ : ℕ}
    (hempty : realisedContours d n ℓ = ∅) : ContourSubsetCountBound d n ℓ :=
  contourSubsetCountBound_of_walkEncoding
    (realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_empty hempty))

end Lattice
end StatMech
