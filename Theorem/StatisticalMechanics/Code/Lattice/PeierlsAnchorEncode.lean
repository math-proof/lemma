/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
import Def.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem realisedContourWalkEncoding_of_perContour {n ℓ : ℕ}
    (h : PerContourDualCircuit d n ℓ) : RealisedContourWalkEncoding d n ℓ := by
  classical
  obtain ⟨anchorPool, hcard, decode, hcirc⟩ := h
  
  
  refine ⟨anchorPool, hcard,
    fun F => if hF : F ∈ realisedContours d n ℓ
      then ⟨(hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩
      else ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩,
    decode, ?_⟩
  
  intro F hF
  beta_reduce
  have hred : (if hF : F ∈ realisedContours d n ℓ
      then (⟨(hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩ :
        Σ v : Site d, (hypercubicLattice d).Walk v v)
      else ⟨StatMech.Ising.origin d, SimpleGraph.Walk.nil⟩)
      = ⟨(hcirc F hF).choose, (hcirc F hF).choose_spec.2.choose⟩ := dif_pos hF
  refine ⟨?_, ?_, ?_⟩
  · rw [hred]
    exact (hcirc F hF).choose_spec.1
  · rw [hred]
    exact (hcirc F hF).choose_spec.2.choose_spec.1
  · rw [hred]
    exact (hcirc F hF).choose_spec.2.choose_spec.2


end Lattice
end StatMech
