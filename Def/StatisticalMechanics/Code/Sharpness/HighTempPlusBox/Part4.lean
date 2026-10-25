/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part3
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


noncomputable def plusCutVertexEquiv {Lambda : Finset (Site d)}
    (T : Finset {v // v ∈ Lambda}) :
    {x : {v // v ∈ Lambda} // x ∈ T} ≃
      {z : Site d // z ∈ plusCutSites T} :=
  Equiv.ofBijective
    (fun x ↦ ⟨x.1.1, mem_plusCutSites.mpr x.2⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : {z : Site d // z ∈ plusCutSites T} ↦ z.1) h,
    by
      intro z
      have hz : z.1 ∈ T.image Subtype.val := z.2
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, hval⟩ := hz
      exact ⟨⟨x, hx⟩, Subtype.ext hval⟩⟩

end Sharpness
end StatMech
