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
import Def.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part3
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


@[simp] theorem mem_plusCutSites {Lambda : Finset (Site d)}
    {T : Finset {v // v ∈ Lambda}} {x : {v // v ∈ Lambda}} :
    x.1 ∈ plusCutSites T ↔ x ∈ T := by
  constructor
  · intro hx
    rw [plusCutSites, Finset.mem_image] at hx
    obtain ⟨y, hy, hval⟩ := hx
    have hyx : y = x := Subtype.ext hval
    subst y
    exact hy
  · exact fun hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩

end Sharpness
end StatMech
