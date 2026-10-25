/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part10
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


noncomputable def iptp_transInteriorEquiv (g : Multiplicative (Site d)) (S : Finset (Site d)) :
    {x : Site d // x ∈ S} ≃ {x : Site d // x ∈ S.image (fun x => g • x)} where
  toFun x := ⟨g • (x : Site d), Finset.mem_image_of_mem _ x.2⟩
  invFun y := ⟨g⁻¹ • (y : Site d), by
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp y.2
    rw [← hzeq, inv_smul_smul]; exact hz⟩
  left_inv x := by ext; simp [inv_smul_smul]
  right_inv y := by ext; simp [smul_inv_smul]


end Ising
end StatMech
