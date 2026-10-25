/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part4
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge
open Filter Topology
open scoped symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem rectangularPrismInterfaceDensity_eq_boundaryRatio
    (beta : Real) (n : Nat) :
    rectangularPrismInterfaceDensity beta n =
      (Real.log (StatMech.Ising.rectangularPrismPlusPartition
          1 beta (2 * n + 1) (2 * n + 1) n) -
        Real.log (StatMech.Ising.rectangularPrismDobrushinPartition
          1 beta (2 * n + 1) (2 * n + 1) n)) /
        ((2 * n + 1 : Nat) : Real) ^ 2 := by
  rw [rectangularPrismInterfaceDensity,
    StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio]


theorem oddCubicalIsingDisorderDensity_tendsto
    {beta : Real} (hbeta : 0 < beta) :
    Tendsto (oddCubicalIsingDisorderDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension beta)) := by
  have hsquare :=
    (rectangularIsingDobrushin_square_and_iterated_tendsto hbeta).1
  have hodd : Tendsto (fun n : Nat => 2 * n + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    omega
  simpa [oddCubicalIsingDisorderDensity, Function.comp_def] using
    hsquare.comp hodd


end
end StatMech.FrontierA
