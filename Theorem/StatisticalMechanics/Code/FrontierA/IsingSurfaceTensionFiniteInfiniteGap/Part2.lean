/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteInfiniteGap
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

theorem cubicalFiniteInfiniteSquareDensityGap_nonneg
    {K : Real} (hK : 0 < K) (n : Nat) :
    0 <= cubicalFiniteInfiniteSquareDensityGap K n := by
  exact sub_nonneg.mpr
    (cubicalInfiniteVolumeSquareWilsonDensity_le_finite hK n)


theorem cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop
      (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) := by
  have hfinite :=
    cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hK
  have hinfinite :=
    cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC
      K hK hlt
  simpa [cubicalFiniteInfiniteSquareDensityGap] using hfinite.sub hinfinite


theorem rectangularIsingSurfaceTension_eq_zero_iff_gap_tendsto_zero
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    rectangularIsingSurfaceTension (gaugeDualCoupling K) = 0 <->
      Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop (nhds 0) := by
  constructor
  · intro htau
    simpa [htau] using
      cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension K hK hlt
  · intro hzero
    exact tendsto_nhds_unique
      (cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension K hK hlt)
      hzero

end
end StatMech.FrontierA
