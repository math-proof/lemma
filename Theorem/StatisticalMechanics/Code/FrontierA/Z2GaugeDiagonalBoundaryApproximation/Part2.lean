/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

theorem cubicalDiagonalApproximationPadding_spec
    {K : Real} (hK : 0 < K) (n : Nat) :
    0 < cubicalDiagonalApproximationPadding hK n /\
      0 <= cubicalDiagonalFiniteInfiniteDensityGap hK n /\
      cubicalDiagonalFiniteInfiniteDensityGap hK n <
        (1 : Real) / ((centralSquareSide n : Nat) : Real) := by
  simpa [cubicalDiagonalApproximationPadding,
    cubicalDiagonalFiniteInfiniteDensityGap] using
      (Classical.choose_spec
        (exists_cubicalPaddedDisorderDensity_close_infiniteVolume hK n
          (by positivity :
            0 < (1 : Real) / ((centralSquareSide n : Nat) : Real))))


theorem cubicalDiagonalFiniteInfiniteDensityGap_tendsto_zero
    {K : Real} (hK : 0 < K) :
    Tendsto (cubicalDiagonalFiniteInfiniteDensityGap hK) atTop (nhds 0) := by
  have hvanish : Tendsto
      (fun n : Nat =>
        (1 : Real) / ((centralSquareSide n : Nat) : Real)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 : Real)).comp
      (tendsto_add_atTop_nat 1)
    simpa [centralSquareSide, Function.comp_def] using h
  apply squeeze_zero'
    (Eventually.of_forall fun n =>
      (cubicalDiagonalApproximationPadding_spec hK n).2.1)
    (Eventually.of_forall fun n =>
      (cubicalDiagonalApproximationPadding_spec hK n).2.2.le)
    hvanish


theorem cubicalDiagonalPaddedDisorderDensity_tendsto_zero_of_dual_lt_betaC
    (K : Real) (hK : 0 < K)
    (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
    Tendsto (fun n : Nat =>
      let m := cubicalDiagonalApproximationPadding hK n
      cubicalPaddedDisorderFreeEnergy K
          (centralSquareSide n) (centralSquareSide n) m m m m m m /
        ((centralSquareSide n : Nat) : Real) ^ 2) atTop (nhds 0) := by
  have hgap := cubicalDiagonalFiniteInfiniteDensityGap_tendsto_zero hK
  have hinfinite :=
    cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC
      K hK hlt
  have hsum := hgap.add hinfinite
  simpa [cubicalDiagonalFiniteInfiniteDensityGap] using hsum

end
end StatMech.FrontierA
