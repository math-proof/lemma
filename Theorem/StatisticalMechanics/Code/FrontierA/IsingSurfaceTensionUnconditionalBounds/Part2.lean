/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

theorem cubicalInfiniteVolumeSquareWilsonDensity_nonneg
    {K : Real} (hK : 0 < K) (n : Nat) :
    0 <= cubicalInfiniteVolumeSquareWilsonDensity K n := by
  have hw := cubicalInfiniteVolumeWilsonExpectation_mem_Icc hK
    (centralSquareSide n) (centralSquareSide n)
  unfold cubicalInfiniteVolumeSquareWilsonDensity
  apply div_nonneg
  · unfold cubicalInfiniteVolumeWilsonFreeEnergy
    rw [neg_nonneg]
    exact Real.log_nonpos hw.1 hw.2
  · positivity


theorem cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC
    (K : Real) (hK : 0 < K) (hlt : gaugeDualCoupling K < betaC 3) :
    Tendsto (cubicalInfiniteVolumeSquareWilsonDensity K) atTop (nhds 0) := by
  obtain ⟨C, hC, hfree⟩ :=
    exists_cubicalInfiniteVolumeWilsonFreeEnergy_perimeterUpper_of_dual_lt_betaC
      K hK hlt
  have hupper : ∀ n,
      cubicalInfiniteVolumeSquareWilsonDensity K n <=
        C / ((centralSquareSide n : Nat) : Real) := by
    intro n
    have hs : (0 : Real) < (centralSquareSide n : Nat) := by
      positivity
    unfold cubicalInfiniteVolumeSquareWilsonDensity
    calc
      cubicalInfiniteVolumeWilsonFreeEnergy K
            (centralSquareSide n) (centralSquareSide n) /
          ((centralSquareSide n : Nat) : Real) ^ 2 <=
        (C * (centralSquareSide n : Nat)) /
          ((centralSquareSide n : Nat) : Real) ^ 2 := by
            exact div_le_div_of_nonneg_right (hfree n) (sq_nonneg _)
      _ = C / ((centralSquareSide n : Nat) : Real) := by
        field_simp
  have hvanish : Tendsto
      (fun n : Nat => C / ((centralSquareSide n : Nat) : Real))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (tendsto_add_atTop_nat 1)
    simpa [centralSquareSide, Function.comp_def] using h
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      cubicalInfiniteVolumeSquareWilsonDensity_nonneg hK n)
    (Filter.Eventually.of_forall hupper)
    hvanish

end
end StatMech.FrontierA
