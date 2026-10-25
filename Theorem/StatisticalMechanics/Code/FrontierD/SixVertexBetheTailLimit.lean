/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
import Mathlib.Topology.ContinuousMap.Ordered
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailLimit


namespace StatMech.FrontierD

noncomputable section

open Filter Topology

theorem sixVertexTailConvolutionError_fourWidth_pos
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k : Nat) :
    0 < sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) := by
  unfold sixVertexTailConvolutionError
  have hK := sixVertexRootDensityKernelLipschitzBound_pos hc
  have hfloor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hB : 0 < sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  positivity

theorem cauchySeq_sixVertexSelectedWeightedDensityMap
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    CauchySeq (sixVertexSelectedWeightedDensityMap hc) := by
  apply Metric.cauchySeq_iff.2
  intro eps heps
  let rate := sixVertexRootDensityContractionRate c
  let D := (2 * Real.pi) * (1 - rate)
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hD : 0 < D := by
    dsimp [D, rate]
    exact mul_pos (by positivity) (sub_pos.mpr hrate.2)
  have herror := sixVertexTailConvolutionError_fourWidth_tendsto_zero hc htail
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 herror)
    (eps * D / 4) (by positivity)
  refine ⟨K, ?_⟩
  intro m hm n hn
  have hemDist := hK m hm
  have henDist := hK n hn
  have hem : sixVertexTailConvolutionError c (sixVertexFourWidth 0 m) <
      eps * D / 4 := by
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (sixVertexTailConvolutionError_fourWidth_pos hc htail m)] at hemDist
    exact hemDist
  have hen : sixVertexTailConvolutionError c (sixVertexFourWidth 0 n) <
      eps * D / 4 := by
    rw [Real.dist_eq, sub_zero,
      abs_of_pos (sixVertexTailConvolutionError_fourWidth_pos hc htail n)] at henDist
    exact henDist
  let B := ((sixVertexTailConvolutionError c (sixVertexFourWidth 0 m) +
      sixVertexTailConvolutionError c (sixVertexFourWidth 0 n)) /
        (2 * Real.pi)) / (1 - rate)
  have hB : 0 <= B := by
    dsimp [B, rate]
    exact div_nonneg
      (div_nonneg (add_nonneg
        (sixVertexTailConvolutionError_fourWidth_pos hc htail m).le
        (sixVertexTailConvolutionError_fourWidth_pos hc htail n).le)
        (by positivity))
      (sub_nonneg.mpr hrate.2.le)
  have hdist : dist (sixVertexSelectedWeightedDensityMap hc m)
      (sixVertexSelectedWeightedDensityMap hc n) <= B := by
    apply (ContinuousMap.dist_le hB).2
    intro x
    rw [Real.dist_eq]
    change |sixVertexRootDensityWeight c x *
        sixVertexSelectedFiniteRootDensity hc m x -
      sixVertexRootDensityWeight c x *
        sixVertexSelectedFiniteRootDensity hc n x| <= B
    rw [← mul_sub]
    exact sixVertexSelectedFiniteRootDensity_weighted_cauchy_tail
      hc htail m n x x.property
  calc
    dist (sixVertexSelectedWeightedDensityMap hc m)
        (sixVertexSelectedWeightedDensityMap hc n) <= B := hdist
    _ < eps := by
      dsimp [B, D, rate] at *
      rw [div_div, div_lt_iff₀ (mul_pos (by positivity : 0 < 2 * Real.pi)
        (by linarith [hrate.2] : 0 < 1 - sixVertexRootDensityContractionRate c))]
      nlinarith

end
end StatMech.FrontierD
