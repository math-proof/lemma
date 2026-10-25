/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part4


namespace StatMech.FrontierD

noncomputable section

theorem lipschitzWith_sixVertexMomentumRapidity
    {lam : Real} (hlam : 0 < lam) :
    LipschitzWith (sixVertexMomentumRapidityLipschitzNNReal lam)
      (sixVertexMomentumRapidity lam hlam) := by
  let floor := sixVertexRapidityMomentumDerivativeFloor lam
  have hfloor : 0 < floor := sixVertexRapidityMomentumDerivativeFloor_pos hlam
  have hK : 0 <= 1 / floor := by positivity
  have hKcoe : (sixVertexMomentumRapidityLipschitzNNReal lam : Real) =
      1 / floor := by
    exact Real.coe_toNNReal _ hK
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let px := (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x : Real)
  let py := (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) y : Real)
  let alpha := sixVertexMomentumRapidity lam hlam x
  let beta := sixVertexMomentumRapidity lam hlam y
  have hpx : px ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [px]
    exact (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x).property
  have hpy : py ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [py]
    exact (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) y).property
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) x)).property
  have hbeta : beta ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [beta, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) y)).property
  have hkalpha : sixVertexRapidityMomentum lam alpha = px := by
    dsimp [alpha, px, sixVertexMomentumRapidity]
    exact congrArg Subtype.val
      ((sixVertexRapidityMomentumOrderIso lam hlam).apply_symm_apply _)
  have hkbeta : sixVertexRapidityMomentum lam beta = py := by
    dsimp [beta, py, sixVertexMomentumRapidity]
    exact congrArg Subtype.val
      ((sixVertexRapidityMomentumOrderIso lam hlam).apply_symm_apply _)
  have hdiff : Differentiable Real (sixVertexRapidityMomentum lam) :=
    fun z => (hasDerivAt_sixVertexRapidityMomentum hlam z).differentiableAt
  have hrapidity : |alpha - beta| <= (1 / floor) * |px - py| := by
    rcases le_total alpha beta with hab | hba
    · have hgrowth := (convex_Icc alpha beta).mul_sub_le_image_sub_of_le_deriv
          (continuous_iff_continuousAt.2 fun z =>
            (hasDerivAt_sixVertexRapidityMomentum hlam z).continuousAt).continuousOn
          hdiff.differentiableOn
          (fun z _ => by
            rw [(hasDerivAt_sixVertexRapidityMomentum hlam z).deriv]
            exact sixVertexRapidityMomentumDerivativeFloor_le hlam z)
          alpha (Set.left_mem_Icc.mpr hab) beta
          (Set.right_mem_Icc.mpr hab) hab
      rw [hkalpha, hkbeta] at hgrowth
      have hp : px <= py := by
        rw [<- hkalpha, <- hkbeta]
        exact (strictMono_sixVertexRapidityMomentum hlam).monotone hab
      have hmain : beta - alpha <= (1 / floor) * (py - px) := by
        calc
        beta - alpha <= (py - px) / floor :=
          (le_div_iff₀ hfloor).2 (by simpa [mul_comm] using hgrowth)
        _ = (1 / floor) * (py - px) := by ring
      simpa [abs_of_nonpos (sub_nonpos.mpr hab),
        abs_of_nonpos (sub_nonpos.mpr hp)] using hmain
    · have hgrowth := (convex_Icc beta alpha).mul_sub_le_image_sub_of_le_deriv
          (continuous_iff_continuousAt.2 fun z =>
            (hasDerivAt_sixVertexRapidityMomentum hlam z).continuousAt).continuousOn
          hdiff.differentiableOn
          (fun z _ => by
            rw [(hasDerivAt_sixVertexRapidityMomentum hlam z).deriv]
            exact sixVertexRapidityMomentumDerivativeFloor_le hlam z)
          beta (Set.left_mem_Icc.mpr hba) alpha
          (Set.right_mem_Icc.mpr hba) hba
      rw [hkalpha, hkbeta] at hgrowth
      have hp : py <= px := by
        rw [<- hkalpha, <- hkbeta]
        exact (strictMono_sixVertexRapidityMomentum hlam).monotone hba
      rw [abs_of_nonneg (sub_nonneg.mpr hba),
        abs_of_nonneg (sub_nonneg.mpr hp)]
      calc
        alpha - beta <= (px - py) / floor :=
          (le_div_iff₀ hfloor).2 (by simpa [mul_comm] using hgrowth)
        _ = (1 / floor) * (px - py) := by ring
  have hproj := (LipschitzWith.projIcc
    (by linarith [Real.pi_pos] : -Real.pi <= Real.pi)).dist_le_mul x y
  have hproj' : |px - py| <= |x - y| := by
    simpa [px, py, Real.dist_eq] using hproj
  rw [Real.dist_eq, Real.dist_eq, hKcoe]
  exact hrapidity.trans (mul_le_mul_of_nonneg_left hproj' hK)

end
end StatMech.FrontierD
