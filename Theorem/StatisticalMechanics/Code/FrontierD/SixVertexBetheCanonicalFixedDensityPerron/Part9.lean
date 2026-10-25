/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part9


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower
    {c : Real} (hc : 2 < c) {N q : Nat} (hN : 0 < N) (hq : 0 < q)
    (hhalf : N = 2 * q) {p : Fin q -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N q p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N q p x) :
    sixVertexWeightedFiniteDensityGauge hc N q p
        (sixVertexFourierPhysicalDensityMap hc) <=
      sixVertexHalfDensityInvWidthConstantOfLower c lower / N := by
  let rate := sixVertexRootDensityContractionRate c
  let G := sixVertexWeightedFiniteDensityGauge hc N q p
    (sixVertexFourierPhysicalDensityMap hc)
  have hrateGap : 0 < 1 - rate :=
    sub_pos.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2
  have himprove : G <= rate * G +
      sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
    cases q with
    | zero => omega
    | succ n =>
        exact sixVertexWeightedFiniteDensityGauge_selfImproves hc hN
          (by omega) (by omega) hopen hsol
          (sixVertexFourierPhysicalDensityMap hc)
          (sixVertexFourierPhysicalDensity_continuumEquation hc)
          (intervalIntegral_sixVertexFourierPhysicalDensity hc)
          hlower hdensity (norm_nonneg _) le_rfl
  have hbasic : (1 - rate) * G <=
      sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
    nlinarith
  have hbasic' : (1 - rate) * G <=
      sixVertexFiniteDensityContinuumErrorOfLower c 1 lower / N :=
    hbasic.trans_eq
      (sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div c lower hN)
  rw [mul_comm] at hbasic'
  have hdiv := (le_div_iff₀ hrateGap).2 hbasic'
  change sixVertexWeightedFiniteDensityGauge hc N q p
      (sixVertexFourierPhysicalDensityMap hc) <= _ at hdiv
  unfold sixVertexHalfDensityInvWidthConstantOfLower
  dsimp [rate] at hdiv ⊢
  convert hdiv using 1
  field_simp [hrateGap.ne']

theorem eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc k)
          (sixVertexFourierPhysicalDensityMap hc) <=
        sixVertexHalfDensityInvWidthConstantOfLower c
            (sixVertexCanonicalHalfDensityFloor hc) /
          sixVertexFourWidth 0 k := by
  filter_upwards
    [eventually_sixVertexCanonicalHalfDensityFloor_le hc] with k hk
  apply sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower hc
    (sixVertexFourWidth_pos 0 k) (by omega)
    (by unfold sixVertexFourWidth; omega)
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
    (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k)
    (sixVertexCanonicalHalfDensityFloor_pos hc) hk

end
end StatMech.FrontierD
