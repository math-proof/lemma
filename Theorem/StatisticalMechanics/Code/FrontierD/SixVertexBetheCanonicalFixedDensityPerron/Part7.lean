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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part7


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower
    {c : Real} (hc : 2 < c) {N q r : Nat} (hN : 0 < N) (hq : 0 < q)
    (hcharge : N = 2 * q + 2 * r) {p : Fin q -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N q p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N q p x) :
    sixVertexWeightedFiniteDensityGauge hc N q p
        (sixVertexFourierPhysicalDensityMap hc) <=
      sixVertexFixedChargeDensityInvWidthConstantOfLower c r lower / N := by
  let rate := sixVertexRootDensityContractionRate c
  let G := sixVertexWeightedFiniteDensityGauge hc N q p
    (sixVertexFourierPhysicalDensityMap hc)
  have hrateGap : 0 < 1 - rate :=
    sub_pos.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2
  have himprove : G <= rate * G +
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    exact sixVertexWeightedFiniteDensityGauge_selfImproves_fixedCharge_count
      hc hN hq hcharge hopen hsol
      (sixVertexFourierPhysicalDensityMap hc)
      (sixVertexFourierPhysicalDensity_continuumEquation hc)
      (intervalIntegral_sixVertexFourierPhysicalDensity hc)
      hlower hdensity (norm_nonneg _) le_rfl
  have hbasic : (1 - rate) * G <=
      sixVertexFixedChargeDensityStabilityErrorOfLower c N r lower := by
    nlinarith
  have hbasic' : (1 - rate) * G <=
      sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower / N :=
    hbasic.trans_eq
      (sixVertexFixedChargeDensityStabilityErrorOfLower_eq_one_div
        c lower r hN)
  rw [mul_comm] at hbasic'
  have hdiv := (le_div_iff₀ hrateGap).2 hbasic'
  change sixVertexWeightedFiniteDensityGauge hc N q p
      (sixVertexFourierPhysicalDensityMap hc) <= _ at hdiv
  unfold sixVertexFixedChargeDensityInvWidthConstantOfLower
  dsimp [rate] at hdiv ⊢
  convert hdiv using 1
  field_simp [hrateGap.ne']

theorem eventually_sixVertexCanonicalFixedEvenDensityGauge_le_invWidth
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1))
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
          (sixVertexFourierPhysicalDensityMap hc) <=
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
            (sixVertexCanonicalFixedEvenDensityFloor hc s) /
          sixVertexFourWidth (2 * s) k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  apply sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower hc
    (sixVertexFourWidth_pos (2 * s) k) (by omega)
    (by unfold sixVertexFourWidth; omega)
    hk.1.1 hk.1.2.1
    (sixVertexCanonicalFixedEvenDensityFloor_pos hc s) hk.2

theorem eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexWeightedFiniteDensityGauge hc
          (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
          (sixVertexFourierPhysicalDensityMap hc) <=
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
            (sixVertexCanonicalFixedOddDensityFloor hc s) /
          sixVertexFourWidth (2 * s + 1) k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  apply sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower hc
    (sixVertexFourWidth_pos (2 * s + 1) k) (by omega)
    (by unfold sixVertexFourWidth; omega)
    hk.1.1 hk.1.2.1
    (sixVertexCanonicalFixedOddDensityFloor_pos hc s) hk.2

end
end StatMech.FrontierD
