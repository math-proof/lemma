/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledBetheCandidateRate_eq_rootAverage
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    sixVertexHalfFilledBetheCandidateRate hc k =
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexPositiveHalfBetheRootFamily hc) k := by
  rw [sixVertexHalfFilledBetheCandidateRate,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
  ring

theorem sixVertexSelectedRootAverage_eq_logKernel
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc) k =
      (∑ j, Real.log
        (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) *
              Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) /
          (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)))) /
        (sixVertexFourWidth 0 k : ℝ) := by
  have hlog (j : Fin (k + 1)) :=
    sixVertexBetheM_phase_log_norm c
      (sixVertexPositiveHalfBetheRoots hc k j)
      (sixVertexHalfFilledBetheRoots_phase_ne_one hc k
        (Fin.natAdd (k + 1) j))
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
  simp_rw [hlog]
  rw [Finset.mul_sum]
  apply congrArg (fun t : ℝ => t / (sixVertexFourWidth 0 k : ℝ))
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sixVertexSelectedLogKernel_pos
    {c : ℝ} (hc : 2 < c) (k : ℕ) (j : Fin (k + 1)) :
    0 < (((c ^ 2 - 1) ^ 2 + 1 +
          2 * (c ^ 2 - 1) *
            Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) /
        (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j))) := by
  let p := sixVertexPositiveHalfBetheRoots hc k j
  have hM := Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
  have hphase := sixVertexHalfFilledBetheRoots_phase_ne_one hc k
    (Fin.natAdd (k + 1) j)
  rw [sixVertexBetheM_phase_normSq c p hphase] at hM
  exact hM

end
end StatMech.FrontierD
