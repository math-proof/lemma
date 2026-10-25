/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized
    (s k : Nat) (j : Fin (s + k + 1)) :
    Tendsto
      (fun c => Complex.normSq
          (sixVertexBetheM c
            (sixVertexBethePhase
              (sixVertexFixedEvenPositiveBetheRootAt s k j c)) /
            (c ^ 2 - 2 : Real)))
      atTop (nhds (sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
  have h := (Complex.continuous_normSq.continuousAt.tendsto.comp
    (tendsto_sixVertexFixedEvenPositiveBetheM_normalized s k j))
  convert h using 1
  rw [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_one]
  have hden : Complex.normSq (1 - sixVertexBethePhase
      (sixVertexFixedEvenPositiveLimitingRoot s k j)) =
      2 - 2 * Real.cos (sixVertexFixedEvenPositiveLimitingRoot s k j) := by
    rw [Complex.normSq_sub]
    have hz : Complex.normSq (sixVertexBethePhase
        (sixVertexFixedEvenPositiveLimitingRoot s k j)) = 1 := by
      rw [Complex.normSq_eq_norm_sq,
        sixVertexBethePhase_norm, one_pow]
    rw [Complex.normSq_one, hz]
    simp [sixVertexBethePhase, Complex.exp_re]
    norm_num
  rw [hden]
  rfl


end
end StatMech.FrontierD
