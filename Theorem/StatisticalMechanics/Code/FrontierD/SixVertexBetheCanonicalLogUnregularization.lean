/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLogRegularizationCutoff
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalRegularizedQuadrature


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem sixVertexBetheLogObservable_eq_logNormKernel
    {c x : Real} (hc : 2 < c) (hx : x ∈ Set.Ioo 0 Real.pi) :
    sixVertexBetheLogObservable c x = sixVertexBetheLogNormKernel c x := by
  have hphase : sixVertexBethePhase x ≠ 1 :=
    sixVertexBethePhase_ne_one_of_mem_Ioo
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans hx.1, hx.2⟩ hx.1.ne'
  unfold sixVertexBetheLogObservable
  rw [sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator hc hphase]
  unfold sixVertexBetheLogNormKernel sixVertexBetheLogNumerator
    sixVertexBetheLogDenominator
  rfl

end
end StatMech.FrontierD
