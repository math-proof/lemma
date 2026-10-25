/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteTwoBranchWeightedTransport
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone.Part2
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTrace_logConcave_of_physicalPairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 1 <= c)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
  have hmass := fintype_sum_le_of_twoBranchWeight
    (fun choice source => embeddings.branch choice source)
    (fun choice => (embeddings.branch choice).injective)
    (fun source => c ^ sixVertexConfigurationPairTotalCPhysical source)
    (fun target => c ^ sixVertexConfigurationPairTotalCPhysical target)
    (fun target => pow_nonneg (by linarith) _)
    (fun source => two_mul_pow_le_pow_add_pow_of_twice_le_add hc
      (embeddings.aggregateTotalC source))
  rw [sum_pow_configurationPairTotalC_eq_trace_mul_trace,
    sum_pow_configurationPairTotalC_eq_trace_mul_trace] at hmass
  simpa [pow_two] using hmass

end
end StatMech.FrontierD
