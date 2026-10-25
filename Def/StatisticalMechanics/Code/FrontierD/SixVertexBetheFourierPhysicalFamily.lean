/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Mathlib.Topology.Homeomorph.Lemmas
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily


namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityMomentumFamilyEquiv
    {a b : Real} (ha : 2 < a) :
    (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) ≃
      (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) where
  toFun z :=
    (z.1, ⟨sixVertexRapidityMomentum
      (sixVertexAntiferroelectricLambda z.1.1) z.2.1,
      sixVertexRapidityMomentum_mem_Icc
        (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2.2⟩)
  invFun z :=
    (z.1, (sixVertexRapidityMomentumOrderIso
      (sixVertexAntiferroelectricLambda z.1.1)
      (sixVertexAntiferroelectricLambda_pos
        (ha.trans_le z.1.2.1))).symm z.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · exact (sixVertexRapidityMomentumOrderIso
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexAntiferroelectricLambda_pos
          (ha.trans_le z.1.2.1))).symm_apply_apply z.2
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact (sixVertexRapidityMomentumOrderIso
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexAntiferroelectricLambda_pos
          (ha.trans_le z.1.2.1))).apply_symm_apply z.2

end
end StatMech.FrontierD
