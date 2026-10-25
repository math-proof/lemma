/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness hc s]
      with k hk
  have hlift : sixVertexEvenSymmetricLift (s + k + 1)
      (sixVertexEvenPositiveHalfProjection (s + k + 1)
        (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k)) =
      sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k :=
    sixVertexEvenSymmetricLift_projection (s + k + 1) hk.1.2.1
  have hpositive (j : Fin (s + k + 1)) :
      sixVertexEvenPositiveHalfProjection (s + k + 1)
          (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k) j ∈
        Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    rw [hlift]
    exact hk.1
  unfold sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue
  rw [← sixVertexSymmetricBetheEigenvalueKernel_eq_value c _ hpositive]
  exact hk.2.2

end
end StatMech.FrontierD
