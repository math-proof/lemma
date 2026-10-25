/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityCandidate


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  have hlift : sixVertexEvenSymmetricLift (s + k + 1)
      (sixVertexEvenPositiveHalfProjection (s + k + 1)
        (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) =
      sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k :=
    sixVertexEvenSymmetricLift_projection (s + k + 1) hk.1.1.2.1
  have hpositive (j : Fin (s + k + 1)) :
      sixVertexEvenPositiveHalfProjection (s + k + 1)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) j ∈
        Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    rw [hlift]
    exact hk.1.1
  unfold sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue
  rw [<- sixVertexSymmetricBetheEigenvalueKernel_eq_value c _ hpositive]
  exact hk.1.2.2

theorem eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  exact hk.1.2.2

theorem eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq
    {c : Real} (hc : 2 < c) (s : Nat) :
    sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s =ᶠ[atTop]
      sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top hc s,
      eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top hc s]
      with k hkDensity hkCanonical
  rw [hkDensity, hkCanonical]

theorem eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq
    {c : Real} (hc : 2 < c) (s : Nat) :
    sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s =ᶠ[atTop]
      sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top hc s,
      eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top hc s]
      with k hkDensity hkCanonical
  rw [hkDensity, hkCanonical]

end
end StatMech.FrontierD
