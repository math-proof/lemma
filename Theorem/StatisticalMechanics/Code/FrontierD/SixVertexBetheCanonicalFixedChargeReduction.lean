/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualOddPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEventuallyFixedChargeBethePerronIdentification_of_even
    {c : Real} (hc : 2 < c) (s : Nat)
    (h : SixVertexEventuallyEvenChargeBethePerronIdentification hc s) :
    SixVertexEventuallyFixedChargeBethePerronIdentification hc (2 * s) := by
  filter_upwards [h] with k hk
  unfold sixVertexFixedChargeBetheEigenvalueValue
  rw [dif_pos ⟨s, by ring⟩]
  simpa using hk

theorem sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd
    {c : Real} (hc : 2 < c) (s : Nat)
    (h : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s k =
        sixVertexLambdaAlongFour c (2 * s + 1) k) :
    SixVertexEventuallyFixedChargeBethePerronIdentification hc
      (2 * s + 1) := by
  filter_upwards [h] with k hk
  unfold sixVertexFixedChargeBetheEigenvalueValue
  rw [dif_neg (Nat.not_even_iff_odd.2 ⟨s, rfl⟩)]
  simpa using hk


theorem sixVertexEventuallyFixedChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (r : Nat) :
    SixVertexEventuallyFixedChargeBethePerronIdentification hc r := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨s, rfl⟩ := hr
    have heven : SixVertexEventuallyEvenChargeBethePerronIdentification hc s := by
      filter_upwards
        [eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top
          hc s]
      with k hk
      rw [hk]
      unfold sixVertexLambdaAlongFour sixVertexLambda sixVertexFourWidth
      congr 1 <;> omega
    simpa [two_mul] using
      (sixVertexEventuallyFixedChargeBethePerronIdentification_of_even
        hc s heven)
  · obtain ⟨s, rfl⟩ := hr
    apply sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd hc s
    filter_upwards
      [eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top
        hc s]
        with k hk
    rw [hk]
    unfold sixVertexLambdaAlongFour sixVertexLambda sixVertexFourWidth
    congr 1 <;> omega


end
end StatMech.FrontierD
