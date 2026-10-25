/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargePerronClosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddUniqueStabilitySheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeEventualPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenChargePerronClosed.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargePerronClosed
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEventuallySelectedFixedChargeBethePerronIdentification_of_densityTail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexSelectedFixedChargeBetheEigenvalueValue hc r k =
        sixVertexLambdaAlongFour c r k := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨s, rfl⟩ := hr
    filter_upwards
      [sixVertexEventuallyEvenChargeBethePerronIdentification_of_densityTail
        hc htail s] with k hk
    unfold sixVertexSelectedFixedChargeBetheEigenvalueValue
    rw [dif_pos ⟨s, by omega⟩]
    have hadd : s + s = 2 * s := by omega
    have hhalf : (2 * s) / 2 = s := by omega
    simpa only [hadd, hhalf] using hk
  · obtain ⟨s, rfl⟩ := hr
    filter_upwards
      [sixVertexEventuallyOddChargeBethePerronIdentification_of_densityTail
        hc htail s] with k hk
    unfold sixVertexSelectedFixedChargeBetheEigenvalueValue
    rw [dif_neg (Nat.not_even_iff_odd.mpr ⟨s, rfl⟩)]
    simpa using hk

end
end StatMech.FrontierD
