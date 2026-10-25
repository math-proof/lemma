/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFixedOddChargeBetheContinuationPoint_projection
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexFixedOddChargeBetheContinuationPoint ha hc s k) = ⟨c, hc⟩ := rfl

theorem sixVertexFiniteRootDensity_fixedOddCharge_eq
    {c : Real} (hc : 2 < c) (s k : Nat) (x : Real) :
    sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexFixedOddChargeBetheRoots hc s k) x =
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x := by
  let e : Fin (((s + k + 1) + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) :=
    (Fin.castOrderIso
      (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm).toEquiv
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
    fun j => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) /
      sixVertexThetaDerivativeDenominator c x
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)
  have hsum : (∑ j, f j) = ∑ j, f (e j) := by
    simpa using (Equiv.sum_comp e f).symm
  have heqsum : (∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
      (sixVertexFixedOddChargeBetheRoots hc s k j) /
        sixVertexThetaDerivativeDenominator c x
          (sixVertexFixedOddChargeBetheRoots hc s k j)) =
      ∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) /
          sixVertexThetaDerivativeDenominator c x
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) := by
    simpa [sixVertexFixedOddChargeBetheRoots, e, f] using hsum.symm
  unfold sixVertexFiniteRootDensity
  rw [heqsum]

theorem sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq
    {c : Real} (hc : 2 < c) (s k : Nat) (rho : C(Real, Real)) :
    sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexFixedOddChargeBetheRoots hc s k) rho =
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) rho := by
  unfold sixVertexWeightedFiniteDensityGauge
  congr 1
  apply ContinuousMap.ext
  intro x
  simp only [sixVertexWeightedFiniteDensityDifference, ContinuousMap.coe_mk]
  rw [sixVertexFiniteRootDensity_fixedOddCharge_eq hc s k x]

theorem tendsto_sixVertexFixedOddChargeContinuationGauge_tail
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (s : Nat) :
    Tendsto (fun k : Nat =>
      sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexFixedOddChargeBetheContinuationPoint ha hc s k))
      atTop (nhds 0) := by
  have h := tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail
    (ha.trans_le hc.1) htail (2 * s + 1)
  apply h.congr'
  filter_upwards with k
  symm
  change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc.1)
      (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1))
      (sixVertexFixedOddChargeBetheRoots (ha.trans_le hc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hc⟩) = _
  rw [sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq]
  congr 2

end
end StatMech.FrontierD
