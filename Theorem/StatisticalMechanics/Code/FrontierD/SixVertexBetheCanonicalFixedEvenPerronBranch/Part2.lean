/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexCanonicalFixedEvenChargeContinuationPoint_projection
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexCanonicalFixedEvenChargeContinuationPoint ha hc s k) =
        ⟨c, hc⟩ := rfl

theorem sixVertexFiniteRootDensity_fixedEvenCharge_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) (x : Real) :
    sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1))
        (sixVertexFixedEvenChargeBetheRoots hc s k) x =
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) x := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
    fun j => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k j) /
      sixVertexThetaDerivativeDenominator c x
        (sixVertexFixedChargeBetheRoots hc (2 * s) k j)
  have hsum : (∑ j, f j) = ∑ j, f (e j) := by
    simpa using (Equiv.sum_comp e f).symm
  unfold sixVertexFiniteRootDensity
  rw [show (∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
      (sixVertexFixedEvenChargeBetheRoots hc s k j) /
        sixVertexThetaDerivativeDenominator c x
          (sixVertexFixedEvenChargeBetheRoots hc s k j)) = ∑ j, f j by
    simpa [sixVertexFixedEvenChargeBetheRoots, e, f] using hsum.symm]

theorem sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) (rho : C(Real, Real)) :
    sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1))
        (sixVertexFixedEvenChargeBetheRoots hc s k) rho =
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) rho := by
  unfold sixVertexWeightedFiniteDensityGauge
  congr 1
  apply ContinuousMap.ext
  intro x
  simp only [sixVertexWeightedFiniteDensityDifference, ContinuousMap.coe_mk]
  rw [sixVertexFiniteRootDensity_fixedEvenCharge_canonical hc s k x]

theorem sixVertexCoordinateBetheWave_finCast_ne_zero
    {N n m : Nat} (h : n = m) (c : Real) (p : Fin n → Real)
    (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
        (fun i : Fin m => p (Fin.cast h.symm i)) ≠ 0 := by
  subst m
  simpa using hwave

theorem sixVertexSectorTopEigenvalue_eq_of_finCast
    {N n m : Nat} (h : n = m) (hn : n ≤ N) (hm : m ≤ N)
    (c value : Real)
    (hv : value = sixVertexSectorTopEigenvalue N n hn c) :
    value = sixVertexSectorTopEigenvalue N m hm c := by
  subst m
  simpa using hv


end
end StatMech.FrontierD
