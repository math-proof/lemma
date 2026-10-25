/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFiniteResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTaylor
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFiniteResidual


namespace StatMech.FrontierD

open Finset

noncomputable section

theorem sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeBetheOffset hc s k j =
      sixVertexEvenChargeOffsetBoundarySource hc s k j +
        ∑ l, (sixVertexTheta c
          (sixVertexEvenChargeAlignedHalfRoots hc s k j)
          (sixVertexEvenChargeAlignedHalfRoots hc s k l) -
        sixVertexTheta c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) := by
  rw [sixVertexEvenChargeBetheOffset_eq_thetaDifference]
  unfold sixVertexEvenChargeOffsetBoundarySource
    sixVertexEvenChargeAlignedHalfRoots
  rw [Finset.sum_sub_distrib]
  ring


theorem abs_sixVertexEvenChargeOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) (s k : Nat) {B : Real} (hB : 0 ≤ B)
    (hoffset : ∀ j, |sixVertexEvenChargeBetheOffset hc s k j| ≤ B)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexEvenChargeOffsetNodalResidual hc s k j| ≤
      4 * sixVertexThetaTaylorBound c * B ^ 2 /
        sixVertexFourWidth (2 * s) k := by
  let N := sixVertexFourWidth (2 * s) k
  let n := sixVertexFixedChargeBetheParticleCount (2 * s) k
  let p := sixVertexEvenChargeAlignedHalfRoots hc s k
  let q := sixVertexFixedChargeBetheRoots hc (2 * s) k
  let eps := sixVertexEvenChargeBetheOffset hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hn : n ≤ N := by
    have htwice := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
    dsimp [n, N]
    omega
  have hoffset' : ∀ l, |(N : Real) * (q l - p l)| ≤ B := by
    intro l
    simpa [N, q, p, eps, sixVertexEvenChargeAlignedHalfRoots,
      sixVertexEvenChargeBetheOffset] using hoffset l
  have htaylor := abs_sum_sixVertexTheta_sub_linearization_le
    hc hN hn hB hoffset' j
  let R : Fin n → Real := fun l =>
    sixVertexTheta c (p j) (p l) - sixVertexTheta c (q j) (q l) -
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) *
            (p j - q j) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) *
            (p l - q l))
  change |∑ l, R l| ≤ 4 * sixVertexThetaTaylorBound c * B ^ 2 / N at htaylor
  have hNreal : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hpoint (l : Fin n) :
      p l - q l = -(eps l) / N := by
    change p l - q l = -((N : Real) * (q l - p l)) / N
    field_simp [hNreal]
    ring
  have hcommon : eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j =
      ∑ l, (sixVertexTheta c (p j) (p l) -
        sixVertexTheta c (q j) (q l)) := by
    have h := sixVertexEvenChargeBetheOffset_eq_boundary_add_commonDifference
      hc s k j
    change eps j = sixVertexEvenChargeOffsetBoundarySource hc s k j +
      ∑ l, (sixVertexTheta c (p j) (p l) -
        sixVertexTheta c (q j) (q l)) at h
    linarith
  have hresidual : sixVertexEvenChargeOffsetNodalResidual hc s k j =
      ∑ l, R l := by
    change eps j - sixVertexEvenChargeOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
      ∑ l, R l
    rw [hcommon, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [R]
    rw [hpoint j, hpoint l]
    field_simp [hNreal]
    ring
  rw [hresidual]
  exact htaylor


end
end StatMech.FrontierD
