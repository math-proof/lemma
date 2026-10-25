/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem norm_sixVertexFixedOddChargeBetheEigenvalueCandidate
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    ‖sixVertexFixedOddChargeBetheEigenvalueCandidate hc r k‖ =
      sixVertexFixedOddChargeBetheEigenvalueValue hc r k := by
  exact norm_sixVertexZeroPhaseBetheEigenvalueCandidate hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)


theorem sixVertexFixedOddChargeBethePrefactor_div_width_eq
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k) /
          (sixVertexFourWidth r k : Real) =
      c ^ 2 * (1 +
        (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real)) := by
  rw [sixVertexZeroPhaseBethePrefactor_eq hc _ _ _
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)]
  have hN : (sixVertexFourWidth r k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos r k).ne'
  field_simp [hN]

theorem sixVertexFixedOddChargeBethePrefactor_bounds
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    c ^ 2 * (2 * (r : Real)) <
        sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheRoots hc r k)
          (sixVertexFixedChargeBetheCentralIndex r k) ∧
      sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheRoots hc r k)
          (sixVertexFixedChargeBetheCentralIndex r k) <=
        c ^ 2 * (sixVertexFourWidth r k : Real) := by
  have hb := sixVertexZeroPhaseBethePrefactor_bounds
    (N := sixVertexFourWidth r k) hc
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)
  have hcount : (sixVertexFourWidth r k : Real) -
      2 * (sixVertexFixedChargeBetheParticleCount r k : Real) =
        2 * (r : Real) := by
    rw [sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    ring
  rwa [hcount] at hb


theorem sixVertexFixedOddChargeEmpiricalThetaDerivative_bounds
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    -(1 : Real) + 2 * (r : Real) / (sixVertexFourWidth r k : Real) <
        (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) ∧
      (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) <= 0 := by
  have hb := sixVertexFixedOddChargeBethePrefactor_bounds hc hr k
  have heq := sixVertexFixedOddChargeBethePrefactor_div_width_eq hc hr k
  have hN : (0 : Real) < sixVertexFourWidth r k := by
    exact_mod_cast sixVertexFourWidth_pos r k
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  constructor
  · rw [← sub_pos, show
        (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) -
          (-(1 : Real) + 2 * (r : Real) /
            (sixVertexFourWidth r k : Real)) =
        (1 + (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real)) -
          2 * (r : Real) / (sixVertexFourWidth r k : Real) by ring]
    have hdiv := div_lt_div_of_pos_right hb.1 hN
    rw [heq] at hdiv
    have hdiv' : c ^ 2 *
          (2 * (r : Real) / (sixVertexFourWidth r k : Real)) <
        c ^ 2 * (1 + (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real)) := by
      convert hdiv using 1 <;> ring
    have hcancel : 2 * (r : Real) / (sixVertexFourWidth r k : Real) <
        1 + (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) :=
      lt_of_mul_lt_mul_left hdiv' hc2.le
    exact sub_pos.mpr hcancel
  · have hneg (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
        sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j) <= 0 :=
      (sixVertexThetaLeftDerivAtZero_neg hc _).le
    exact div_nonpos_of_nonpos_of_nonneg
      (Finset.sum_nonpos fun j hj => hneg j) hN.le

theorem sixVertexFixedOddChargeBetheEigenvalueValue_pos
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    0 < sixVertexFixedOddChargeBetheEigenvalueValue hc r k := by
  exact sixVertexZeroPhaseBetheEigenvalueValue_pos hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)

theorem sixVertexFixedOddChargeBetheEigenvalueValue_log
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    Real.log (sixVertexFixedOddChargeBetheEigenvalueValue hc r k) =
      Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k)) +
      ∑ j ∈ (Finset.univ.erase
          (sixVertexFixedChargeBetheCentralIndex r k)),
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j))‖ := by
  exact sixVertexZeroPhaseBetheEigenvalueValue_log hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)

end
end StatMech.FrontierD
