/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedSectorPairMass_eq_coeff
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    sixVertexMarkedSectorPairMass T left right k =
      (sixVertexShiftedSectorTracePolynomial T.width T.height left.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height right.val).coeff k := by
  rw [← sixVertexMarkedSectorConfigurationPolynomial_eq_trace T left,
    ← sixVertexMarkedSectorConfigurationPolynomial_eq_trace T right]
  unfold sixVertexMarkedSectorPairMass sixVertexMarkedPairMultiplicity
  unfold sixVertexMarkedSectorConfigurationPolynomial
  have hpoly :
      (∑ omega : SixVertexMarkedSectorConfiguration T left,
          sixVertexTorusMarkedWeight omega.1) *
        (∑ eta : SixVertexMarkedSectorConfiguration T right,
          sixVertexTorusMarkedWeight eta.1) =
      ∑ pair : SixVertexMarkedSectorConfiguration T left ×
          SixVertexMarkedSectorConfiguration T right,
        sixVertexTorusMarkedWeight pair.1.1 *
          sixVertexTorusMarkedWeight pair.2.1 := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Fintype.sum_prod_type]
  rw [hpoly]
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]

theorem sixVertexMarkedPairMultiplicity_nonneg
    {T : EvenTorus}
    (omega eta : SixVertexArrows T)
    (homega : omega.IceRule) (heta : eta.IceRule) (k : Nat) :
    0 <= sixVertexMarkedPairMultiplicity omega eta k := by
  unfold sixVertexMarkedPairMultiplicity
  apply Polynomial.coeffNonnegative_mul
  · rw [sixVertexTorusMarkedWeight_eq_pow omega homega]
    exact Polynomial.coeffNonnegative_pow
      Polynomial.coeffNonnegative_two_add_X _
  · rw [sixVertexTorusMarkedWeight_eq_pow eta heta]
    exact Polynomial.coeffNonnegative_pow
      Polynomial.coeffNonnegative_two_add_X _


end
end StatMech.FrontierD
