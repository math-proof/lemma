/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem tendsto_faceEndpointPolynomialBound :
    Filter.Tendsto faceEndpointPolynomialBound Filter.atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hrhs : Filter.Tendsto
      (fun k => 4 * (1 + u k) ^ 2 *
        (1 + (1 / isingFermionicGhostCoefficient) * u k) * u k)
      Filter.atTop (nhds 0) := by
    convert (((tendsto_const_nhds.mul
      ((tendsto_const_nhds.add hu).pow 2)).mul
        (tendsto_const_nhds.add (tendsto_const_nhds.mul hu))).mul hu) using 1
    norm_num
  convert hrhs using 1
  funext k
  unfold faceEndpointPolynomialBound u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']
  ring

theorem faceMarkedEndpointBarrier_le_polynomialBound
    (k : Nat)
    (source : FKIsingSquareFullFaceNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary ((k + 1) ^ 5) source))
    (hleft : 0 < source.1.1)
    (hlowerDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (source.2.1 : Real))
    (hupperDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (source.1.1 : Real) + 1 / isingFermionicGhostCoefficient +
        (2 * ((k + 1) ^ 5) - 1 - source.2.1 : Nat)) :
    faceMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      faceEndpointPolynomialBound k := by
  have hdistance : (0 : Real) < (((k + 1) ^ 5 : Nat) : Real) / 2 := by
    positivity
  simpa [faceEndpointPolynomialBound] using
    faceMarkedEndpointBarrier_le_radiusDistance
      ((k + 1) ^ 5) (k + 1)
      ((((k + 1) ^ 5 : Nat) : Real) / 2)
      source hfixed hleft hdistance hlowerDistance hupperDistance


theorem faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
    (k : Nat)
    (source : FKIsingSquareFullFaceNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullFaceFixedBoundary ((k + 1) ^ 5) source))
    (hhalf : ((((k + 1) ^ 5 : Nat) : Real) / 2) <= source.1.1) :
    faceMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      faceEndpointPolynomialBound k := by
  have hleft : 0 < source.1.1 := by
    by_contra h
    have hz : source.1.1 = 0 := Nat.eq_zero_of_not_pos h
    have hN : (0 : Real) < ((k : Real) + 1) ^ 5 / 2 := by
      positivity
    simp [hz] at hhalf
    linarith
  apply faceMarkedEndpointBarrier_le_polynomialBound k source hfixed hleft
  · have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    have hy : 0 <= (source.2.1 : Real) := Nat.cast_nonneg _
    linarith
  · have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    have hy : 0 <= ((2 * ((k + 1) ^ 5) - 1 - source.2.1 : Nat) : Real) :=
      Nat.cast_nonneg _
    linarith

theorem tendsto_four_mul_faceEndpointPolynomialBound :
    Filter.Tendsto (fun k => 4 * faceEndpointPolynomialBound k)
      Filter.atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul tendsto_faceEndpointPolynomialBound

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
