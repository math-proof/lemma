/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem tendsto_vertexEndpointPolynomialBound :
    Filter.Tendsto vertexEndpointPolynomialBound Filter.atTop (nhds 0) := by
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
  unfold vertexEndpointPolynomialBound u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']
  ring

theorem vertexMarkedEndpointBarrier_le_polynomialBound
    (k : Nat)
    (source : FKIsingSquareFullVertexNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary
      ((k + 1) ^ 5) source))
    (hright : source.1 0 < (((k + 1) ^ 5 : Nat) : Int))
    (hbottom : -((((k + 1) ^ 5 : Nat) : Int)) < source.1 1)
    (htop : source.1 1 < (((k + 1) ^ 5 : Nat) : Int))
    (hlowerDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (fullVertexColumnIndex ((k + 1) ^ 5) source : Real) +
        (fullVertexRowIndex ((k + 1) ^ 5) source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      (fullVertexColumnIndex ((k + 1) ^ 5) source : Real) +
        (2 * ((k + 1) ^ 5) -
          fullVertexRowIndex ((k + 1) ^ 5) source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      vertexEndpointPolynomialBound k := by
  have hn : 0 < (k + 1) ^ 5 := by positivity
  have hdistance : (0 : Real) < (((k + 1) ^ 5 : Nat) : Real) / 2 := by
    positivity
  simpa [vertexEndpointPolynomialBound] using
    vertexMarkedEndpointBarrier_le_radiusDistance
      ((k + 1) ^ 5) (k + 1)
      ((((k + 1) ^ 5 : Nat) : Real) / 2)
      source hn hfixed hright hbottom htop hdistance
      hlowerDistance hupperDistance


theorem vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
    (k : Nat)
    (source : FKIsingSquareFullVertexNode ((k + 1) ^ 5))
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary
      ((k + 1) ^ 5) source))
    (hright : source.1 0 < (((k + 1) ^ 5 : Nat) : Int))
    (hbottom : -((((k + 1) ^ 5 : Nat) : Int)) < source.1 1)
    (htop : source.1 1 < (((k + 1) ^ 5 : Nat) : Int))
    (hhalf : ((((k + 1) ^ 5 : Nat) : Real) / 2) <=
      fullVertexColumnIndex ((k + 1) ^ 5) source) :
    vertexMarkedEndpointBarrier ((k + 1) ^ 5) (k + 1) (some source) <=
      vertexEndpointPolynomialBound k := by
  apply vertexMarkedEndpointBarrier_le_polynomialBound k source hfixed
    hright hbottom htop
  · have hrow : 0 <=
        (fullVertexRowIndex ((k + 1) ^ 5) source : Real) := by positivity
    have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    linarith
  · have hrow : 0 <=
        ((2 * ((k + 1) ^ 5) -
          fullVertexRowIndex ((k + 1) ^ 5) source : Nat) : Real) := by
      positivity
    have hrecip : 0 <= 1 / isingFermionicGhostCoefficient :=
      one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le
    linarith

theorem tendsto_four_mul_vertexEndpointPolynomialBound :
    Filter.Tendsto (fun k => 4 * vertexEndpointPolynomialBound k)
      Filter.atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul tendsto_vertexEndpointPolynomialBound

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
