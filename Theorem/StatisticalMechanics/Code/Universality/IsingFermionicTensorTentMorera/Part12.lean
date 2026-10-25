/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part10


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem fkIsingExpandingSquareScale_mul_side (k : Nat) :
    fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k =
      (k + 1 : Nat) := by
  simp [fkIsingExpandingSquareScale, fkIsingExpandingSquareSide]
  field_simp


theorem fkIsingExpandingSquareScale_mul_side_tendsto_atTop :
    Tendsto (fun k =>
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
      atTop atTop := by
  simpa only [fkIsingExpandingSquareScale_mul_side] using
    ((tendsto_natCast_atTop_atTop (R := Real)).comp
      (tendsto_add_atTop_nat 1))

theorem fkIsingExpandingSquareScale_tendsto_zero :
    Tendsto fkIsingExpandingSquareScale atTop (nhds 0) := by
  have hadd : Tendsto (fun k : Nat => k + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hinv : Tendsto (fun k : Nat => (1 : Real) / (k + 1 : Nat))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat.comp hadd
  change Tendsto (fun k : Nat => (1 : Real) / (k + 1 : Nat))
    atTop (nhds 0)
  exact hinv


theorem fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop
    (layers : Real) :
    Tendsto (fun k =>
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k -
        layers * fkIsingExpandingSquareScale k) atTop atTop := by
  have hsmall : Tendsto (fun k =>
      -(layers * fkIsingExpandingSquareScale k)) atTop (nhds 0) := by
    simpa using
      (fkIsingExpandingSquareScale_tendsto_zero.const_mul layers).neg
  simpa [sub_eq_add_neg] using Filter.Tendsto.atTop_add
    fkIsingExpandingSquareScale_mul_side_tendsto_atTop hsmall

theorem fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
    (R layers : Real) :
    ∀ᶠ k in atTop,
      R ≤ fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k -
        layers * fkIsingExpandingSquareScale k :=
  (tendsto_atTop.1
    (fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop layers)) R


end
end StatMech.Universality
