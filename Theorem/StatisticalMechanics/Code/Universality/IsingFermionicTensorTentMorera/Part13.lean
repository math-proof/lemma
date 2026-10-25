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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part11


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem shiftedRealGridFloor_error
    (mesh shift x : Real) (hmesh : 0 < mesh) :
    0 ≤ x - shiftedRealGridFloor mesh shift x ∧
      x - shiftedRealGridFloor mesh shift x < mesh := by
  let q : Int := ⌊x / mesh - shift⌋
  have hlo : (q : Real) ≤ x / mesh - shift := by
    exact_mod_cast Int.floor_le (x / mesh - shift)
  have hhi : x / mesh - shift < (q : Real) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (x / mesh - shift)
  unfold shiftedRealGridFloor
  change 0 ≤ x - mesh * ((q : Real) + shift) ∧
    x - mesh * ((q : Real) + shift) < mesh
  constructor <;> (field_simp at hlo hhi ⊢ <;> nlinarith)

theorem abs_shiftedRealGridFloor_sub_lt
    (mesh shift x : Real) (hmesh : 0 < mesh) :
    |shiftedRealGridFloor mesh shift x - x| < mesh := by
  have h := shiftedRealGridFloor_error mesh shift x hmesh
  rw [abs_lt]
  constructor <;> linarith


theorem shiftedRealGridFloor_mono
    (mesh shift x y : Real) (hmesh : 0 < mesh) (hxy : x ≤ y) :
    shiftedRealGridFloor mesh shift x ≤
      shiftedRealGridFloor mesh shift y := by
  unfold shiftedRealGridFloor
  apply mul_le_mul_of_nonneg_left _ hmesh.le
  gcongr


end
end StatMech.Universality
