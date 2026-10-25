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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part12


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem shiftedRealGridFloor_add_steps
    (mesh shift x y : Real) (hmesh : 0 < mesh) (hxy : x ≤ y) :
    shiftedRealGridFloor mesh shift x +
        (shiftedRealGridFloorSteps mesh shift x y : Real) * mesh =
      shiftedRealGridFloor mesh shift y := by
  let qx : Int := ⌊x / mesh - shift⌋
  let qy : Int := ⌊y / mesh - shift⌋
  have hq : qx ≤ qy := by
    apply Int.floor_mono
    exact sub_le_sub_right (div_le_div_of_nonneg_right hxy hmesh.le) shift
  have hcast : (Int.toNat (qy - qx) : Int) = qy - qx :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hq)
  have hcastR : (Int.toNat (qy - qx) : Real) = (qy : Real) - (qx : Real) := by
    exact_mod_cast hcast
  unfold shiftedRealGridFloor shiftedRealGridFloorSteps
  change mesh * ((qx : Real) + shift) +
      (Int.toNat (qy - qx) : Real) * mesh =
    mesh * ((qy : Real) + shift)
  rw [hcastR]
  ring

theorem shiftedRealGridFloor_tendsto
    (mesh : Nat -> Real) (hmeshPos : ∀ k, 0 < mesh k)
    (hmesh : Tendsto mesh atTop (nhds 0)) (shift x : Real) :
    Tendsto (fun k => shiftedRealGridFloor (mesh k) shift x)
      atTop (nhds x) := by
  rw [Metric.tendsto_atTop] at hmesh ⊢
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hmesh epsilon hepsilon
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  have hkMesh : mesh k < epsilon := by
    simpa [Real.dist_eq, abs_of_pos (hmeshPos k)] using hN k hk
  exact (abs_shiftedRealGridFloor_sub_lt
    (mesh k) shift x (hmeshPos k)).trans hkMesh


end
end StatMech.Universality
