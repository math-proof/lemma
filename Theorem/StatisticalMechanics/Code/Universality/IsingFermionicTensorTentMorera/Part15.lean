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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part13


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialAxisSnapWidth_mul_mesh_le
    (mesh : Real) (z w : Complex) (hmesh : 0 < mesh)
    (hre : z.re ≤ w.re) :
    (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh ≤
      w.re - z.re + mesh := by
  have hadd := shiftedRealGridFloor_add_steps
    mesh (1 / 2) z.re w.re hmesh hre
  have hz := shiftedRealGridFloor_error mesh (1 / 2) z.re hmesh
  have hw := shiftedRealGridFloor_error mesh (1 / 2) w.re hmesh
  unfold reflectedRadialAxisSnapWidth
  nlinarith

theorem reflectedRadialAxisSnapHeight_mul_mesh_le
    (mesh : Real) (z w : Complex) (hmesh : 0 < mesh)
    (him : z.im ≤ w.im) :
    (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh ≤
      w.im - z.im + mesh := by
  have hadd := shiftedRealGridFloor_add_steps
    mesh 0 z.im w.im hmesh him
  have hz := shiftedRealGridFloor_error mesh 0 z.im hmesh
  have hw := shiftedRealGridFloor_error mesh 0 w.im hmesh
  unfold reflectedRadialAxisSnapHeight
  nlinarith


theorem reflectedRadialAxisSnap_oppositeCorner
    (mesh : Real) (z w : Complex) (hmesh : 0 < mesh)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    (shiftedRealGridFloor mesh (1 / 2) z.re +
        (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh : Real) +
      (shiftedRealGridFloor mesh 0 z.im +
        (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh : Real) *
        Complex.I =
      reflectedRadialAxisSnap mesh w := by
  unfold reflectedRadialAxisSnapWidth reflectedRadialAxisSnapHeight
    reflectedRadialAxisSnap
  rw [shiftedRealGridFloor_add_steps mesh (1 / 2) z.re w.re hmesh hre,
    shiftedRealGridFloor_add_steps mesh 0 z.im w.im hmesh him]

theorem reflectedRadialAxisSnap_dist_lt
    (mesh : Real) (z : Complex) (hmesh : 0 < mesh) :
    dist (reflectedRadialAxisSnap mesh z) z < 2 * mesh := by
  rw [dist_eq_norm]
  have hre := abs_shiftedRealGridFloor_sub_lt mesh (1 / 2) z.re hmesh
  have him := abs_shiftedRealGridFloor_sub_lt mesh 0 z.im hmesh
  calc
    norm (reflectedRadialAxisSnap mesh z - z) ≤
        |(reflectedRadialAxisSnap mesh z - z).re| +
          |(reflectedRadialAxisSnap mesh z - z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |shiftedRealGridFloor mesh (1 / 2) z.re - z.re| +
        |shiftedRealGridFloor mesh 0 z.im - z.im| := by
      simp [reflectedRadialAxisSnap]
    _ < 2 * mesh := by linarith

theorem reflectedRadialAxisSnap_tendsto
    (mesh : Nat -> Real) (hmeshPos : ∀ k, 0 < mesh k)
    (hmesh : Tendsto mesh atTop (nhds 0)) (z : Complex) :
    Tendsto (fun k => reflectedRadialAxisSnap (mesh k) z)
      atTop (nhds z) := by
  unfold reflectedRadialAxisSnap
  have hre := shiftedRealGridFloor_tendsto mesh hmeshPos hmesh (1 / 2) z.re
  have him := shiftedRealGridFloor_tendsto mesh hmeshPos hmesh 0 z.im
  simpa only [Complex.re_add_im] using
    hre.ofReal.add (him.ofReal.mul_const Complex.I)


end
end StatMech.Universality
