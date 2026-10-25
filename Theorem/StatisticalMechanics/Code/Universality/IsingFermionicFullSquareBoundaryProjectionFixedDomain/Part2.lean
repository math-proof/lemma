/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain.Part2


namespace StatMech.Universality

open Filter Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) *
        isingFermionicFixedDiamondMesh k) atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 2)
  have hu : Tendsto u atTop (nhds 0) := by
    let v : Nat -> Real := fun k => 1 / ((k : Real) + 1)
    have hv : Tendsto v atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := hv.comp (tendsto_add_atTop_nat 1)
    convert hcomp using 1
    funext k
    dsimp [u, v, Function.comp_def]
    push_cast
    ring
  have hCu : Tendsto (fun k => (C : Real) * u k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hu
  convert hCu using 1
  funext k
  have hL :
      (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) =
        (C : Real) * ((k : Real) + 2) ^ 4 := by
    change (C : Real) * ((((k + 2 : Nat) : Real) ^ 4)) = _
    push_cast
    ring
  rw [hL, isingFermionicFixedDiamondMesh_eq_inv_pow]
  dsimp [u]
  have hk : (0 : Real) < (k : Real) + 2 := by positivity
  field_simp [hk.ne']


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
