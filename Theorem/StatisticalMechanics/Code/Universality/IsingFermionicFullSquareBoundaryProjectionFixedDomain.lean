/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain


namespace StatMech.Universality

open Filter Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFermionicFixedDiamondMesh_nonneg (k : Nat) :
    0 <= isingFermionicFixedDiamondMesh k := by
  unfold isingFermionicFixedDiamondMesh
  positivity

theorem isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh
    (k : Nat) :
    (isingFermionicProjectionPolynomialSide k : Real) *
        isingFermionicFixedDiamondMesh k = 1 := by
  unfold isingFermionicFixedDiamondMesh
  field_simp [ne_of_gt (isingFermionicProjectionPolynomialSide_pos k)]

theorem isingFermionicFixedDiamondMesh_eq_inv_pow (k : Nat) :
    isingFermionicFixedDiamondMesh k =
      (1 / ((k : Real) + 2)) ^ 5 := by
  unfold isingFermionicFixedDiamondMesh
    isingFermionicProjectionPolynomialSide
    isingFermionicPolynomialSide
  push_cast
  rw [one_div_pow]
  congr 2
  ring

theorem tendsto_isingFermionicFixedDiamondMesh :
    Tendsto isingFermionicFixedDiamondMesh atTop (nhds 0) := by
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
  have hu5 : Tendsto (fun k => u k ^ 5) atTop (nhds 0) := by
    simpa using hu.pow 5
  convert hu5 using 1
  funext k
  exact isingFermionicFixedDiamondMesh_eq_inv_pow k

theorem tendsto_isingFermionicFixedDiamondMesh_fourthOrder :
    Tendsto (fun k =>
      |isingFermionicFixedDiamondMesh k| ^ 4 *
        (isingFermionicProjectionPolynomialSide k : Real) ^ 2)
      atTop (nhds 0) := by
  have hsq : Tendsto (fun k => isingFermionicFixedDiamondMesh k ^ 2)
      atTop (nhds 0) := by
    simpa using tendsto_isingFermionicFixedDiamondMesh.pow 2
  convert hsq using 1
  funext k
  have hnonneg := isingFermionicFixedDiamondMesh_nonneg k
  have hmul :=
    isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k
  rw [abs_of_nonneg hnonneg]
  calc
    isingFermionicFixedDiamondMesh k ^ 4 *
          (isingFermionicProjectionPolynomialSide k : Real) ^ 2 =
        ((isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k) ^ 2 *
            isingFermionicFixedDiamondMesh k ^ 2 := by ring
    _ = isingFermionicFixedDiamondMesh k ^ 2 := by rw [hmul]; norm_num

theorem
    tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
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
  have hCu3 : Tendsto (fun k => (C : Real) * u k ^ 3)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hu.pow 3)
  convert hCu3 using 1
  funext k
  have hL :
      (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) =
        (C : Real) * ((k : Real) + 2) ^ 2 := by
    change (C : Real) * ((((k + 1 + 1 : Nat) : Real) ^ 2)) = _
    push_cast
    ring
  rw [hL, isingFermionicFixedDiamondMesh_eq_inv_pow]
  dsimp [u]
  have hk : (0 : Real) < (k : Real) + 2 := by positivity
  field_simp [hk.ne']


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
