/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence


namespace StatMech.Universality

open Filter

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFermionicPolynomialSide_pos (k : Nat) :
    0 < isingFermionicPolynomialSide k := by
  unfold isingFermionicPolynomialSide
  positivity

theorem isingFermionicPolynomialMesh_nonneg (k : Nat) :
    0 <= isingFermionicPolynomialMesh k := by
  unfold isingFermionicPolynomialMesh
  positivity

theorem tendsto_isingFermionicPolynomialMesh :
    Tendsto isingFermionicPolynomialMesh atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu3 : Tendsto (fun k => u k ^ 3) atTop (nhds 0) := by
    simpa using hu.pow 3
  convert hu3 using 1
  funext k
  unfold isingFermionicPolynomialMesh u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']

theorem tendsto_isingFermionicPolynomialMesh_fourthOrder :
    Tendsto (fun k =>
      |isingFermionicPolynomialMesh k| ^ 4 *
        (isingFermionicPolynomialSide k : Real) ^ 2)
      atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu2 : Tendsto (fun k => u k ^ 2) atTop (nhds 0) := by
    simpa using hu.pow 2
  convert hu2 using 1
  funext k
  unfold isingFermionicPolynomialMesh isingFermionicPolynomialSide u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  rw [abs_of_nonneg (by positivity :
    0 <= 1 / ((((k + 1 : Nat) : Real)) ^ 3))]
  push_cast
  field_simp [hk.ne']


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
