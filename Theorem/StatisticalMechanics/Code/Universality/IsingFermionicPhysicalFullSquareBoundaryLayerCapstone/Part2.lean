/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem bottomBoundaryProjectionReconstruction_projection_west
    (west north : Complex)
    (hwest : (starRingEnd Complex) west = west)
    (hnorth : (starRingEnd Complex) north = -Complex.I * north) :
    isingProj 1 (bottomBoundaryProjectionReconstruction west north) = west := by
  unfold bottomBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_sub, map_add, map_one,
    Complex.conj_I, hwest, hnorth]
  norm_num
  ring_nf
  have hI2 : Complex.I ^ 2 = -1 := by norm_num [Complex.I_sq]
  rw [hI2]
  ring

theorem bottomBoundaryProjectionReconstruction_projection_north
    (west north : Complex)
    (hwest : (starRingEnd Complex) west = west)
    (hnorth : (starRingEnd Complex) north = -Complex.I * north) :
    isingProj (-Complex.I)
        (bottomBoundaryProjectionReconstruction west north) = north := by
  unfold bottomBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_sub, map_add, map_one,
    map_neg, Complex.conj_I, hwest, hnorth]
  norm_num
  have hI2 : Complex.I ^ 2 = -1 := by norm_num [Complex.I_sq]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, hI2]
    ring
  ring_nf
  rw [hI2, hI3]
  ring


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
