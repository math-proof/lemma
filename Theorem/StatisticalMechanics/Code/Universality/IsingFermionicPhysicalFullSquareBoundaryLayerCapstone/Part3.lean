/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part2


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem rightBoundaryProjectionReconstruction_projection_north
    (north west : Complex)
    (hnorth : (starRingEnd Complex) north = -north)
    (hwest : (starRingEnd Complex) west = -Complex.I * west) :
    isingProj (-1) (rightBoundaryProjectionReconstruction north west) =
      north := by
  unfold rightBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one,
    Complex.conj_I, map_neg, hnorth, hwest]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
  ring

theorem rightBoundaryProjectionReconstruction_projection_west
    (north west : Complex)
    (hnorth : (starRingEnd Complex) north = -north)
    (hwest : (starRingEnd Complex) west = -Complex.I * west) :
    isingProj (-Complex.I)
        (rightBoundaryProjectionReconstruction north west) = west := by
  unfold rightBoundaryProjectionReconstruction isingProj
  rw [map_add, map_mul, map_mul, map_add, map_sub, map_one,
    Complex.conj_I, map_neg, hnorth, hwest]
  norm_num
  ring_nf
  rw [show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq],
    show Complex.I ^ 3 = -Complex.I by
      rw [show (3 : Nat) = 2 + 1 by omega, pow_succ,
        show Complex.I ^ 2 = -1 by norm_num [Complex.I_sq]]
      ring]
  ring


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
