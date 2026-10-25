/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part13


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem isingPrimalProjectionDivergenceWithoutWest_left_add_ghost_nonneg
    (north east south : Complex)
    (hNE : isingProj (-1) north = isingProj (-1) east)
    (hES : isingProj (-Complex.I) east =
      isingProj (-Complex.I) south)
    (hphase : isingProj 1 south =
      isingLambda * isingProj Complex.I north) :
    0 ≤ isingPrimalProjectionDivergenceWithoutWest north east south -
      isingFermionicGhostCoefficient *
        Complex.normSq (isingProj Complex.I north) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  have hsqrtCube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hsqrtSq]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hghost : isingFermionicGhostCoefficient = 2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  rw [hghost]
  simp [isingPrimalProjectionDivergenceWithoutWest, isingProj,
    Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, hsqrt_ne] at hNE hES hphase ⊢
  field_simp [hsqrt_ne] at hphase ⊢
  have hei : east.im = north.im := by linarith [hNE]
  have her : east.re = south.re + south.im - north.im := by
    linarith [hES.1]
  have hp := congrArg (fun z : Real => Real.sqrt 2 * z) hphase.1
  have hnr : north.re = north.im + Real.sqrt 2 * south.re := by
    dsimp at hp
    ring_nf at hp
    rw [hsqrtSq] at hp
    linarith
  rw [hei, her, hnr]
  ring_nf
  rw [hsqrtSq, hsqrtCube]
  nlinarith [sq_nonneg (south.im - north.im),
    sq_nonneg (north.im + (Real.sqrt 2 - 1) * south.re)]

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
