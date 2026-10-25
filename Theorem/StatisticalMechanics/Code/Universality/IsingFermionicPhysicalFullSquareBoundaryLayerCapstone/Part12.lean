/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part11


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem isingPrimalProjectionDivergenceWithoutEast_right_decomposition
    (north south west : Complex)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    isingPrimalProjectionDivergenceWithoutEast north south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-Complex.I) west) =
      -2 * Complex.normSq (isingProj (-Complex.I) west) -
        Complex.normSq (isingProj (-1) north) -
        Complex.normSq (isingProj (-Complex.I) south) := by
  have hsame : Complex.normSq (isingProj (-1) west) =
      Complex.normSq (isingProj (-Complex.I) west) := by
    have hlam : Complex.normSq isingLambda = 1 := by
      rw [isingLambda_val]
      norm_num [Complex.normSq_apply]
    rw [hphase, Complex.normSq_mul, Complex.normSq_neg,
      hlam, one_mul]
  have hfar : Complex.normSq (isingProj Complex.I west) =
      (3 + 2 * Real.sqrt 2) *
        Complex.normSq (isingProj (-Complex.I) west) := by
    rw [isingLambda_val] at hphase
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
    simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
      Complex.div_re, Complex.div_im] at hphase ⊢
    field_simp at hphase ⊢
    have hlinear : Real.sqrt 2 * west.re +
        (Real.sqrt 2 + 2) * west.im = 0 := by
      linarith [hphase.2]
    have hprod : Real.sqrt 2 *
        (west.re + (1 + Real.sqrt 2) * west.im) = 0 := by
      calc
        _ = Real.sqrt 2 * west.re +
            (Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 2) * west.im := by ring
        _ = Real.sqrt 2 * west.re +
            (Real.sqrt 2 + 2) * west.im := by rw [hsqrt]
        _ = 0 := hlinear
    have hWx : west.re = -(1 + Real.sqrt 2) * west.im := by
      have hz := (mul_eq_zero.mp hprod).resolve_left hsqrt_ne
      linarith
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
    have hsq3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = _ := by rw [hsq2]
    rw [hWx]
    ring_nf
    rw [hsq2, hsq3]
    ring
  have hpairS_I := isingProj_normSq_add_neg Complex.I south (by norm_num)
  have hpairS_one := isingProj_normSq_add_neg 1 south (by norm_num)
  have hS : Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj 1 south) =
      Complex.normSq (isingProj (-1) west) -
        Complex.normSq (isingProj (-Complex.I) south) := by
    rw [← hSW]
    linarith
  have hWNnorm := congrArg Complex.normSq hWN
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  unfold isingPrimalProjectionDivergenceWithoutEast
  rw [hghost]
  nlinarith [hS, hWNnorm, hsame, hfar]

theorem isingPrimalProjectionDivergenceWithoutEast_right_add_ghost_nonpos
    (north south west : Complex)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    isingPrimalProjectionDivergenceWithoutEast north south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-Complex.I) west) ≤ 0 := by
  rw [isingPrimalProjectionDivergenceWithoutEast_right_decomposition
    north south west hSW hWN hphase]
  have hW := Complex.normSq_nonneg (isingProj (-Complex.I) west)
  have hN := Complex.normSq_nonneg (isingProj (-1) north)
  have hS := Complex.normSq_nonneg (isingProj (-Complex.I) south)
  linarith


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
