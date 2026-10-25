/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part12


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem isingPrimalProjectionDivergenceWithoutNorth_top_decomposition
    (east south west : Complex)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hphase : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south) :
    isingPrimalProjectionDivergenceWithoutNorth east south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-1) south) =
      -2 * Complex.normSq (isingProj (-1) south) -
        Complex.normSq (isingProj (-1) east) -
        Complex.normSq (isingProj Complex.I west) := by
  have hsame : Complex.normSq (isingProj Complex.I south) =
      Complex.normSq (isingProj (-1) south) := by
    have hlam : Complex.normSq isingLambda = 1 := by
      rw [isingLambda_val]
      norm_num [Complex.normSq_apply]
    rw [hphase, Complex.normSq_mul, Complex.normSq_neg,
      hlam, one_mul]
  have hfar : Complex.normSq (isingProj 1 south) =
      (3 + 2 * Real.sqrt 2) *
        Complex.normSq (isingProj (-1) south) := by
    rw [isingLambda_val] at hphase
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
      Complex.div_re, Complex.div_im] at hphase ⊢
    field_simp at hphase ⊢
    have hSx : south.re = (1 + Real.sqrt 2) * south.im := by
      linarith [hphase.1]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
    rw [hSx]
    ring_nf
    rw [hsq2]
    ring
  have hpairE_I := isingProj_normSq_add_neg Complex.I east (by norm_num)
  have hpairE_one := isingProj_normSq_add_neg 1 east (by norm_num)
  have hE : Complex.normSq (isingProj 1 east) -
        Complex.normSq (isingProj (-Complex.I) east) =
      Complex.normSq (isingProj Complex.I south) -
        Complex.normSq (isingProj (-1) east) := by
    rw [← hES]
    linarith
  have hSWnorm := congrArg Complex.normSq hSW
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  unfold isingPrimalProjectionDivergenceWithoutNorth
  rw [hghost]
  nlinarith [hE, hSWnorm, hsame, hfar]

theorem isingPrimalProjectionDivergenceWithoutNorth_top_add_ghost_nonpos
    (east south west : Complex)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hphase : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south) :
    isingPrimalProjectionDivergenceWithoutNorth east south west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj (-1) south) ≤ 0 := by
  rw [isingPrimalProjectionDivergenceWithoutNorth_top_decomposition
    east south west hES hSW hphase]
  have hS := Complex.normSq_nonneg (isingProj (-1) south)
  have hE := Complex.normSq_nonneg (isingProj (-1) east)
  have hW := Complex.normSq_nonneg (isingProj Complex.I west)
  linarith

theorem isingProj_normSq_negOne_of_bottom_phase
    (z : Complex)
    (hphase : isingProj (-Complex.I) z =
      -isingLambda * isingProj 1 z) :
    Complex.normSq (isingProj (-1) z) =
      (3 + 2 * Real.sqrt 2) * Complex.normSq (isingProj 1 z) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im] at hphase ⊢
  field_simp at hphase ⊢
  have hzy : z.im = -(1 + Real.sqrt 2) * z.re := by
    linarith [hphase.1]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  rw [hzy]
  ring_nf
  rw [hsq2]
  ring

theorem isingProj_normSq_I_of_right_phase
    (z : Complex)
    (hphase : isingProj (-1) z =
      -isingLambda * isingProj (-Complex.I) z) :
    Complex.normSq (isingProj Complex.I z) =
      (3 + 2 * Real.sqrt 2) *
        Complex.normSq (isingProj (-Complex.I) z) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im] at hphase ⊢
  field_simp at hphase ⊢
  have hlinear : Real.sqrt 2 * z.re +
      (Real.sqrt 2 + 2) * z.im = 0 := by
    linarith [hphase.2]
  have hprod : Real.sqrt 2 *
      (z.re + (1 + Real.sqrt 2) * z.im) = 0 := by
    calc
      _ = Real.sqrt 2 * z.re +
          (Real.sqrt 2 + Real.sqrt 2 * Real.sqrt 2) * z.im := by ring
      _ = Real.sqrt 2 * z.re +
          (Real.sqrt 2 + 2) * z.im := by rw [hsqrt]
      _ = 0 := hlinear
  have hzx : z.re = -(1 + Real.sqrt 2) * z.im := by
    have hz := (mul_eq_zero.mp hprod).resolve_left hsqrt_ne
    linarith
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  have hsq3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = _ := by rw [hsq2]
  rw [hzx]
  ring_nf
  rw [hsq2, hsq3]
  ring

theorem isingProj_normSq_one_of_top_phase
    (z : Complex)
    (hphase : isingProj Complex.I z =
      -isingLambda * isingProj (-1) z) :
    Complex.normSq (isingProj 1 z) =
      (3 + 2 * Real.sqrt 2) * Complex.normSq (isingProj (-1) z) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  simp [isingProj, Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im] at hphase ⊢
  field_simp at hphase ⊢
  have hzx : z.re = (1 + Real.sqrt 2) * z.im := by
    linarith [hphase.1]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := by nlinarith [hsqrt]
  rw [hzx]
  ring_nf
  rw [hsq2]
  ring


theorem isingPrimalProjectionDivergence_bottomRightCorner_decomposition
    (north west : Complex)
    (hbottom : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj (-Complex.I) north) -
          Complex.normSq (isingProj (-1) north)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj 1 north) +
            Complex.normSq (isingProj (-Complex.I) west)) =
      -4 * (Complex.normSq (isingProj 1 north) +
        Complex.normSq (isingProj (-Complex.I) west)) := by
  have hNfar := isingProj_normSq_negOne_of_bottom_phase north hbottom
  have hWfar := isingProj_normSq_I_of_right_phase west hright
  have hlam : Complex.normSq isingLambda = 1 := by
    rw [isingLambda_val]
    norm_num [Complex.normSq_apply]
  have hNnear := congrArg Complex.normSq hbottom
  have hWnear := congrArg Complex.normSq hright
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hNnear
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hWnear
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  rw [hghost]
  nlinarith

theorem isingPrimalProjectionDivergence_bottomRightCorner_add_ghost_nonpos
    (north west : Complex)
    (hbottom : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj (-Complex.I) north) -
          Complex.normSq (isingProj (-1) north)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj 1 north) +
            Complex.normSq (isingProj (-Complex.I) west)) ≤ 0 := by
  rw [isingPrimalProjectionDivergence_bottomRightCorner_decomposition
    north west hbottom hright]
  have hN : 0 ≤ Complex.normSq (isingProj 1 north) := Complex.normSq_nonneg _
  have hW : 0 ≤ Complex.normSq (isingProj (-Complex.I) west) :=
    Complex.normSq_nonneg _
  linarith


theorem isingPrimalProjectionDivergence_topRightCorner_decomposition
    (south west : Complex)
    (htop : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj Complex.I south) -
          Complex.normSq (isingProj 1 south)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj (-1) south) +
            Complex.normSq (isingProj (-Complex.I) west)) =
      -4 * (Complex.normSq (isingProj (-1) south) +
        Complex.normSq (isingProj (-Complex.I) west)) := by
  have hSfar := isingProj_normSq_one_of_top_phase south htop
  have hWfar := isingProj_normSq_I_of_right_phase west hright
  have hlam : Complex.normSq isingLambda = 1 := by
    rw [isingLambda_val]
    norm_num [Complex.normSq_apply]
  have hSnear := congrArg Complex.normSq htop
  have hWnear := congrArg Complex.normSq hright
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hSnear
  simp only [Complex.normSq_mul, Complex.normSq_neg, hlam, one_mul] at hWnear
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hghost : isingFermionicGhostCoefficient =
      2 * Real.sqrt 2 - 2 := by
    unfold isingFermionicGhostCoefficient
    field_simp [show 1 + Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [hsqrt]
  rw [hghost]
  nlinarith

theorem isingPrimalProjectionDivergence_topRightCorner_add_ghost_nonpos
    (south west : Complex)
    (htop : isingProj Complex.I south =
      -isingLambda * isingProj (-1) south)
    (hright : isingProj (-1) west =
      -isingLambda * isingProj (-Complex.I) west) :
    (Complex.normSq (isingProj Complex.I south) -
          Complex.normSq (isingProj 1 south)) +
        (Complex.normSq (isingProj (-1) west) -
          Complex.normSq (isingProj Complex.I west)) +
        isingFermionicGhostCoefficient *
          (Complex.normSq (isingProj (-1) south) +
            Complex.normSq (isingProj (-Complex.I) west)) ≤ 0 := by
  rw [isingPrimalProjectionDivergence_topRightCorner_decomposition
    south west htop hright]
  have hS : 0 ≤ Complex.normSq (isingProj (-1) south) := Complex.normSq_nonneg _
  have hW : 0 ≤ Complex.normSq (isingProj (-Complex.I) west) :=
    Complex.normSq_nonneg _
  linarith


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
