/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSwitching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPrimitive
open Complex


namespace StatMech.Universality

noncomputable section

theorem isingPrimalProjectionDivergenceWithoutSouth_add
    (north east south west : Complex) :
    isingPrimalProjectionDivergenceWithoutSouth north east west +
        (Complex.normSq (isingProj Complex.I south) -
          Complex.normSq (isingProj 1 south)) =
      isingPrimalProjectionDivergence north east south west := by
  unfold isingPrimalProjectionDivergenceWithoutSouth
    isingPrimalProjectionDivergence
  ring


theorem isingPrimalPrimitiveLaplacian_eq_projectionDivergence
    (north east south west : Complex) :
    isingPrimalPrimitiveLaplacian north east south west =
      isingPrimalProjectionDivergence north east south west := by
  unfold isingPrimalPrimitiveLaplacian isingPrimitiveSquareCombination
  unfold isingPrimalProjectionDivergence isingProj
  simp only [Complex.normSq_apply, map_neg, map_one, map_mul,
    Complex.conj_I, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  norm_num
  ring


theorem isingSquareSHolomorphicQuad_of_projection_cycle
    (north east south west : Complex)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north) :
    IsingSquareSHolomorphicQuad south west north east := by
  have hNEre := congrArg Complex.re hNE
  have hESre := congrArg Complex.re hES
  have hSWim := congrArg Complex.im hSW
  have hWNre := congrArg Complex.re hWN
  simp only [isingProj, map_one, map_neg, map_mul, Complex.conj_I,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    at hNEre hESre hSWim hWNre
  norm_num at hNEre hESre hSWim hWNre
  unfold IsingSquareSHolomorphicQuad
  constructor
  · apply Complex.ext
    · simp
    · simp
      linarith
  constructor
  · apply Complex.ext
    · simp
      linarith
    · simp
      ring
  · apply Complex.ext
    · simp
      linarith
    · simp
      linarith


end
end StatMech.Universality
