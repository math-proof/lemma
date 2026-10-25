/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTheta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCactusAssembly.Part2
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Def.StatisticalMechanics.Code.FrontierA.KacWardTheta
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix StatMech.Onsager


theorem kwTheta_one_sub (omega : ℂ) (x : Fin 3 -> ℂ) :
    1 - kwThetaTransition omega x =
      Matrix.fromBlocks 1 (-kwThetaForward omega x)
        (-kwThetaReverse omega x) 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [kwThetaTransition, Matrix.one_apply]


theorem kacWard_theta (omega : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I) (x : Fin 3 -> ℂ) :
    (1 - kwThetaTransition omega x).det = (kwThetaEvenPolynomial x) ^ 2 := by
  rw [kwTheta_one_sub, Matrix.det_fromBlocks_one₁₁]
  have hnegMul :
      (-kwThetaReverse omega x) * (-kwThetaForward omega x) =
        kwThetaReverse omega x * kwThetaForward omega x := by
    simp
  rw [hnegMul, Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Fin.sum_univ_three]
  simp [kwThetaForward, kwThetaReverse, kwThetaForwardInternal,
    kwThetaReverseInternal, kwThetaLeftDirection, kwThetaRightDirection,
    ons_turnW]
  field_simp
  have h4 : omega ^ 4 = -1 := ons_omega_pow_four omega hI
  have h8 : omega ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add, h4]
    norm_num
  have h12 : omega ^ 12 = -1 := by
    rw [show (12 : ℕ) = 4 + 8 by norm_num, pow_add, h4, h8]
    norm_num
  rw [h4, h8, h12]
  unfold kwThetaEvenPolynomial
  ring

end StatMech.FrontierA
