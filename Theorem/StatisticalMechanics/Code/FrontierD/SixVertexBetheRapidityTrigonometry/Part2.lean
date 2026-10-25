/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityTrigonometry.Part2


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexCircleRatio
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexCircleRatio lam) 0 alpha := by
  have hu := hasDerivAt_sixVertexMomentumCircle hlam alpha
  have hv := hasDerivAt_sixVertexRapidityCircle hlam alpha
  have hv0 := sixVertexRapidityCircle_ne_zero hlam alpha
  have hdiv := hu.div hv hv0
  convert hdiv using 1
  ring


theorem sixVertexMomentumCircle_eq_rapidityCircle
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexMomentumCircle lam alpha =
      sixVertexRapidityCircle lam alpha := by
  have hw (x : Real) : HasDerivAt (sixVertexCircleRatio lam) 0 x :=
    hasDerivAt_sixVertexCircleRatio hlam x
  have hw0 : sixVertexCircleRatio lam 0 = 1 := by
    unfold sixVertexCircleRatio sixVertexMomentumCircle
      sixVertexRapidityCircle sixVertexRapidityMomentum
    have hden : Real.cosh lam - 1 ≠ 0 := by
      have hcosh := Real.one_lt_cosh.mpr hlam.ne'
      linarith
    have hdenC : Complex.cosh (lam : Complex) - 1 ≠ 0 := by
      rw [<- Complex.ofReal_cosh]
      exact_mod_cast hden
    simp [hdenC]
  have hwa : sixVertexCircleRatio lam alpha =
      sixVertexCircleRatio lam 0 := by
    by_cases ha : 0 <= alpha
    · have hcont : ContinuousOn (sixVertexCircleRatio lam)
          (Set.Icc 0 alpha) :=
        fun x _ => (hw x).continuousAt.continuousWithinAt
      exact constant_of_has_deriv_right_zero hcont
        (fun x _ => (hw x).hasDerivWithinAt) alpha ⟨ha, le_rfl⟩
    · have ha' : alpha <= 0 := le_of_not_ge ha
      have hcont : ContinuousOn (sixVertexCircleRatio lam)
          (Set.Icc alpha 0) :=
        fun x _ => (hw x).continuousAt.continuousWithinAt
      exact (constant_of_has_deriv_right_zero hcont
        (fun x _ => (hw x).hasDerivWithinAt) 0 ⟨ha', le_rfl⟩).symm
  have hwone : sixVertexCircleRatio lam alpha = 1 := hwa.trans hw0
  exact (div_eq_one_iff_eq (sixVertexRapidityCircle_ne_zero hlam alpha)).mp
    hwone

theorem cos_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Real.cos (sixVertexRapidityMomentum lam alpha) =
      (Real.cosh lam * Real.cos alpha - 1) /
        (Real.cosh lam - Real.cos alpha) := by
  have huv := sixVertexMomentumCircle_eq_rapidityCircle hlam alpha
  have hre := congrArg Complex.re huv
  unfold sixVertexMomentumCircle sixVertexRapidityCircle at hre
  simp [Complex.exp_ofReal_mul_I_re, Complex.div_re,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re] at hre
  have hden : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have hd := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  field_simp [hden] at hre ⊢
  nlinarith

theorem sin_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Real.sin (sixVertexRapidityMomentum lam alpha) =
      Real.sinh lam * Real.sin alpha /
        (Real.cosh lam - Real.cos alpha) := by
  have huv := sixVertexMomentumCircle_eq_rapidityCircle hlam alpha
  have him := congrArg Complex.im huv
  unfold sixVertexMomentumCircle sixVertexRapidityCircle at him
  simp [Complex.exp_ofReal_mul_I_im, Complex.div_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.sinh_ofReal_re] at him
  have hden : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have hd := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  field_simp [hden] at him ⊢
  nlinarith

end
end StatMech.FrontierD
