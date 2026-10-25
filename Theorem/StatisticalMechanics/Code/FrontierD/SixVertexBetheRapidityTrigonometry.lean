/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityTrigonometry


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexRapidityCircle
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexRapidityCircle lam)
      (((sixVertexXiFourier lam alpha : Real) : Complex) * Complex.I *
        sixVertexRapidityCircle lam alpha) alpha := by
  let d := Real.cosh lam
  let s := Real.sinh lam
  have hdenPos : 0 < d - Real.cos alpha := by
    dsimp [d]
    have hd : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hden : ((d - Real.cos alpha : Real) : Complex) ≠ 0 := by
    exact_mod_cast hdenPos.ne'
  have hre : HasDerivAt
      (fun a : Real => d * Real.cos a - 1)
      (-d * Real.sin alpha) alpha := by
    convert (Real.hasDerivAt_cos alpha).const_mul d |>.sub_const 1 using 1
    ring
  have him : HasDerivAt
      (fun a : Real => s * Real.sin a)
      (s * Real.cos alpha) alpha := by
    convert (Real.hasDerivAt_sin alpha).const_mul s using 1
  have hnum := hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I)
  have hdenDeriv : HasDerivAt
      (fun a : Real => ((d - Real.cos a : Real) : Complex))
      (Real.sin alpha : Complex) alpha := by
    convert ((Real.hasDerivAt_cos alpha).const_sub d).ofReal_comp using 1
    ring
  have hquot := hnum.div hdenDeriv hden
  convert hquot using 1
  rw [sixVertexXiFourier_eq hlam]
  change (((s / (d - Real.cos alpha) : Real) : Complex) * Complex.I) *
      sixVertexRapidityCircle lam alpha =
    ((((-d * Real.sin alpha : Real) : Complex) +
          ((s * Real.cos alpha : Real) : Complex) * Complex.I) *
          ((d - Real.cos alpha : Real) : Complex) -
        ((((d * Real.cos alpha - 1 : Real) : Complex) +
            ((s * Real.sin alpha : Real) : Complex) * Complex.I) *
          (Real.sin alpha : Complex))) /
        ((d - Real.cos alpha : Real) : Complex) ^ 2
  rw [sixVertexRapidityCircle]
  dsimp [d, s]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_one]
  have hdenC :
      (Real.cosh lam : Complex) - (Real.cos alpha : Complex) ≠ 0 := by
    simpa only [Complex.ofReal_sub] using hden
  field_simp [hdenC]
  have hh : Real.cosh lam ^ 2 - Real.sinh lam ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq lam
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    linear_combination Real.sin alpha * hh
  · simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    linear_combination Real.sinh lam * (Real.sin_sq_add_cos_sq alpha)

theorem hasDerivAt_sixVertexMomentumCircle
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexMomentumCircle lam)
      (((sixVertexXiFourier lam alpha : Real) : Complex) * Complex.I *
        sixVertexMomentumCircle lam alpha) alpha := by
  unfold sixVertexMomentumCircle
  have hk := hasDerivAt_sixVertexRapidityMomentum hlam alpha
  have hinner := hk.ofReal_comp.mul_const Complex.I
  have houter := Complex.hasDerivAt_exp
    ((sixVertexRapidityMomentum lam alpha : Complex) * Complex.I)
  have hcomp := houter.comp alpha hinner
  change HasDerivAt
    (fun a => Complex.exp
      ((sixVertexRapidityMomentum lam a : Complex) * Complex.I)) _ alpha
  simpa only [Function.comp_apply, mul_comm] using hcomp

theorem sixVertexRapidityCircle_ne_zero
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexRapidityCircle lam alpha ≠ 0 := by
  let d := Real.cosh lam
  let s := Real.sinh lam
  have hd : 1 < d := by
    dsimp [d]
    exact Real.one_lt_cosh.mpr hlam.ne'
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sinh_pos_iff.mpr hlam
  have hdenPos : 0 < d - Real.cos alpha := by
    linarith [Real.cos_le_one alpha]
  have hden : ((d - Real.cos alpha : Real) : Complex) ≠ 0 := by
    exact_mod_cast hdenPos.ne'
  intro hv
  have hnum :
      (((d * Real.cos alpha - 1 : Real) : Complex) +
        ((s * Real.sin alpha : Real) : Complex) * Complex.I) = 0 := by
    rw [sixVertexRapidityCircle] at hv
    exact (div_eq_zero_iff.mp hv).resolve_right hden
  have hre := congrArg Complex.re hnum
  have him := congrArg Complex.im hnum
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re] at hre him
  have hsin : Real.sin alpha = 0 := him.resolve_left hs.ne'
  have hcosSq : Real.cos alpha ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  rcases sq_eq_one_iff.mp hcosSq with hcos | hcos <;> nlinarith

end
end StatMech.FrontierD
