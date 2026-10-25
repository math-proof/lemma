/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem hasSum_sixVertexLogCosineSeries
    {r : Real} (hr : |r| < 1) (alpha : Real) :
    HasSum (fun n : Nat =>
      r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
        (n + 1 : Real))
      (-Real.log ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖) := by
  let z : Complex := (r : Complex) * Complex.exp (Complex.I * alpha)
  have hzNorm : ‖z‖ = |r| := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp
  have hz : ‖z‖ < 1 := by simpa [hzNorm] using hr
  have hcomplex := Complex.hasSum_taylorSeries_neg_log hz
  have hreal := Complex.hasSum_re hcomplex
  have hshift : HasSum (fun n : Nat =>
      ((z ^ (n + 1) / ((n + 1 : Nat) : Complex)).re))
      (-Complex.log (1 - z)).re := by
    simpa using
      ((hasSum_nat_add_iff'
        (f := fun n : Nat => (z ^ n / (n : Complex)).re) 1).mpr hreal)
  convert hshift using 1
  · funext n
    have hexp :
        (Complex.exp (Complex.I * alpha) ^ (n + 1)).re =
          Real.cos ((n + 1 : Real) * alpha) := by
      rw [← Complex.exp_nat_mul]
      convert Complex.exp_ofReal_mul_I_re ((n + 1 : Real) * alpha) using 2
      push_cast
      ring
    dsimp [z]
    rw [mul_pow, Complex.div_natCast_re, Complex.mul_re, hexp]
    have hre : ((r : Complex) ^ (n + 1)).re = r ^ (n + 1) := by
      rw [← Complex.ofReal_pow]
      rfl
    have him : ((r : Complex) ^ (n + 1)).im = 0 := by
      rw [← Complex.ofReal_pow]
      rfl
    rw [hre, him]
    norm_num [Nat.cast_add, Nat.cast_one]
  · simpa [z, Complex.log_re]

theorem sixVertexLogCosineSeries_eq_neg_log_norm
    {r : Real} (hr : |r| < 1) (alpha : Real) :
    sixVertexLogCosineSeries r alpha =
      -Real.log ‖(1 : Complex) -
        (r : Complex) * Complex.exp (Complex.I * alpha)‖ :=
  (hasSum_sixVertexLogCosineSeries hr alpha).tsum_eq

end
end StatMech.FrontierD
