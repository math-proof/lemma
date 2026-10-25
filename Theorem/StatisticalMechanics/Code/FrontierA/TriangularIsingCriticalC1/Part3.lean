/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part3
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingRayLogDeriv_abs_le_criticalMajorant
    {beta J m K b x y : Real}
    (hm : 0 < m) (hK : 0 < K)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hlower : m * ((b - beta) ^ 2 +
        ((1 - Real.cos x) + (1 - Real.cos y))) <=
      triangularIsingSymbol b b (b * J) x y)
    (hderiv : |triangularIsingRaySymbolDeriv J b x y| <=
      K * (2 * |b - beta| +
        ((1 - Real.cos x) + (1 - Real.cos y)))) :
    |triangularIsingRayLogDeriv J b x y| <=
      triangularIsingCriticalFirstMajorant m K x y := by
  let A : Real := 2 - Real.cos x - Real.cos y
  let delta : Real := b - beta
  have hAeq : (1 - Real.cos x) + (1 - Real.cos y) = A := by
    unfold A
    ring
  rw [hAeq] at hlower hderiv
  have hxy : 0 < |x * y| := abs_pos.mpr (mul_ne_zero hx0 hy0)
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hA : 0 < A := by
    exact (div_pos hxy hpi).trans_le
      (StatMech.Onsager.ons_criticalDenom_lower_abs_mul hx hy)
  have hden0 : 0 < m * (delta ^ 2 + A) := by positivity
  have hsymbol : 0 < triangularIsingSymbol b b (b * J) x y := by
    apply hden0.trans_le
    simpa only [A, delta] using hlower
  change |triangularIsingRaySymbolDeriv J b x y /
      triangularIsingSymbol b b (b * J) x y| <= _
  rw [abs_div, abs_of_pos hsymbol]
  have hratio := StatMech.Onsager.ons_delta_ratio_le_inv_sqrt
    (delta := delta) hA
  have hfirst :
      |triangularIsingRaySymbolDeriv J b x y| /
          triangularIsingSymbol b b (b * J) x y <=
        (K / m) * ((2 * |delta| + A) / (delta ^ 2 + A)) := by
    calc
      _ <= (K * (2 * |delta| + A)) /
          (m * (delta ^ 2 + A)) := by
            apply div_le_div₀
            · positivity
            · simpa only [A, delta] using hderiv
            · exact hden0
            · simpa only [A, delta] using hlower
      _ = (K / m) * ((2 * |delta| + A) / (delta ^ 2 + A)) := by
            field_simp [hm.ne', (show delta ^ 2 + A ≠ 0 by positivity)]
            <;> ring
  calc
    _ <= (K / m) * ((2 * |delta| + A) / (delta ^ 2 + A)) := hfirst
    _ <= (K / m) * (1 / Real.sqrt A + 1) := by
      gcongr
    _ <= (K / m) *
        (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
          StatMech.Onsager.ons_criticalOneDimMajorant y + 1) := by
      gcongr
      simpa only [A, StatMech.Onsager.ons_criticalOneDimMajorant] using
        StatMech.Onsager.ons_inv_sqrt_criticalDenom_le_product
          hx hy hx0 hy0
    _ = triangularIsingCriticalFirstMajorant m K x y := rfl

theorem triangularIsingCriticalFirstMajorant_inner_intervalIntegrable
    {m K : Real} (x : Real) :
    IntervalIntegrable (triangularIsingCriticalFirstMajorant m K x)
      volume (-Real.pi) Real.pi := by
  unfold triangularIsingCriticalFirstMajorant
  exact (((StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable.const_mul
    (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x)).add
      intervalIntegral.intervalIntegrable_const).const_mul (K / m))

theorem triangularIsingCriticalFirstMajorant_inner_integral
    (m K x : Real) :
    (∫ y in (-Real.pi)..Real.pi,
      triangularIsingCriticalFirstMajorant m K x y) =
      (K / m) *
        (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
          (∫ y in (-Real.pi)..Real.pi,
            StatMech.Onsager.ons_criticalOneDimMajorant y) +
          2 * Real.pi) := by
  have hfirst : IntervalIntegrable
      (fun y => Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
        StatMech.Onsager.ons_criticalOneDimMajorant y)
      volume (-Real.pi) Real.pi :=
    StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable.const_mul _
  unfold triangularIsingCriticalFirstMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hfirst
    intervalIntegral.intervalIntegrable_const]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  norm_num only [smul_eq_mul]
  ring

end
end StatMech.FrontierA
