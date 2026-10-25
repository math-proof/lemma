/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed


namespace StatMech.FrontierD

open Filter Topology Finset MeasureTheory

noncomputable section

theorem hasDerivAt_sixVertexBetheDesingularizedLogObservable
    {c x : Real} (hc : 2 < c) (hx : x ∈ Set.Icc 0 Real.pi) :
    HasDerivAt (sixVertexBetheDesingularizedLogObservable c)
      (sixVertexBetheDesingularizedLogObservableDerivative c x) x := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun y => a ^ 2 + 1 + 2 * a * Real.cos y
  let S : Real -> Real := fun y => Real.sinc (y / 2)
  have hApos : 0 < A x := by
    have ha : 1 < a := by dsimp [a]; nlinarith
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hSpos : 0 < S x := by
    rcases hx.1.eq_or_lt with rfl | hx0
    · simp [S]
    · have hhalf0 : x / 2 ≠ 0 := by positivity
      dsimp [S]
      rw [Real.sinc_of_ne_zero hhalf0]
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
        (by nlinarith [hx.2, Real.pi_pos])) (by linarith)
  have hAderiv : HasDerivAt A (-2 * a * Real.sin x) x := by
    dsimp [A]
    convert (Real.hasDerivAt_cos x).const_mul (2 * a) |>.const_add
      (a ^ 2 + 1) using 1 <;> ring
  have hSderiv : HasDerivAt S
      ((1 / 2 : Real) * sixVertexSincDerivative (x / 2)) x := by
    dsimp [S]
    convert (hasDerivAt_sinc (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2) using 1 <;> ring
  have hfirst := (hAderiv.log hApos.ne').const_mul (1 / 2 : Real)
  have hsecond := hSderiv.log hSpos.ne'
  unfold sixVertexBetheDesingularizedLogObservable
    sixVertexBetheDesingularizedLogObservableDerivative
  dsimp [a, A, S] at hfirst hsecond ⊢
  convert hfirst.sub hsecond using 1
  ring

theorem continuousOn_sixVertexBetheDesingularizedLogObservableDerivative
    {c : Real} (hc : 2 < c) :
    ContinuousOn (sixVertexBetheDesingularizedLogObservableDerivative c)
      (Set.Icc 0 Real.pi) := by
  let a := c ^ 2 - 1
  let A : Real -> Real := fun x => a ^ 2 + 1 + 2 * a * Real.cos x
  let S : Real -> Real := fun x => Real.sinc (x / 2)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hScont : Continuous S :=
    Real.continuous_sinc.comp (continuous_id.div_const 2)
  have hDcont : Continuous (fun x : Real =>
      sixVertexSincDerivative (x / 2)) :=
    continuous_sixVertexSincDerivative.comp (continuous_id.div_const 2)
  have hApos (x : Real) : 0 < A x := by
    have ha : 1 < a := by dsimp [a]; nlinarith
    dsimp [A]
    nlinarith [Real.neg_one_le_cos x, sq_nonneg (a - 1)]
  have hSpos (x : Real) (hx : x ∈ Set.Icc 0 Real.pi) : 0 < S x := by
    rcases hx.1.eq_or_lt with rfl | hx0
    · simp [S]
    · have hhalf0 : x / 2 ≠ 0 := by positivity
      dsimp [S]
      rw [Real.sinc_of_ne_zero hhalf0]
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
        (by nlinarith [hx.2, Real.pi_pos])) (by linarith)
  unfold sixVertexBetheDesingularizedLogObservableDerivative
  apply ContinuousOn.sub
  · exact ((continuous_const.mul Real.continuous_sin).div hAcont
      (fun x => (hApos x).ne')).continuousOn
  · exact continuous_const.continuousOn.mul
      (hDcont.continuousOn.div hScont.continuousOn
        (fun x hx => (hSpos x hx).ne'))

theorem abs_intervalIntegral_sub_const_mul_le_of_bound
    {f : Real -> Real} {a b z E : Real} (hab : a <= b)
    (hf : ContinuousOn f (Set.Icc a b)) (hE : 0 <= E)
    (hbound : ∀ x ∈ Set.Icc a b, |f x - z| <= E) :
    |(∫ x in a..b, f x) - (b - a) * z| <= E * (b - a) := by
  have hfint : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have hrewrite :
      (∫ x in a..b, f x) - (b - a) * z =
        ∫ x in a..b, (f x - z) := by
    rw [intervalIntegral.integral_sub hfint intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
  rw [hrewrite]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := E) (f := fun x => f x - z)
    (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact hbound x ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h

theorem abs_two_halfIncrement_sub_fullIncrement_le
    {H D : Real -> Real} {a b E : Real} (hab : a <= b)
    (hH : ContinuousOn H (Set.Icc a b))
    (hD : ContinuousOn D (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt H (D x) x)
    (hE : 0 <= E)
    (hclose : ∀ x ∈ Set.Icc a b,
      |D x - D ((a + b) / 2)| <= E) :
    |2 * (H ((a + b) / 2) - H a) - (H b - H a)| <=
      E * (b - a) := by
  let m := (a + b) / 2
  have ham : a <= m := by dsimp [m]; linarith
  have hmb : m <= b := by dsimp [m]; linarith
  have hleftSub : Set.Icc a m ⊆ Set.Icc a b := fun x hx =>
    ⟨hx.1, hx.2.trans hmb⟩
  have hrightSub : Set.Icc m b ⊆ Set.Icc a b := fun x hx =>
    ⟨ham.trans hx.1, hx.2⟩
  have hleftInt : IntervalIntegrable D volume a m :=
    (hD.mono hleftSub).intervalIntegrable_of_Icc ham
  have hrightInt : IntervalIntegrable D volume m b :=
    (hD.mono hrightSub).intervalIntegrable_of_Icc hmb
  have hleftFTC : (∫ x in a..m, D x) = H m - H a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (hleftSub (by simpa [Set.uIcc_of_le ham] using hx)))
      hleftInt
  have hrightFTC : (∫ x in m..b, D x) = H b - H m := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (hrightSub (by simpa [Set.uIcc_of_le hmb] using hx)))
      hrightInt
  have hleftBound :
      |(∫ x in a..m, D x) - (m - a) * D m| <= E * (m - a) :=
    by
      simpa [m] using
        (abs_intervalIntegral_sub_const_mul_le_of_bound ham
          (hD.mono hleftSub) hE (fun x hx => hclose x (hleftSub hx)))
  have hrightBound :
      |(∫ x in m..b, D x) - (b - m) * D m| <= E * (b - m) :=
    by
      simpa [m] using
        (abs_intervalIntegral_sub_const_mul_le_of_bound hmb
          (hD.mono hrightSub) hE (fun x hx => hclose x (hrightSub hx)))
  have hhalf : m - a = b - m := by dsimp [m]; ring
  rw [hleftFTC] at hleftBound
  rw [hrightFTC] at hrightBound
  calc
    |2 * (H m - H a) - (H b - H a)| =
        |((H m - H a) - (m - a) * D m) -
          ((H b - H m) - (b - m) * D m)| := by
      rw [hhalf]
      congr 1
      ring
    _ <= |(H m - H a) - (m - a) * D m| +
        |(H b - H m) - (b - m) * D m| := abs_sub _ _
    _ <= E * (m - a) + E * (b - m) :=
      add_le_add hleftBound hrightBound
    _ = E * (b - a) := by ring

theorem abs_two_halfIncrementSum_sub_endpoint_le
    {H D : Real -> Real} {n : Nat} (a : Nat -> Real) {E : Real}
    (ha : ∀ j, j <= n -> a j ∈ Set.Icc 0 Real.pi)
    (hordered : ∀ j, j < n -> a j <= a (j + 1))
    (hH : ContinuousOn H (Set.Icc 0 Real.pi))
    (hD : ContinuousOn D (Set.Icc 0 Real.pi))
    (hderiv : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt H (D x) x)
    (hE : 0 <= E)
    (hclose : ∀ j, j < n -> ∀ x ∈ Set.Icc (a j) (a (j + 1)),
      |D x - D ((a j + a (j + 1)) / 2)| <= E) :
    |2 * ∑ j : Fin n,
        (H ((a j.val + a (j.val + 1)) / 2) - H (a j.val)) -
        (H (a n) - H (a 0))| <= E * (a n - a 0) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => H ((a j + a (j + 1)) / 2) - H (a j)) n]
  have hcell (j : Nat) (hj : j < n) :
      |2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
          (H (a (j + 1)) - H (a j))| <=
        E * (a (j + 1) - a j) := by
    have hsub : Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc 0 Real.pi :=
      fun x hx => ⟨(ha j hj.le).1.trans hx.1,
        hx.2.trans (ha (j + 1) (by omega)).2⟩
    exact abs_two_halfIncrement_sub_fullIncrement_le (hordered j hj)
      (hH.mono hsub) (hD.mono hsub)
      (fun x hx => hderiv x (hsub hx)) hE (hclose j hj)
  have htel :
      (∑ j ∈ Finset.range n, (H (a (j + 1)) - H (a j))) =
        H (a n) - H (a 0) := by
    have h := Finset.sum_range_sub' (fun j => H (a j)) n
    rw [Finset.sum_sub_distrib] at h ⊢
    linarith
  have hrewrite :
      2 * ∑ j ∈ Finset.range n,
          (H ((a j + a (j + 1)) / 2) - H (a j)) -
          (H (a n) - H (a 0)) =
        ∑ j ∈ Finset.range n,
          (2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
            (H (a (j + 1)) - H (a j))) := by
    rw [← htel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    |∑ j ∈ Finset.range n,
        (2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
          (H (a (j + 1)) - H (a j)))| <=
        ∑ j ∈ Finset.range n,
          |2 * (H ((a j + a (j + 1)) / 2) - H (a j)) -
            (H (a (j + 1)) - H (a j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ j ∈ Finset.range n, E * (a (j + 1) - a j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcell j (Finset.mem_range.mp hj)
    _ = E * (a n - a 0) := by
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.sum_range_sub' a n
      rw [Finset.sum_sub_distrib] at h ⊢
      linarith

end
end StatMech.FrontierD
