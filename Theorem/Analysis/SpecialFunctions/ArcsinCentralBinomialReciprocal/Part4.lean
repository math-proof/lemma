import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part5


namespace MetaMathlibExt

theorem S2term_zero (x : ℝ) : S2term x 0 = 0 := by simp [S2term]

theorem S2term_bound (x : ℝ) (hx0 : x ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ‖S2term x n‖ ≤ (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n)
      + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
  have hratio := ratio_le n hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx2pos : (0:ℝ) < x ^ 2 := by positivity
  have hCnonneg : (0:ℝ) ≤ (4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) := by positivity
  have hcast : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
    have h : 1 ≤ 2 * n := by omega
    have hsub := Nat.cast_sub (R := ℝ) (m := 1) (n := 2 * n) h
    push_cast at hsub ⊢
    linarith
  have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
    simp only [dcoef]; field_simp
  have e1 : (0:ℝ) ≤ 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) := by
    positivity
  have e2 : (0:ℝ) ≤ 2 * (n : ℝ) - 1 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hnorm : ‖S2term x n‖
      = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ))
        * (2 * (n : ℝ) - 1) * |x| ^ (2 * n - 2) := by
    simp only [S2term, show n ≠ 0 by omega, ↓reduceIte, hcast, hd]
    rw [Real.norm_eq_abs]
    simp only [abs_mul, abs_pow, abs_of_nonneg e1, abs_of_nonneg e2]
  rw [hnorm]
  have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
  have hpow : |x| ^ (2 * n - 2) = (x ^ 2) ^ n / x ^ 2 := by
    have h1 : |x| ^ (2 * n) = (|x| ^ 2) ^ n := by rw [← pow_mul]
    have h2 : 2 * n = (2 * n - 2) + 2 := by omega
    have h3 : |x| ^ (2 * n) = |x| ^ (2 * n - 2) * |x| ^ 2 := by
      conv_lhs => rw [h2]; rw [pow_add]
    have hne : (|x| ^ 2 : ℝ) ≠ 0 := by
      rw [sq_abs]; exact ne_of_gt hx2pos
    have hsq : (|x| ^ 2 : ℝ) = x ^ 2 := sq_abs x
    have h4 : |x| ^ (2 * n - 2) = |x| ^ (2 * n) / |x| ^ 2 := by
      field_simp; exact h3.symm
    rw [h4, h1, hsq]
  rw [hpow]
  have hpos : (0:ℝ) ≤ (x ^ 2) ^ n / x ^ 2 :=
    div_nonneg (pow_nonneg (sq_nonneg x) n) (sq_nonneg x)
  have hnn21 : (0:ℝ) ≤ (n : ℝ) * (2 * (n : ℝ) - 1) := by
    apply mul_nonneg (by positivity); linarith
  have hstep : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)
      ≤ 4 * ((n : ℝ) * (2 * (n : ℝ) - 1)) := by
    have hmul := mul_le_mul_of_nonneg_right hle2 hnn21
    linarith
  calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * ((x ^ 2) ^ n / x ^ 2)
      ≤ (4 * ((n : ℝ) * (2 * (n : ℝ) - 1))) * ((x ^ 2) ^ n / x ^ 2) :=
        mul_le_mul_of_nonneg_right hstep hpos
    _ = (4 / x ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (x ^ 2) ^ n) := by ring
    _ ≤ (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n) + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
        have hq : (0:ℝ) ≤ (x ^ 2) ^ n := pow_nonneg (sq_nonneg x) n
        have hcoef : (n : ℝ) * (2 * (n : ℝ) - 1) ≤ 2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1) := by
          nlinarith [sq_nonneg (n : ℝ)]
        have := mul_le_mul_of_nonneg_right hcoef hq
        have hdiv : (4 / x ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (x ^ 2) ^ n)
            ≤ (4 / x ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (x ^ 2) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [this]
        calc (4 / x ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (x ^ 2) ^ n)
            ≤ (4 / x ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (x ^ 2) ^ n) := hdiv
          _ = (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n) + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by ring

theorem summable_S2term (x : ℝ) (hx : |x| < 1) : Summable (S2term x) := by
  by_cases hx0 : x = 0
  · subst hx0
    have hsupp : Function.support (S2term 0) ⊆ {1} := by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn
      simp only [Set.mem_singleton_iff]
      by_contra hne
      apply hn
      simp only [S2term]
      split
      · rfl
      · rename_i h
        have : 2 ≤ n := by omega
        simp [zero_pow (by omega : 2 * n - 2 ≠ 0)]
    have hfin : Function.HasFiniteSupport (S2term 0) :=
      Set.Finite.subset (Set.finite_singleton 1) hsupp
    exact summable_of_hasFiniteSupport hfin
  · have hx2 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
    have hnn : 0 ≤ x ^ 2 := sq_nonneg x
    have hgeom1 := summable_succ_mul_geom (x ^ 2) hnn hx2
    have hnorm : ‖x ^ 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]; exact hx2
    have hgeom2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
    have hC : Summable (fun n : ℕ => (8 / x ^ 2) * ((n : ℝ) ^ 2 * (x ^ 2) ^ n)
        + (4 / x ^ 2) * (((n : ℝ) + 1) * (x ^ 2) ^ n)) :=
      (hgeom2.mul_left _).add (hgeom1.mul_left _)
    apply Summable.of_norm_bounded hC
    intro n
    by_cases hn : n = 0
    · subst hn; simp only [S2term_zero, norm_zero]; positivity
    · exact S2term_bound x hx0 n (by omega)

theorem two_pow_eq (n : ℕ) : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
  calc (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
    _ = 4 ^ n := by norm_num

theorem hasDerivAt_Aterm (x : ℝ) (n : ℕ) : HasDerivAt (fun y => Aterm y n) (Dterm x n) x := by
  by_cases hn : n = 0
  · subst hn
    have hfun : (fun y => Aterm y 0) = fun _ => 0 := by
      funext y; simp [Aterm]
    rw [hfun, Dterm_zero]
    exact hasDerivAt_const x 0
  · have h2 : (2 : ℝ) ^ (2 * n) = 4 ^ n := two_pow_eq n
    have hfun : (fun y => Aterm y n)
        = fun y => ((2 ^ (2 * n) : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * y ^ (2 * n) := by
      funext y
      simp only [Aterm, mul_pow, h2]
      ring
    rw [hfun]
    have hderiv := (hasDerivAt_pow (2 * n) x).const_mul
      ((2 ^ (2 * n) : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)))
    have hcast : (((2 * n : ℕ)) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rw [hcast] at hderiv
    refine hderiv.congr_deriv ?_
    simp only [Dterm, hn, ↓reduceIte, dcoef, h2]
    field_simp

theorem hasDerivAt_Dterm (x : ℝ) (n : ℕ) : HasDerivAt (fun y => Dterm y n) (S2term x n) x := by
  by_cases hn : n = 0
  · subst hn
    have hfun : (fun y => Dterm y 0) = fun _ => 0 := by
      funext y; simp [Dterm]
    rw [hfun, S2term_zero]
    exact hasDerivAt_const x 0
  · have hcast1 : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
      have h : 1 ≤ 2 * n := by omega
      have hsub := Nat.cast_sub (R := ℝ) (m := 1) (n := 2 * n) h
      push_cast at hsub ⊢
      linarith
    have hfun : (fun y => Dterm y n) = fun y => (2 * dcoef n) * y ^ (2 * n - 1) := by
      funext y; simp [Dterm, hn, mul_assoc]
    rw [hfun]
    have hderiv := (hasDerivAt_pow (2 * n - 1) x).const_mul (2 * dcoef n)
    have hexp : 2 * n - 1 - 1 = 2 * n - 2 := by omega
    rw [hexp, hcast1] at hderiv
    refine hderiv.congr_deriv ?_
    simp only [S2term, hn, ↓reduceIte, ← hcast1]
    ring

theorem mem_ball_zero_iff (y r : ℝ) : y ∈ Metric.ball (0 : ℝ) r ↔ |y| < r := by
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]

theorem Dterm_uniform_bound (r : ℝ) (hr : 0 < r) (n : ℕ) (y : ℝ)
    (hy : y ∈ Metric.ball (0 : ℝ) r) :
    ‖Dterm y n‖ ≤ (4 / r) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
  have hyr : |y| < r := (mem_ball_zero_iff y r).mp hy
  have hyr0 : |y| ≤ r := le_of_lt hyr
  by_cases hn : n = 0
  · subst hn
    simp only [Dterm_zero, norm_zero]
    positivity
  · have hratio := ratio_le n (by omega)
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
      simp only [dcoef]; field_simp
    have epos : (0:ℝ) ≤ 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) := by
      positivity
    have hnorm : ‖Dterm y n‖
        = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) * |y| ^ (2 * n - 1) := by
      simp only [Dterm, hn, ↓reduceIte, hd]
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_pow, abs_of_nonneg epos]
    rw [hnorm]
    have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
    have hpow_le : |y| ^ (2 * n - 1) ≤ r ^ (2 * n - 1) :=
      pow_le_pow_left₀ (abs_nonneg y) hyr0 _
    have hpow_eq : r ^ (2 * n - 1) = (r ^ 2) ^ n / r := by
      have h1 : r ^ (2 * n) = (r ^ 2) ^ n := by rw [← pow_mul]
      have h2 : 2 * n = (2 * n - 1) + 1 := by omega
      have h3 : r ^ (2 * n) = r ^ (2 * n - 1) * r := by
        conv_lhs => rw [h2]; rw [pow_succ]
      have hne : (r : ℝ) ≠ 0 := ne_of_gt hr
      have h4 : r ^ (2 * n - 1) = r ^ (2 * n) / r := by
        field_simp; exact h3.symm
      rw [h4, h1]
    have hqpos : (0:ℝ) ≤ (r ^ 2) ^ n / r := by positivity
    have eA : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * ((r ^ 2) ^ n / r)
        ≤ 4 * ((n : ℝ) * ((r ^ 2) ^ n / r)) := by
      have hmul := mul_le_mul_of_nonneg_right hle2 (by positivity : (0:ℝ) ≤ (n : ℝ) * ((r ^ 2) ^ n / r))
      linarith
    have eB : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * |y| ^ (2 * n - 1)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (r ^ (2 * n - 1)) := by
      apply mul_le_mul_of_nonneg_left hpow_le (by positivity)
    calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * |y| ^ (2 * n - 1)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (r ^ (2 * n - 1)) := eB
      _ = 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * ((r ^ 2) ^ n / r) := by
          rw [hpow_eq]
      _ ≤ 4 * ((n : ℝ) * ((r ^ 2) ^ n / r)) := eA
      _ = (4 / r) * ((n : ℝ) * (r ^ 2) ^ n) := by ring
      _ ≤ (4 / r) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (n : ℝ) * (r ^ 2) ^ n ≤ ((n : ℝ) + 1) * (r ^ 2) ^ n :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sq_nonneg r) n)
          exact this

theorem S2term_uniform_bound (r : ℝ) (hr : 0 < r) (n : ℕ) (y : ℝ)
    (hy : y ∈ Metric.ball (0 : ℝ) r) :
    ‖S2term y n‖ ≤ (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n)
      + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
  by_cases hn : n = 0
  · subst hn
    simp only [S2term_zero, norm_zero]
    positivity
  · have hyr0 : |y| ≤ r := le_of_lt ((mem_ball_zero_iff y r).mp hy)
    have hratio := ratio_le n (by omega)
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hcast : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
      have h : 1 ≤ 2 * n := by omega
      have hsub := Nat.cast_sub (R := ℝ) (m := 1) (n := 2 * n) h
      push_cast at hsub ⊢
      linarith
    have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
      simp only [dcoef]; field_simp
    have e1 : (0:ℝ) ≤ 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) := by
      positivity
    have e2 : (0:ℝ) ≤ 2 * (n : ℝ) - 1 := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hnorm : ‖S2term y n‖
        = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ))
          * (2 * (n : ℝ) - 1) * |y| ^ (2 * n - 2) := by
      simp only [S2term, hn, ↓reduceIte, hcast, hd]
      rw [Real.norm_eq_abs]
      simp only [abs_mul, abs_pow, abs_of_nonneg e1, abs_of_nonneg e2]
    rw [hnorm]
    have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
    have hpow_le : |y| ^ (2 * n - 2) ≤ r ^ (2 * n - 2) :=
      pow_le_pow_left₀ (abs_nonneg y) hyr0 _
    have hpow_eq : r ^ (2 * n - 2) = (r ^ 2) ^ n / r ^ 2 := by
      have h1 : r ^ (2 * n) = (r ^ 2) ^ n := by rw [← pow_mul]
      have h2 : 2 * n = (2 * n - 2) + 2 := by omega
      have h3 : r ^ (2 * n) = r ^ (2 * n - 2) * r ^ 2 := by
        conv_lhs => rw [h2]; rw [pow_add]
      have hne : (r ^ 2 : ℝ) ≠ 0 := by positivity
      have h4 : r ^ (2 * n - 2) = r ^ (2 * n) / r ^ 2 := by
        field_simp; exact h3.symm
      rw [h4, h1]
    have hnn21 : (0:ℝ) ≤ (n : ℝ) * (2 * (n : ℝ) - 1) := by
      apply mul_nonneg (by positivity); linarith
    have hstep : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)
        ≤ 4 * ((n : ℝ) * (2 * (n : ℝ) - 1)) := by
      have hmul := mul_le_mul_of_nonneg_right hle2 hnn21
      linarith
    have hmono : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * |y| ^ (2 * n - 2)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * r ^ (2 * n - 2) := by
      apply mul_le_mul_of_nonneg_left hpow_le (by positivity)
    calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * |y| ^ (2 * n - 2)
        ≤ 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1) * r ^ (2 * n - 2) := hmono
      _ = (2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)) * (r ^ (2 * n - 2)) := by ring
      _ = (2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * (2 * (n : ℝ) - 1)) * ((r ^ 2) ^ n / r ^ 2) := by
          rw [hpow_eq]
      _ ≤ (4 * ((n : ℝ) * (2 * (n : ℝ) - 1))) * ((r ^ 2) ^ n / r ^ 2) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (4 / r ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (r ^ 2) ^ n) := by ring
      _ ≤ (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n) + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by
          have hq : (0:ℝ) ≤ (r ^ 2) ^ n := pow_nonneg (sq_nonneg r) n
          have hcoef : (n : ℝ) * (2 * (n : ℝ) - 1) ≤ 2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1) := by
            nlinarith [sq_nonneg (n : ℝ)]
          have hmul2 := mul_le_mul_of_nonneg_right hcoef hq
          have hdiv : (4 / r ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (r ^ 2) ^ n)
              ≤ (4 / r ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (r ^ 2) ^ n) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hmul2]
          calc (4 / r ^ 2) * ((n : ℝ) * (2 * (n : ℝ) - 1) * (r ^ 2) ^ n)
              ≤ (4 / r ^ 2) * ((2 * (n : ℝ) ^ 2 + ((n : ℝ) + 1)) * (r ^ 2) ^ n) := hdiv
            _ = (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n) + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n) := by ring

theorem hasDerivAt_Sfun (x : ℝ) (hx : |x| < 1) : HasDerivAt Sfun (Dfun x) x := by
  set r := (|x| + 1) / 2 with hr_def
  have hr0 : (0:ℝ) < r := by
    have : (0:ℝ) ≤ |x| := abs_nonneg x
    linarith
  have hrr : r < 1 := by
    have : |x| < 1 := hx
    linarith
  have hxr : |x| < r := by linarith [hx]
  have hr2 : r ^ 2 < 1 := by nlinarith [hr0, hrr, sq_nonneg r]
  have hr2nn : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
  set s := Metric.ball (0 : ℝ) r with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hxs : x ∈ s := (mem_ball_zero_iff x r).mpr hxr
  have hgeom := summable_succ_mul_geom (r ^ 2) hr2nn hr2
  have hu : Summable (fun n : ℕ => (4 / r) * (((n : ℝ) + 1) * (r ^ 2) ^ n)) :=
    hgeom.mul_left _
  have hunif : TendstoUniformlyOn (fun N y => ∑ n ∈ Finset.range N, Dterm y n)
      (fun y => ∑' n, Dterm y n) Filter.atTop s :=
    tendstoUniformlyOn_tsum_nat hu (fun n y hy => Dterm_uniform_bound r hr0 n y hy)
  have hderiv_each : ∀ᶠ N in Filter.atTop,
      ∀ y ∈ s, HasDerivAt (fun y => ∑ n ∈ Finset.range N, Aterm y n)
        (∑ n ∈ Finset.range N, Dterm y n) y := by
    apply Filter.Eventually.of_forall
    intro N y _
    have h := HasDerivAt.sum (u := Finset.range N)
      (A := fun n y => Aterm y n) (A' := fun n => Dterm y n)
      (fun i _ => hasDerivAt_Aterm y i)
    have hfun : (∑ i ∈ Finset.range N, fun y => Aterm y i)
        = (fun y => ∑ n ∈ Finset.range N, Aterm y n) := by
      funext y
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hlim : ∀ y ∈ s, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, Aterm y n)
      Filter.atTop (nhds (Sfun y)) := by
    intro y hy
    have hy1 : |y| < 1 := lt_trans ((mem_ball_zero_iff y r).mp hy) hrr
    have hsum := (summable_Aterm y hy1).hasSum
    have htend := hsum.tendsto_sum_nat
    simpa [Sfun] using htend
  have hmain := hasDerivAt_of_tendstoUniformlyOn hs_open hunif hderiv_each hlim hxs
  simpa [Sfun, Dfun] using hmain

theorem hasDerivAt_Dfun (x : ℝ) (hx : |x| < 1) : HasDerivAt Dfun (S2fun x) x := by
  set r := (|x| + 1) / 2 with hr_def
  have hr0 : (0:ℝ) < r := by
    have : (0:ℝ) ≤ |x| := abs_nonneg x
    linarith
  have hrr : r < 1 := by linarith [hx]
  have hxr : |x| < r := by linarith [hx]
  have hr2 : r ^ 2 < 1 := by nlinarith [hr0, hrr, sq_nonneg r]
  have hr2nn : (0:ℝ) ≤ r ^ 2 := sq_nonneg r
  set s := Metric.ball (0 : ℝ) r with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hxs : x ∈ s := (mem_ball_zero_iff x r).mpr hxr
  have hnorm : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2nn]; exact hr2
  have hgeom1 := summable_succ_mul_geom (r ^ 2) hr2nn hr2
  have hgeom2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
  have hu : Summable (fun n : ℕ => (8 / r ^ 2) * ((n : ℝ) ^ 2 * (r ^ 2) ^ n)
      + (4 / r ^ 2) * (((n : ℝ) + 1) * (r ^ 2) ^ n)) :=
    (hgeom2.mul_left _).add (hgeom1.mul_left _)
  have hunif : TendstoUniformlyOn (fun N y => ∑ n ∈ Finset.range N, S2term y n)
      (fun y => ∑' n, S2term y n) Filter.atTop s :=
    tendstoUniformlyOn_tsum_nat hu (fun n y hy => S2term_uniform_bound r hr0 n y hy)
  have hderiv_each : ∀ᶠ N in Filter.atTop,
      ∀ y ∈ s, HasDerivAt (fun y => ∑ n ∈ Finset.range N, Dterm y n)
        (∑ n ∈ Finset.range N, S2term y n) y := by
    apply Filter.Eventually.of_forall
    intro N y _
    have h := HasDerivAt.sum (u := Finset.range N)
      (A := fun n y => Dterm y n) (A' := fun n => S2term y n)
      (fun i _ => hasDerivAt_Dterm y i)
    have hfun : (∑ i ∈ Finset.range N, fun y => Dterm y i)
        = (fun y => ∑ n ∈ Finset.range N, Dterm y n) := by
      funext y
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hlim : ∀ y ∈ s, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, Dterm y n)
      Filter.atTop (nhds (Dfun y)) := by
    intro y hy
    have hy1 : |y| < 1 := lt_trans ((mem_ball_zero_iff y r).mp hy) hrr
    have hsum := (summable_Dterm y hy1).hasSum
    have htend := hsum.tendsto_sum_nat
    simpa [Dfun] using htend
  have hmain := hasDerivAt_of_tendstoUniformlyOn hs_open hunif hderiv_each hlim hxs
  simpa [Dfun, S2fun] using hmain

theorem S2term_one (x : ℝ) : S2term x 1 = 4 := by
  have h1 : S2term x 1 = 2 * dcoef 1 * ((2 * 1 - 1 : ℕ) : ℝ) * x ^ (2 * 1 - 2) := by
    simp [S2term]
  rw [h1]
  norm_num [dcoef_one]

theorem S2term_succ (x : ℝ) (m : ℕ) :
    S2term x (m + 1) = 2 * dcoef (m + 1) * (2 * (m : ℝ) + 1) * x ^ (2 * m) := by
  have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have hcast : (((2 * (m + 1) - 1 : ℕ)) : ℝ) = 2 * (m : ℝ) + 1 := by
    rw [h1]; push_cast; ring
  simp only [S2term, show m + 1 ≠ 0 by omega, ↓reduceIte, hcast, h2]

theorem Dterm_succ (x : ℝ) (m : ℕ) :
    Dterm x (m + 1) = 2 * dcoef (m + 1) * x ^ (2 * m + 1) := by
  have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  simp only [Dterm, show m + 1 ≠ 0 by omega, ↓reduceIte, h1]

theorem ode_S (x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * S2fun x - 3 * x * Dfun x = 4 := by
  have hS2 := summable_S2term x hx
  have hD := summable_Dterm x hx
  have hS2s : Summable (fun m => S2term x (m + 1)) :=
    (summable_nat_add_iff (f := S2term x) 1).mpr hS2
  have hDs : Summable (fun m => Dterm x (m + 1)) :=
    (summable_nat_add_iff (f := Dterm x) 1).mpr hD
  have hS2ss : Summable (fun m => S2term x (m + 1 + 1)) :=
    (summable_nat_add_iff (f := fun m => S2term x (m + 1)) 1).mpr hS2s
  have hshift : ∑' n, S2term x n = ∑' m, S2term x (m + 1) := by
    have h := hS2.tsum_eq_zero_add
    rw [S2term_zero, zero_add] at h
    exact h
  have hpeel : (∑' m, S2term x (m + 1)) = S2term x 1 + ∑' m, S2term x (m + 1 + 1) := by
    simpa using hS2s.tsum_eq_zero_add
  have hDshift : ∑' n, Dterm x n = ∑' m, Dterm x (m + 1) := by
    have h := hD.tsum_eq_zero_add
    rw [Dterm_zero, zero_add] at h
    exact h
  have hB : Summable (fun m => x ^ 2 * S2term x (m + 1)) := hS2s.mul_left _
  have hC : Summable (fun m => (3 * x) * Dterm x (m + 1)) := hDs.mul_left _
  have hBtsum : (∑' m, x ^ 2 * S2term x (m + 1)) = x ^ 2 * (∑' m, S2term x (m + 1)) :=
    hS2s.tsum_mul_left _
  have hCtsum : (∑' m, (3 * x) * Dterm x (m + 1)) = (3 * x) * (∑' m, Dterm x (m + 1)) :=
    hDs.tsum_mul_left _
  have hzero : (fun m => S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)
      - (3 * x) * Dterm x (m + 1)) = fun _ => 0 := by
    funext m
    have e1 := S2term_succ x (m + 1)
    have e2 := S2term_succ x m
    have e3 := Dterm_succ x m
    have hrec := dcoef_rec (m + 1)
    have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hrec
    rw [e1, e2, e3, hcast]
    have pA : x ^ (2 * (m + 1)) = x ^ 2 * x ^ (2 * m) := by
      rw [← pow_add]
      congr 1
      omega
    have pB : x ^ (2 * m + 1) = x ^ (2 * m) * x := by
      rw [← pow_succ]
    rw [pA, pB]
    linear_combination 2 * (x ^ 2 * x ^ (2 * m)) * hrec
  have hsum0 : ∑' m, (S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)
      - (3 * x) * Dterm x (m + 1)) = 0 := by
    rw [hzero]
    exact tsum_zero
  have hAB : Summable (fun m => S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)) :=
    hS2ss.sub hB
  have hdecomp : (∑' m, (S2term x (m + 1 + 1) - x ^ 2 * S2term x (m + 1)
      - (3 * x) * Dterm x (m + 1)))
      = (∑' m, S2term x (m + 1 + 1)) - (∑' m, x ^ 2 * S2term x (m + 1))
        - (∑' m, (3 * x) * Dterm x (m + 1)) := by
    rw [Summable.tsum_sub hAB hC, Summable.tsum_sub hS2ss hB]
  have hpeel4 : (∑' m, S2term x (m + 1)) = 4 + ∑' m, S2term x (m + 1 + 1) := by
    rw [hpeel, S2term_one]
  have hzz : (∑' m, S2term x (m + 1 + 1)) - (∑' m, x ^ 2 * S2term x (m + 1))
      - (∑' m, (3 * x) * Dterm x (m + 1)) = 0 := hdecomp.symm.trans hsum0
  have key : (1 - x ^ 2) * (∑' n, S2term x n) - 3 * x * (∑' n, Dterm x n) = 4 := by
    linear_combination (1 - x ^ 2) * hshift - (3 * x) * hDshift + hpeel4 + hzz + hBtsum + hCtsum
  show (1 - x ^ 2) * S2fun x - 3 * x * Dfun x = 4
  exact key

theorem hpos_of_mem (x : ℝ) (hx : |x| < 1) : (0:ℝ) < 1 - x ^ 2 := by
  have hx2 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
  linarith

theorem hne_one_of_mem (x : ℝ) (hx : |x| < 1) : x ≠ 1 ∧ x ≠ -1 := by
  constructor
  · intro h; rw [h] at hx; norm_num at hx
  · intro h; rw [h] at hx; norm_num at hx

end MetaMathlibExt
