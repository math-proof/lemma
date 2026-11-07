import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Lemma.Complex.Any_All_Eq_Mul_SqrtAdd1SquareDeriv.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.ContDiff_2.Differentiable
open Complex


/--
Catenary from static force balance (悬链线).

Given `Differentiable ℝ T`, `ContDiff ℝ 2 y`, and
\(\partial_x(T e^{i\arctan y'})=i\mu g\sqrt{1+(y')^2}\)
(\(\mu,g:\mathbb{R}^+\)),
the force balance yields \(H\) with \(a=H/(\mu g)\) and \(y''=a^{-1}\sqrt{1+(y')^2}\).
That scale is nonzero, and solving the ODE gives
\(y(x)=a\cosh((x-x_0)/a)+b\) for some \(x_0,b\in\mathbb{R}\).
-/
@[path]
private lemma main
  {μ g : ℝ⁺}
  {T y : ℝ → ℝ}
-- given
  (hT : Differentiable ℝ T)
  (hy : ContDiff ℝ 2 y)
  (h_force : ∀ x,
    ∂[x] (T x * exp (I * (∂[x] y x).arctan)) =
      I * (μ * √(1 + (∂[x] y x) ^ 2) * g)) :
-- imply
  ∃ H x₀ b : ℝ,
    let a := H / (μ * g)
    y = fun x => a * Real.cosh ((x - x₀) / a) + b := by
-- proof
  obtain ⟨H, hode⟩ :=
    Any_All_Eq_Mul_SqrtAdd1SquareDeriv.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.ContDiff_2.Differentiable
      hT hy h_force
  set a : ℝ := H / (μ * g)
  have hy1 : Differentiable ℝ y := hy.differentiable (by decide)
  have hy1' : Differentiable ℝ (deriv y) := hy.differentiable_deriv_two
  have ha0 : a ≠ 0 := by
    intro ha
    have hode0 : ∀ x, deriv (deriv y) x = 0 := by
      intro x
      have hinv : a⁻¹ = 0 := inv_eq_zero.mpr ha
      have hx := hode x
      simpa [a, hinv, show ∂[x, x] y x = deriv (deriv y) x from rfl] using hx
    have hyconst : ∀ x, deriv y x = deriv y 0 := fun x =>
      is_const_of_deriv_eq_zero hy1' hode0 x 0
    set u : ℝ := deriv y 0
    set c : ℂ := exp (I * Real.arctan u)
    have hcos_ne : Real.cos (Real.arctan u) ≠ 0 := by
      rw [Real.cos_arctan]
      refine div_ne_zero one_ne_zero ?_
      exact (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (sq_nonneg _)))).ne'
    have hspos : 0 < √(1 + u ^ 2) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (sq_nonneg _)))
    have him_ne : μ * √(1 + u ^ 2) * g ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ne_of_gt μ.property) hspos.ne') (ne_of_gt g.property)
    have hc : c =
        ↑(Real.cos (Real.arctan u)) + ↑(Real.sin (Real.arctan u)) * I := by
      unfold c
      rw [mul_comm I]
      simpa using exp_ofReal_mul_I (Real.arctan u)
    have hfun : (fun ξ => (T ξ : ℂ) * exp (I * (∂[ξ] y ξ).arctan)) =
        fun ξ => (T ξ : ℂ) * c := by
      funext ξ
      have hξ : ∂[ξ] y ξ = u := by simpa [u] using hyconst ξ
      simp [c, hξ]
    have hderiv : deriv (fun ξ => (T ξ : ℂ) * c) 0 =
        I * ↑(μ * √(1 + u ^ 2) * g) := by
      have h0 := h_force 0
      simpa [hfun, u] using h0
    have hmul : deriv (fun ξ : ℝ => (T ξ : ℂ) * c) (0 : ℝ) =
        ↑(deriv T (0 : ℝ)) * c := by
      have hTc : HasDerivAt (fun ξ => (T ξ : ℂ)) ↑(deriv T 0) 0 :=
        (hT 0).hasDerivAt.ofReal_comp
      simpa using (hTc.mul_const c).deriv
    have hlin : ↑(deriv T 0) * c = I * ↑(μ * √(1 + u ^ 2) * g) := by
      rw [← hmul]
      simpa using hderiv
    have hlin' : ↑(deriv T 0) *
        (↑(Real.cos (Real.arctan u)) + ↑(Real.sin (Real.arctan u)) * I) =
        I * ↑(μ * √(1 + u ^ 2) * g) := by
      simpa [hc] using hlin
    have hre : deriv T 0 * Real.cos (Real.arctan u) = 0 := by
      have h := congrArg re hlin'
      simp only [mul_add, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im] at h
      simpa using h
    have him : deriv T 0 * Real.sin (Real.arctan u) =
        μ * √(1 + u ^ 2) * g := by
      have h := congrArg im hlin'
      simp only [mul_add, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im] at h
      simpa using h
    have hT0 : deriv T 0 = 0 := by
      apply mul_right_cancel₀ hcos_ne
      simpa using hre
    apply him_ne
    rw [← him, hT0]
    ring
  have hode_deriv : ∀ x, deriv (deriv y) x =
      a⁻¹ * √(1 + (deriv y x) ^ 2) := by
    intro x
    simpa [a, show ∂[x, x] y x = deriv (fun x => deriv y x) x from rfl] using hode x
  set v : ℝ → ℝ := deriv y
  have hv' : ∀ x, ∂[x] v x = a⁻¹ * √(1 + v x ^ 2) := hode_deriv
  set w : ℝ → ℝ := fun x => Real.arsinh (v x) - x / a
  have hw' : ∀ x, HasDerivAt w 0 x := by
    intro x
    have hdiv : HasDerivAt (fun ξ => ξ / a) a⁻¹ x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const a⁻¹
    have hars : HasDerivAt (fun ξ => Real.arsinh (v ξ))
      ((√(1 + v x ^ 2))⁻¹ * ∂[x] v x) x := by
      convert (Real.hasDerivAt_arsinh (v x)).comp x (hy1' x).hasDerivAt with t
      rfl
    have hsub := hars.sub hdiv
    convert hsub.congr_deriv _ using 0
    rw [hv' x]
    have hspos : 0 < √(1 + v x ^ 2) :=
      Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (sq_nonneg _)))
    field_simp [hspos.ne', ha0]
    ring
  have hw_diff : Differentiable ℝ w := fun x => (hw' x).differentiableAt
  have hw0 : ∀ x, ∂[x] w x = 0 := fun x => (hw' x).deriv
  have hw_const : ∀ x, w x = w 0 := fun x =>
    is_const_of_deriv_eq_zero hw_diff hw0 x 0
  set c : ℝ := Real.arsinh (v 0)
  have harsinh : ∀ x, Real.arsinh (v x) = x / a + c := by
    intro x
    have hx := hw_const x
    simp only [w, zero_div, sub_zero] at hx
    linarith
  set x₀ : ℝ := -a * c
  have hv : ∀ x, v x = Real.sinh ((x - x₀) / a) := by
    intro x
    have : (x - x₀) / a = x / a + c := by
      simp only [x₀]
      field_simp [ha0]
      ring
    rw [← Real.sinh_arsinh (v x), harsinh, this]
  set z : ℝ → ℝ := fun x => y x - a * Real.cosh ((x - x₀) / a)
  have hz' : ∀ x, HasDerivAt z 0 x := by
    intro x
    have hyx : HasDerivAt y (v x) x := (hy1 x).hasDerivAt
    have hdiv : HasDerivAt (fun ξ => (ξ - x₀) / a) a⁻¹ x := by
      simpa [div_eq_mul_inv, sub_eq_add_neg] using
        ((hasDerivAt_id x).sub (hasDerivAt_const x x₀)).mul_const a⁻¹
    have hcosh : HasDerivAt (fun ξ => Real.cosh ((ξ - x₀) / a))
      (Real.sinh ((x - x₀) / a) * a⁻¹) x := by
      convert (Real.hasDerivAt_cosh ((x - x₀) / a)).comp x hdiv with t
      rfl
    have hA : HasDerivAt (fun ξ => a * Real.cosh ((ξ - x₀) / a))
      (a * (Real.sinh ((x - x₀) / a) * a⁻¹)) x :=
      hcosh.const_mul a
    have hA' : HasDerivAt (fun ξ => a * Real.cosh ((ξ - x₀) / a))
      (Real.sinh ((x - x₀) / a)) x := by
      convert hA using 1
      field_simp [ha0]
    have hsub := hyx.sub hA'
    convert hsub.congr_deriv _ using 0
    rw [hv x]
    ring
  have hz_diff : Differentiable ℝ z := fun x => (hz' x).differentiableAt
  have hz0d : ∀ x, ∂[x] z x = 0 := fun x => (hz' x).deriv
  have hz_const : ∀ x, z x = z 0 := fun x =>
    is_const_of_deriv_eq_zero hz_diff hz0d x 0
  refine ⟨H, x₀, z 0, ?_⟩
  intro a
  funext x
  have hx := hz_const x
  -- hx : z x = z 0, with z ξ = y ξ - a * cosh((ξ - x₀)/a)
  calc
    _ = z x + a * Real.cosh ((x - x₀) / a) := by
      simp only [z]; ring
    _ = z 0 + a * Real.cosh ((x - x₀) / a) := by rw [hx]
    _ = a * Real.cosh ((x - x₀) / a) + z 0 := by ring


-- created on 2026-11-05
-- updated on 2026-11-07
