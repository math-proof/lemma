import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Notation.Analysis.Real.Numbers
import Syntax.Analysis.Calculus.Deriv.Operators
import Initialize.Tactic.Attr.Basic


/--
Catenary general solution (悬链线): if \(y'' = a^{-1}\sqrt{1+(y')^2}\) for
\(a:\mathbb{R}^+\) and \(y\) is \(C^2\), then
\(y(x)=a\cosh((x-x_0)/a)+b\) for some \(x_0,b\in\mathbb{R}\).
-/
@[path]
private lemma main
  {a : ℝ⁺}
  {y : ℝ → ℝ}
-- given
  (hode : ∀ x, ∂[x, x] y x = (a : ℝ)⁻¹ * √(1 + (∂[x] y x) ^ 2))
  (hy : ContDiff ℝ 2 y) :
-- imply
  ∃ x₀ b : ℝ, y = fun x => (a : ℝ) * Real.cosh ((x - x₀) / a) + b := by
-- proof
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt a.property
  have hy1 : Differentiable ℝ y := hy.differentiable (by decide)
  have hy1' : Differentiable ℝ (deriv y) := hy.differentiable_deriv_two
  have hode_deriv : ∀ x, deriv (deriv y) x =
      (a : ℝ)⁻¹ * √(1 + (deriv y x) ^ 2) := by
    intro x
    simpa [show ∂[x, x] y x = deriv (fun x => deriv y x) x from rfl] using hode x
  set v : ℝ → ℝ := deriv y
  have hv' : ∀ x, ∂[x] v x = (a : ℝ)⁻¹ * √(1 + v x ^ 2) := hode_deriv
  set w : ℝ → ℝ := fun x => Real.arsinh (v x) - x / a
  have hw' : ∀ x, HasDerivAt w 0 x := by
    intro x
    have hdiv : HasDerivAt (fun ξ => ξ / (a : ℝ)) (a : ℝ)⁻¹ x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (a : ℝ)⁻¹
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
  set x₀ : ℝ := -(a : ℝ) * c
  have hv : ∀ x, v x = Real.sinh ((x - x₀) / a) := by
    intro x
    have : (x - x₀) / a = x / a + c := by
      simp only [x₀]
      field_simp [ha0]
      ring
    rw [← Real.sinh_arsinh (v x), harsinh, this]
  set z : ℝ → ℝ := fun x => y x - (a : ℝ) * Real.cosh ((x - x₀) / a)
  have hz' : ∀ x, HasDerivAt z 0 x := by
    intro x
    have hyx : HasDerivAt y (v x) x := (hy1 x).hasDerivAt
    have hdiv : HasDerivAt (fun ξ => (ξ - x₀) / (a : ℝ)) (a : ℝ)⁻¹ x := by
      simpa [div_eq_mul_inv, sub_eq_add_neg] using
        ((hasDerivAt_id x).sub (hasDerivAt_const x x₀)).mul_const (a : ℝ)⁻¹
    have hcosh : HasDerivAt (fun ξ => Real.cosh ((ξ - x₀) / a))
      (Real.sinh ((x - x₀) / a) * (a : ℝ)⁻¹) x := by
      convert (Real.hasDerivAt_cosh ((x - x₀) / a)).comp x hdiv with t
      rfl
    have hA : HasDerivAt (fun ξ => (a : ℝ) * Real.cosh ((ξ - x₀) / a))
      ((a : ℝ) * (Real.sinh ((x - x₀) / a) * (a : ℝ)⁻¹)) x :=
      hcosh.const_mul (a : ℝ)
    have hA' : HasDerivAt (fun ξ => (a : ℝ) * Real.cosh ((ξ - x₀) / a))
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
  refine ⟨x₀, z 0, ?_⟩
  funext x
  have hx := hz_const x
  -- hx : z x = z 0, with z ξ = y ξ - a * cosh((ξ - x₀)/a)
  calc
    _ = z x + (a : ℝ) * Real.cosh ((x - x₀) / a) := by
      simp only [z]; ring
    _ = z 0 + (a : ℝ) * Real.cosh ((x - x₀) / a) := by rw [hx]
    _ = (a : ℝ) * Real.cosh ((x - x₀) / a) + z 0 := by ring


-- created on 2026-11-05
