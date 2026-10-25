/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/GradientDescent.lean -/


import Theorem.Analysis.Convex.GradientDescent
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Mul


namespace MetaMathlibExt

-- The quadratic objective with a half step satisfies the first-iterate rate.
example (x₀ : ℝ) : (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ * x₀) ^ 2 ≤ ‖x₀‖ ^ 2 := by
  let f : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2
  let X : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * x₀
  have hconvex : ConvexOn ℝ Set.univ f := by
    have hsquare : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      (show Even 2 by norm_num).convexOn_pow
    simpa [f, smul_eq_mul] using hsquare.smul (c := (1 / 2 : ℝ)) (by norm_num)
  have hdiff : Differentiable ℝ f := by
    intro x
    simp [f]
  have hgradient (x : ℝ) : gradient f x = x := by
    rw [gradient_eq_deriv']
    simp [f]
  have hsmooth : LipschitzWith (1 : NNReal) (gradient f) := by
    rw [show gradient f = id by ext x; exact hgradient x]
    exact LipschitzWith.id
  have hX : ∀ k, X (k + 1) = X k - (1 / 2 : ℝ) • gradient f (X k) := by
    intro k
    rw [hgradient]
    simp only [X, pow_succ, smul_eq_mul]
    ring
  have hrate := gradient_descent_convex_sublinear_rate
    (E := ℝ) (f := f) (L := 1) (by norm_num) hconvex hdiff hsmooth
    (xstar := 0) (by
      intro x
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, f]
      positivity) (η := 1 / 2) (by norm_num)
    (X := X) hX 1 (by norm_num)
  simpa [f, X] using hrate

-- The same quadratic objective with two half steps satisfies the second-iterate rate.
example (x₀ : ℝ) :
    (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹ ^ 2 * x₀) ^ 2 ≤ ‖x₀‖ ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2
  let X : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * x₀
  have hconvex : ConvexOn ℝ Set.univ f := by
    have hsquare : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
      (show Even 2 by norm_num).convexOn_pow
    simpa [f, smul_eq_mul] using hsquare.smul (c := (1 / 2 : ℝ)) (by norm_num)
  have hdiff : Differentiable ℝ f := by
    intro x
    simp [f]
  have hgradient (x : ℝ) : gradient f x = x := by
    rw [gradient_eq_deriv']
    simp [f]
  have hsmooth : LipschitzWith (1 : NNReal) (gradient f) := by
    rw [show gradient f = id by ext x; exact hgradient x]
    exact LipschitzWith.id
  have hX : ∀ k, X (k + 1) = X k - (1 / 2 : ℝ) • gradient f (X k) := by
    intro k
    rw [hgradient]
    simp only [X, pow_succ, smul_eq_mul]
    ring
  have hrate := gradient_descent_convex_sublinear_rate
    (E := ℝ) (f := f) (L := 1) (by norm_num) hconvex hdiff hsmooth
    (xstar := 0) (by
      intro x
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, f]
      positivity) (η := 1 / 2) (by norm_num)
    (X := X) hX 2 (by norm_num)
  simpa [f, X] using hrate

end MetaMathlibExt
