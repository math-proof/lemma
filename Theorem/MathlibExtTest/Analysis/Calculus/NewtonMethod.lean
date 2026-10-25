/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/NewtonMethod.lean -/


import Theorem.Analysis.Calculus.NewtonMethod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
open MetaMathlibExt


-- Newton iteration for `x² - 4` converges to `2` from every sufficiently close start.
example :
    ∃ δ > 0, ∀ x₀ ∈ Set.Ioo (2 - δ) (2 + δ),
      ∀ X : ℕ → ℝ, X 0 = x₀ →
        (∀ n, X (n + 1) = X n - (X n ^ 2 - 4) /
          deriv (fun x : ℝ => x ^ 2 - 4) (X n)) →
        Filter.Tendsto X Filter.atTop (nhds 2) := by
  have hderiv_sq_sub_four (y : ℝ) :
      deriv (fun x : ℝ => x ^ 2 - 4) y = 2 * y := by
    have hpow : deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
      change deriv ((id : ℝ → ℝ) ^ 2) y = 2 * y
      rw [deriv_pow (differentiableAt_id (𝕜 := ℝ)) 2, deriv_id]
      norm_num
    change deriv ((fun x : ℝ => x ^ 2) - fun _ => 4) y = 2 * y
    rw [deriv_sub (by fun_prop) (by fun_prop), hpow, deriv_const]
    ring
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 2 - 4) := by fun_prop
  have hroot : (2 : ℝ) ^ 2 - 4 = 0 := by norm_num
  have hderiv : deriv (fun x : ℝ => x ^ 2 - 4) 2 ≠ 0 := by
    rw [hderiv_sq_sub_four]
    norm_num
  obtain ⟨δ, hδ, _, hmain⟩ :=
    newton_method_local_quadratic_convergence hf hroot hderiv
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ X hX₀ hrec
  exact (hmain x₀ hx₀ X hX₀ hrec).2.2

-- The one-step bound controls the concrete Newton update from `3` toward the root `2`.
example :
    |(3 : ℝ) - ((3 : ℝ) ^ 2 - 4) /
      deriv (fun x : ℝ => x ^ 2 - 4) 3 - 2| ≤ 1 / 3 := by
  have hderiv_sq_sub_four (y : ℝ) :
      deriv (fun x : ℝ => x ^ 2 - 4) y = 2 * y := by
    have hpow : deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
      change deriv ((id : ℝ → ℝ) ^ 2) y = 2 * y
      rw [deriv_pow (differentiableAt_id (𝕜 := ℝ)) 2, deriv_id]
      norm_num
    change deriv ((fun x : ℝ => x ^ 2) - fun _ => 4) y = 2 * y
    rw [deriv_sub (by fun_prop) (by fun_prop), hpow, deriv_const]
    ring
  have hf : Differentiable ℝ (fun x : ℝ => x ^ 2 - 4) := by fun_prop
  have hK : LipschitzOnWith (2 : NNReal)
      (deriv (fun x : ℝ => x ^ 2 - 4)) (Set.uIcc 2 3) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a _ b _
    rw [hderiv_sq_sub_four, hderiv_sq_sub_four, Real.dist_eq, Real.dist_eq]
    change |2 * a - 2 * b| ≤ (2 : ℝ) * |a - b|
    calc
      |2 * a - 2 * b| = |(2 : ℝ) * (a - b)| := by
        congr 1
        ring
      _ = 2 * |a - b| := by
        rw [abs_mul]
        norm_num
      _ ≤ 2 * |a - b| := le_rfl
  have h := newton_step_sub_root_abs_le (c := (2 : ℝ)) (x := 3)
    (m := 6) (K := (2 : NNReal)) hf (by norm_num) (by norm_num) hK (by
      rw [hderiv_sq_sub_four]
      norm_num)
  rw [hderiv_sq_sub_four] at h ⊢
  calc
    |(3 : ℝ) - ((3 : ℝ) ^ 2 - 4) / (2 * 3) - 2| ≤
        (2 / 6 : ℝ) * |(3 : ℝ) - 2| ^ 2 := by simpa using h
    _ = 1 / 3 := by norm_num

