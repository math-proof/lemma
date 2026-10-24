/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/ExplicitEuler.lean -/


import Lemma.Real.ODE.ExplicitEuler
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set
open MathlibExt.Analysis.ODE.ExplicitEulerWanted

-- The exponential solution has a uniform quadratic explicit-Euler local error.
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Ioc 0 1, ∀ t ∈ Icc 0 1, t + h ≤ 1 →
      ‖Real.exp (t + h) - (Real.exp t + h • Real.exp t)‖ ≤ C * h ^ 2 := by
  have hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Real.exp (Real.exp t) t :=
    fun t _ ↦ Real.hasDerivAt_exp t
  simpa using ODE.exists_explicitEuler_localTruncationError_le
    (fun (_ : ℝ) (y : ℝ) ↦ y) 0 1 (by norm_num) (by fun_prop) Real.exp hx

-- Euler powers instantiate the numerical recurrence for the scalar equation `x' = x`.
example :
    ∃ x : ℝ → ℝ, x 0 = 1 ∧
      (∀ t ∈ Icc 0 1, HasDerivAt x (x t) t) ∧
      ∃ C : ℝ, ∀ h ∈ Ioc 0 1, ∀ n : ℕ, (n : ℝ) * h ≤ 1 →
        ‖(1 + h) ^ n - x ((n : ℝ) * h)‖ ≤ C * h := by
  have hf : ContDiff ℝ 2 (Function.uncurry (fun (_ : ℝ) (y : ℝ) ↦ y)) := by
    fun_prop
  have hlip : ∀ t ∈ Icc (0 : ℝ) 1,
      LipschitzWith (1 : NNReal) (fun y : ℝ ↦ y) := fun _ _ ↦ LipschitzWith.id
  obtain ⟨x, hx0, hx, C, hC⟩ := explicit_euler_first_order_convergence
    (fun (_ : ℝ) (y : ℝ) ↦ y) 0 1 1 1 (by norm_num) hf hlip
  refine ⟨x, hx0, by simpa using hx, C, ?_⟩
  intro h hh n hn
  have hrec : ∀ k : ℕ, (1 + h) ^ (k + 1) =
      (1 + h) ^ k + h • (1 + h) ^ k := by
    intro k
    rw [pow_succ]
    change (1 + h) ^ k * (1 + h) = (1 + h) ^ k + h * (1 + h) ^ k
    ring
  simpa using hC h (by simpa using hh) (fun k ↦ (1 + h) ^ k) (by simp) (by simpa using hrec)
    n (by simpa using hn)
