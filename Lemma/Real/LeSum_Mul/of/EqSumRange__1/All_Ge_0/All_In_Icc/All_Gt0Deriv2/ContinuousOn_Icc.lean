import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Theorem.Function


/--
Jensen's inequality (concave form): if `f` is continuous on `[a, b]` and `f'' < 0` on `(a, b)`,
`w ≥ 0` with `∑ i < n, w[i] = 1` and `x[i] ∈ [a, b]`, then
`∑ i < n, w[i] * f x[i] ≤ f (∑ i < n, w[i] * x[i])`.
-/
@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {w x : ℕ ⇀ ℝ}
  {n : ℕ}
-- given
  (h₀ : ContinuousOn f (Set.Icc a b))
  (h₁ : ∀ y ∈ Set.Ioo a b, deriv^[2] f y < 0)
  (h₂ : ∀ i, x[i] ∈ Set.Icc a b)
  (h₃ : ∀ i, 0 ≤ w[i])
  (h₄ : ∑ i ∈ Finset.range n, w[i] = 1) :
-- imply
  ∑ i ∈ Finset.range n, w[i] * f x[i] ≤ f (∑ i ∈ Finset.range n, w[i] * x[i]) := by
-- proof
  simpa [smul_eq_mul] using
    (strictConcaveOn_of_deriv2_neg (convex_Icc a b) h₀ fun y hy => by
          rw [interior_Icc] at hy
          apply h₁ y hy).concaveOn.le_map_sum
      (fun i _ => h₃ i) h₄ fun i _ => h₂ i


-- created on 2020-06-27
-- updated on 2026-10-23
