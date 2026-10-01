import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import sympy.Basic


/--
Jensen's inequality (concave form): if `f'' < 0` on `(a, b)`, `w ≥ 0` with `∑ i < n, w i = 1`
and `x i ∈ (a, b)`, then `∑ i < n, w i * f (x i) ≤ f (∑ i < n, w i * x i)`.
-/
@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {w x : ℕ → ℝ}
  {n : ℕ}
-- given
  (h₀ : ContinuousOn f (Set.Ioo a b))
  (h₁ : ∀ x ∈ Set.Ioo a b, deriv^[2] f x < 0)
  (h₂ : ∑ i ∈ Finset.range n, w i = 1)
  (h₃ : ∀ i, 0 ≤ w i)
  (h₄ : ∀ i, x i ∈ Set.Ioo a b) :
-- imply
  ∑ i ∈ Finset.range n, w i * f (x i) ≤ f (∑ i ∈ Finset.range n, w i * x i) := by
-- proof
  have h := (strictConcaveOn_of_deriv2_neg' (convex_Ioo a b) h₀ h₁).concaveOn.le_map_sum (fun i _ => h₃ i) h₂ fun i _ => h₄ i
  simpa [smul_eq_mul] using h


-- created on 2020-06-27
