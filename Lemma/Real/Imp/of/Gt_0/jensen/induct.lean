import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import sympy.Basic


/--
Jensen's inequality (induction core): if `f'' > 0` on `(a, b)` and `x i ∈ (a, b)`,
then `∑ i < n, w i = 1` together with `∀ i < n, w i ≥ 0` implies
`∑ i < n, w i * f (x i) ≥ f (∑ i < n, w i * x i)`.
-/
@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {w x : ℕ → ℝ}
  {n : ℕ}
-- given
  (h₀ : ContinuousOn f (Set.Ioo a b))
  (h₁ : ∀ x ∈ Set.Ioo a b, 0 < deriv^[2] f x)
  (h₂ : ∀ i, x i ∈ Set.Ioo a b) :
-- imply
  (∑ i ∈ Finset.range n, w i = 1 ∧ ∀ i ∈ Finset.range n, 0 ≤ w i) →
    ∑ i ∈ Finset.range n, w i * f (x i) ≥ f (∑ i ∈ Finset.range n, w i * x i) := by
-- proof
  rintro ⟨h₃, h₄⟩
  have h := (strictConvexOn_of_deriv2_pos' (convex_Ioo a b) h₀ h₁).convexOn.map_sum_le h₄ h₃ fun i _ => h₂ i
  simpa [smul_eq_mul] using h


-- created on 2020-06-01
