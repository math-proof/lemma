import Lemma.Real.Imp.of.Gt_0.jensen


/--
Jensen's inequality: if `f'' > 0` on `(a, b)`, `w ≥ 0` with `∑ i < n, w i = 1`
and `x i ∈ (a, b)`, then `∑ i < n, w i * f (x i) ≥ f (∑ i < n, w i * x i)`.
-/
@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {w x : ℕ → ℝ}
  {n : ℕ}
-- given
  (h₀ : ContinuousOn f (Set.Ioo a b))
  (h₁ : ∀ x ∈ Set.Ioo a b, 0 < deriv^[2] f x)
  (h₂ : ∑ i ∈ Finset.range n, w i = 1)
  (h₃ : ∀ i, 0 ≤ w i)
  (h₄ : ∀ i, x i ∈ Set.Ioo a b) :
-- imply
  ∑ i ∈ Finset.range n, w i * f (x i) ≥ f (∑ i ∈ Finset.range n, w i * x i) := by
-- proof
  exact Real.Imp.of.Gt_0.jensen h₀ h₁ h₃ h₄ h₂


-- created on 2020-06-02
