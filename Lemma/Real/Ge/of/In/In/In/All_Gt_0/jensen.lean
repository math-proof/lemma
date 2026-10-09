import Lemma.Real.Ge.of.Gt_0.jensen


/--
Jensen's inequality (two-point form): if `f'' > 0` on all of `(a, b)`, `x₀ x₁ ∈ (a, b)`
and `w ∈ [0, 1)`, then `w * f x₀ + (1 - w) * f x₁ ≥ f (w * x₀ + (1 - w) * x₁)`.
-/
@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {x₀ x₁ : ℝ}
  {w : ℝ}
-- given
  (h₀ : w ∈ Set.Ico (0 : ℝ) 1)
  (h₁ : x₀ ∈ Set.Ioo a b)
  (h₂ : x₁ ∈ Set.Ioo a b)
  (h₃ : ContinuousOn f (Set.Ioo a b))
  (h₄ : ∀ x ∈ Set.Ioo a b, 0 < deriv^[2] f x) :
-- imply
  w * f x₀ + (1 - w) * f x₁ ≥ f (w * x₀ + (1 - w) * x₁) := by
-- proof
  exact Real.Ge.of.Gt_0.jensen h₃ h₄ ⟨h₀.1, h₀.2.le⟩ h₁ h₂


-- created on 2020-05-12
