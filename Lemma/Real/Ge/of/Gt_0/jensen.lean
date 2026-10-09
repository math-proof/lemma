import Lemma.Real.Ge.of.Le.Gt_0.jensen


/--
Jensen's inequality (two-point form): if `f'' > 0` on `(a, b)`, `x₀ x₁ ∈ (a, b)`
and `w ∈ [0, 1]`, then `w * f x₀ + (1 - w) * f x₁ ≥ f (w * x₀ + (1 - w) * x₁)`.
-/
@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {x₀ x₁ : ℝ}
  {w : ℝ}
-- given
  (h₀ : ContinuousOn f (Set.Ioo a b))
  (h₁ : ∀ x ∈ Set.Ioo a b, 0 < deriv^[2] f x)
  (h₂ : w ∈ Set.Icc (0 : ℝ) 1)
  (h₃ : x₀ ∈ Set.Ioo a b)
  (h₄ : x₁ ∈ Set.Ioo a b) :
-- imply
  w * f x₀ + (1 - w) * f x₁ ≥ f (w * x₀ + (1 - w) * x₁) := by
-- proof
  if h : x₀ ≤ x₁ then
    exact Real.Ge.of.Le.Gt_0.jensen h₀ h₁ h₂ h₃ h₄
  else
    have h : x₁ ≤ x₀ := le_of_not_ge h
    have h₅ : 1 - w ∈ Set.Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr h₂.2, sub_le_self 1 h₂.1⟩
    have h₆ := Real.Ge.of.Le.Gt_0.jensen h₀ h₁ h₅ h₄ h₃
    rw [sub_sub_self] at h₆
    rw [show w * x₀ + (1 - w) * x₁ = (1 - w) * x₁ + w * x₀ from add_comm _ _]
    linarith [h₆]


-- created on 2020-05-12
