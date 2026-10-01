import Lemma.Real.Imp.of.Gt_0.jensen.induct


/--
Jensen's inequality: if `f'' > 0` on `(a, b)`, `w ≥ 0` and `x i ∈ (a, b)`,
then `∑ i < n, w i = 1` implies
`∑ i < n, w i * f (x i) ≥ f (∑ i < n, w i * x i)`.
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
  (h₂ : ∀ i, 0 ≤ w i)
  (h₃ : ∀ i, x i ∈ Set.Ioo a b) :
-- imply
  (∑ i ∈ Finset.range n, w i = 1) →
    ∑ i ∈ Finset.range n, w i * f (x i) ≥ f (∑ i ∈ Finset.range n, w i * x i) := by
-- proof
  intro h₄
  exact Real.Imp.of.Gt_0.jensen.induct h₀ h₁ h₃ ⟨h₄, fun i _ => h₂ i⟩


-- created on 2026-10-01
