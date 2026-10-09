import sympy.Basic
import sympy.concrete.expr_with_limits


@[path]
private lemma main
  [Nonempty (Fin n)] [Nonempty (Fin (n + b))]
  {x : Fin n → ℝ}
  {i₀ : Fin n}
-- given
  (h₀ : ∀ j, j ≠ i₀ → x j < x i₀)
  (h₁ : x i₀ > 0) :
-- imply
  ((ArgMax Set.univ (Fin.append x (0 : Fin b → ℝ)) : Fin (n + b)) : ℕ) = ((ArgMax Set.univ x : Fin n) : ℕ) := by
-- proof
  have hA : ArgMax Set.univ x = i₀ := by
    have hs : ArgMax Set.univ x ∈ Set.univ ∧ ∀ y ∈ Set.univ, x y ≤ x (ArgMax Set.univ x) := by
      refine Classical.epsilon_spec (p := fun k => k ∈ Set.univ ∧ ∀ y ∈ Set.univ, x y ≤ x k) ⟨i₀, trivial, fun y _ => ?_⟩
      if hy : y = i₀ then
        rw [hy]
      else
        exact (h₀ y hy).le
    by_contra hne
    exact absurd (hs.2 i₀ trivial) (not_le.mpr (h₀ _ hne))
  have hB : ArgMax Set.univ (Fin.append x (0 : Fin b → ℝ)) = Fin.castAdd b i₀ := by
    have hs : ArgMax Set.univ (Fin.append x (0 : Fin b → ℝ)) ∈ Set.univ ∧
        ∀ y ∈ Set.univ, Fin.append x (0 : Fin b → ℝ) y ≤ Fin.append x (0 : Fin b → ℝ) (ArgMax Set.univ (Fin.append x (0 : Fin b → ℝ))) := by
      refine Classical.epsilon_spec (p := fun k => k ∈ Set.univ ∧ ∀ y ∈ Set.univ, Fin.append x (0 : Fin b → ℝ) y ≤ Fin.append x (0 : Fin b → ℝ) k)
        ⟨Fin.castAdd b i₀, trivial, fun y _ => ?_⟩
      induction y using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        if hj : j = i₀ then
          rw [hj]
        else
          exact (h₀ j hj).le
      | right j =>
        simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
        exact h₁.le
    have h₂ := hs.2 (Fin.castAdd b i₀) trivial
    generalize ArgMax Set.univ (Fin.append x (0 : Fin b → ℝ)) = k at h₂ ⊢
    induction k using Fin.addCases with
    | left j =>
      simp only [Fin.append_left] at h₂
      if hj : j = i₀ then
        rw [hj]
      else
        exact absurd h₂ (not_le.mpr (h₀ j hj))
    | right j =>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply] at h₂
      exact absurd h₂ (not_le.mpr h₁)
  rw [hB, hA]
  rfl


-- created on 2021-12-20
