import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [Nonempty (Fin m)] [Nonempty (Fin (n + m))]
  {x : Fin n → ℝ}
  {y : Fin m → ℝ}
  {j₀ : Fin m}
-- given
  (h₀ : ∀ j, j ≠ j₀ → y j < y j₀)
  (h₁ : ∀ i, x i < y j₀) :
-- imply
  ((ArgMax Set.univ (Fin.append x y) : Fin (n + m)) : ℕ) = n + ((ArgMax Set.univ y : Fin m) : ℕ) := by
-- proof
  have hA : ArgMax Set.univ y = j₀ := by
    have hs : ArgMax Set.univ y ∈ Set.univ ∧ ∀ z ∈ Set.univ, y z ≤ y (ArgMax Set.univ y) := by
      refine Classical.epsilon_spec (p := fun k => k ∈ Set.univ ∧ ∀ z ∈ Set.univ, y z ≤ y k) ⟨j₀, trivial, fun z _ => ?_⟩
      if hz : z = j₀ then
        rw [hz]
      else
        exact (h₀ z hz).le
    by_contra hne
    exact absurd (hs.2 j₀ trivial) (not_le.mpr (h₀ _ hne))
  have hB : ArgMax Set.univ (Fin.append x y) = Fin.natAdd n j₀ := by
    have hs : ArgMax Set.univ (Fin.append x y) ∈ Set.univ ∧
        ∀ z ∈ Set.univ, Fin.append x y z ≤ Fin.append x y (ArgMax Set.univ (Fin.append x y)) := by
      refine Classical.epsilon_spec (p := fun k => k ∈ Set.univ ∧ ∀ z ∈ Set.univ, Fin.append x y z ≤ Fin.append x y k)
        ⟨Fin.natAdd n j₀, trivial, fun z _ => ?_⟩
      induction z using Fin.addCases with
      | left i =>
        simp only [Fin.append_left, Fin.append_right]
        exact (h₁ i).le
      | right j =>
        simp only [Fin.append_right]
        if hj : j = j₀ then
          rw [hj]
        else
          exact (h₀ j hj).le
    have h₂ := hs.2 (Fin.natAdd n j₀) trivial
    generalize ArgMax Set.univ (Fin.append x y) = k at h₂ ⊢
    induction k using Fin.addCases with
    | left i =>
      simp only [Fin.append_left, Fin.append_right] at h₂
      exact absurd h₂ (not_le.mpr (h₁ i))
    | right j =>
      simp only [Fin.append_right] at h₂
      if hj : j = j₀ then
        rw [hj]
      else
        exact absurd h₂ (not_le.mpr (h₀ j hj))
  rw [hB, hA]
  rfl


-- created on 2021-12-20
