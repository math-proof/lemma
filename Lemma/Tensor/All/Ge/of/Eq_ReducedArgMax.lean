import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {x : Fin n → ℝ}
  {M : Fin n}
-- given
  (h : M = ArgMax Set.univ x) :
-- imply
  ∀ k, x M ≥ x k := by
-- proof
  intro k
  obtain ⟨i, hi⟩ := Finite.exists_max x
  have hs := Classical.epsilon_spec (p := fun j => j ∈ (Set.univ : Set (Fin n)) ∧ ∀ y ∈ (Set.univ : Set (Fin n)), x y ≤ x j)
    ⟨i, Set.mem_univ i, fun y _ => hi y⟩
  subst h
  exact hs.2 k (Set.mem_univ k)


-- created on 2023-11-05
