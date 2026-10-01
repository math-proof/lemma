import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  Maxima Set.univ x = x (ArgMax Set.univ x) := by
-- proof
  obtain ⟨i, hi⟩ := Finite.exists_max x
  have hs := Classical.epsilon_spec (p := fun j => j ∈ (Set.univ : Set (Fin n)) ∧ ∀ y ∈ (Set.univ : Set (Fin n)), x y ≤ x j)
    ⟨i, Set.mem_univ i, fun y _ => hi y⟩
  show sSup (x '' Set.univ) = x (ArgMax Set.univ x)
  exact IsGreatest.csSup_eq ⟨⟨_, Set.mem_univ _, rfl⟩, by rintro _ ⟨y, _, rfl⟩; exact hs.2 y (Set.mem_univ y)⟩


-- created on 2023-11-12
