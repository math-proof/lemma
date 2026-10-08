import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : x₀ = ArgMin Set.univ fun x => f x)
  (hmin : ∃ x ∈ Set.univ, ∀ y ∈ Set.univ, f x ≤ f y) :
-- imply
  f x₀ = Minima Set.univ fun x => f x := by
-- proof
  subst h
  have hs := Classical.epsilon_spec hmin
  have hl : IsLeast ((fun x => f x) '' Set.univ) (f (ArgMin Set.univ fun x => f x)) :=
    ⟨⟨_, hs.1, rfl⟩, by rintro _ ⟨y, _, rfl⟩; exact hs.2 y (Set.mem_univ y)⟩
  unfold Minima
  exact hl.csInf_eq.symm


-- created on 2026-10-08
