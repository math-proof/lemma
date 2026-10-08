import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : x₀ = ArgMax Set.univ fun x => f x)
  (hmax : ∃ x ∈ Set.univ, ∀ y ∈ Set.univ, f y ≤ f x) :
-- imply
  f x₀ = Maxima Set.univ fun x => f x := by
-- proof
  subst h
  have hs := Classical.epsilon_spec hmax
  have hg : IsGreatest ((fun x => f x) '' Set.univ) (f (ArgMax Set.univ fun x => f x)) :=
    ⟨⟨_, hs.1, rfl⟩, by rintro _ ⟨y, _, rfl⟩; exact hs.2 y (Set.mem_univ y)⟩
  unfold Maxima
  exact hg.csSup_eq.symm


-- created on 2026-10-08
