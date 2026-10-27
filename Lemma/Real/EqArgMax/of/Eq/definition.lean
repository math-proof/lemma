import Macro.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : x₀ = max⁻¹[x] f x)
  (hmax : ∃ x ∈ Set.univ, ∀ y ∈ Set.univ, f y ≤ f x) :
-- imply
  f x₀ = Maxima Set.univ fun x => f x := by
-- proof
  subst h
  have hs := Classical.epsilon_spec hmax
  have hg : IsGreatest ((fun x => f x) '' Set.univ) (f (max⁻¹[x] f x)) :=
    ⟨⟨_, hs.1, rfl⟩, by rintro _ ⟨y, _, rfl⟩; exact hs.2 y (Set.mem_univ y)⟩
  unfold Maxima
  exact hg.csSup_eq.symm


-- created on 2019-04-12
