import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {M : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : Maxima S f > M) :
-- imply
  ∃ x ∈ S, f x > M := by
-- proof
  by_contra hc
  refine absurd h (not_lt.mpr (csSup_le (h₀.image f) ?_))
  rintro _ ⟨x, hx, rfl⟩
  exact not_lt.mp (fun hx' => hc ⟨x, hx, hx'⟩)


-- created on 2018-12-31
