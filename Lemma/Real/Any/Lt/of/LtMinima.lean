import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : Minima S f < M) :
-- imply
  ∃ x ∈ S, f x < M := by
-- proof
  by_contra hc
  have hge : ∀ x ∈ S, M ≤ f x := fun x hx => not_lt.mp (fun hlt => hc ⟨x, hx, hlt⟩)
  have : M ≤ Minima S f := le_csInf (h₀.image f) (Set.forall_mem_image.mpr fun x hx => hge x hx)
  linarith


-- created on 2019-01-02
