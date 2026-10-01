import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h : sSup (f '' S) ≥ M₀) :
-- imply
  ∀ M < M₀, ∃ x ∈ S, f x > M := by
-- proof
  intro M hM
  by_contra hc
  have hle : ∀ x ∈ S, f x ≤ M := fun x hx => not_lt.mp (fun hlt => hc ⟨x, hx, hlt⟩)
  have := csSup_le (h₀.image f) (Set.forall_mem_image.mpr fun x hx => hle x hx)
  linarith


-- created on 2019-04-10
