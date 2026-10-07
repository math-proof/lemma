import sympy.concrete.expr_with_limits
import sympy.Basic


@[main]
private lemma main
  [Nonempty α]
  [LinearOrder β]
  {S : Set α}
  {f : α → β}
  {x₀ : α}
-- given
  (hx : x₀ ∈ S)
  (h : ∀ y ∈ S, y ≠ x₀ → f y < f x₀) :
-- imply
  ArgMax S f = x₀ := by
-- proof
  have spec := Classical.epsilon_spec (p := fun x => x ∈ S ∧ ∀ y ∈ S, f y ≤ f x)
    ⟨x₀, hx, fun y hy => by
      if e : y = x₀ then
        rw [e]
      else
        exact (h y hy e).le⟩
  by_contra hne
  exact absurd (spec.2 x₀ hx) (not_le.mpr (h _ spec.1 hne))


-- created on 2026-10-07
