import sympy.Basic


@[main]
private lemma main
  [Nonempty α]
  {r : Prop}
-- given
  (h : ∀ _ : α, r) :
-- imply
  r := by
-- proof
  obtain ⟨x⟩ := ‹Nonempty α›
  exact h x


@[main]
private lemma domain_defined
  {D : Set α}
  {p : α → Prop}
  {x : α}
-- given
  (h₀ : ∀ x ∈ D, p x)
  (h₁ : x ∈ D) :
-- imply
  p x :=
-- proof
  h₀ x h₁


@[main]
private lemma subst
  {n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∀ x < n + 1, p x) :
-- imply
  p n :=
-- proof
  h n (Nat.lt_succ_self n)


-- created on 2019-03-15
-- updated on 2026-09-27
