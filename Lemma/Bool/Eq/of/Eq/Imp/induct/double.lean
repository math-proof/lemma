import sympy.Basic


@[path]
private lemma main
  {α β : Type}
  {f g : ℕ → α → β}
  {x : α}
  {n : ℕ}
-- given
  (h₀ : ∀ z, f 0 z = g 0 z)
  (h₁ : ∀ n x y, f n x = g n x → f (n + 1) y = g (n + 1) y) :
-- imply
  f n x = g n x := by
-- proof
  induction n with
  | zero =>
    apply h₀
  | succ n ih =>
    apply h₁ n x x ih


-- created on 2019-04-17
-- updated on 2026-10-17
