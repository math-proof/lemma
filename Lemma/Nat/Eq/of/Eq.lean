import sympy.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a = b) :
-- imply
  b = a :=
-- proof
  h.symm


@[main]
private lemma geometric_progression
  {f : ℕ → ℂ}
  {r : ℂ}
-- given
  (h : ∀ n, f (n + 1) = r * f n)
  (n : ℕ) :
-- imply
  f n = f 0 * r ^ n := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [h, ih, pow_succ]
    ring


-- created on 2018-05-25
-- updated on 2026-09-27
