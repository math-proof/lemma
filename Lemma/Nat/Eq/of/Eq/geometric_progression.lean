import sympy.Basic


@[path]
private lemma main
  [CommRing α]
  {f : ℕ → α}
  {r : α}
-- given
  (h : ∀ n, f (n + 1) = r * f n) :
-- imply
  ∀ n, f n = f 0 * r ^ n := by
-- proof
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [h n, ih]
    ring


-- created on 2019-04-05
