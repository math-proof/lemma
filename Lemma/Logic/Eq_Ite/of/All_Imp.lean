import Lemma.Basic


@[main]
private lemma main
  {f g : ℕ → α}
-- given
  (h : ∀ n, f n = (if n = 0 then
    f 0
  else
    g n) → f (n + 1) = g (n + 1)) :
-- imply
  f n = if n = 0 then
    f 0
  else
    g n := by
-- proof
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    apply h n ih


-- created on 2025-08-04
