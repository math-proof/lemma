import Lemma.Bool.Cond.of.All_Imp.Cond
open Bool


@[main]
private lemma main
  [Zero α]
  {f : ℕ → α}
-- given
  (h₀ : f 0 ≠ 0)
  (h₁ : ∀ n, f n ≠ 0 → f (n + 1) ≠ 0)
  (n : ℕ) :
-- imply
  f n ≠ 0 := by
-- proof
  apply Cond.of.All_Imp.Cond h₀ h₁


-- created on 2018-04-16
