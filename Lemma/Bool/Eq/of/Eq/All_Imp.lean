import Lemma.Bool.Cond.of.All_Imp.Cond
open Bool


@[path]
private lemma main
  {f g : ℕ → Prop}
-- given
  (h₀ : f 0 = g 0)
  (h₁ : ∀ n, f n = g n → f (n + 1) = g (n + 1))
  (n : ℕ) :
-- imply
  f n = g n := by
-- proof
  apply Cond.of.All_Imp.Cond h₀ h₁


-- created on 2018-04-17
