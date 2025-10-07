import Lemma.Bool.Cond.of.Cond.All_Imp
open Bool


@[main]
private lemma main
  {f g : ℕ → Prop}
-- given
  (n : ℕ)
  (h₀ : f 0 = g 0)
  (h₁ : ∀ n, f n = g n → f (n + 1) = g (n + 1)) :
-- imply
  f n = g n := by
-- proof
  apply Cond.of.Cond.All_Imp n h₀ h₁


-- created on 2025-07-20
