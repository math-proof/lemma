import Lemma.Bool.Cond.of.All_Imp.Cond
open Bool


@[main]
private lemma main
  {f : ℕ → Prop}
-- given
  (h₁ : ∀ n, f n → f (n + 1))
  (n : ℕ) :
-- imply
  f 0 → f n := by
-- proof
  intro h₀
  apply Cond.of.All_Imp.Cond h₀ h₁


-- created on 2018-04-18
-- updated on 2026-08-28
