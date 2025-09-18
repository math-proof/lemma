import Lemma.Logic.Cond.of.Cond.All_Imp
open Logic


@[main]
private lemma main
  [Zero α]
  {f : ℕ → α}
-- given
  (n : ℕ)
  (h₀ : f 0 ≠ 0)
  (h₁ : ∀ n, f n ≠ 0 → f (n + 1) ≠ 0) :
-- imply
  f n ≠ 0 := by
-- proof
  apply Cond.of.Cond.All_Imp n h₀ h₁


-- created on 2025-07-20
