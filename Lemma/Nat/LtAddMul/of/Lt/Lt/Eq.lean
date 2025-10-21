import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
open Nat


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h : s = m * n)
  (h₀ : i < m)
  (h₁ : j < n) :
-- imply
  i * n + j < s :=
-- proof
  h ▸ AddMul.lt.Mul.of.Lt.Lt h₀ h₁


-- created on 2025-10-21
