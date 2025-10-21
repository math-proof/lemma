import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
open Nat


@[main]
private lemma main
  {m n l : ℕ}
-- given
  (h₀ : i < m)
  (h₁ : j < n)
  (h₂ : k < l) :
-- imply
  (i * n + j) * l + k < m * n * l :=
-- proof
  AddMul.lt.Mul.of.Lt.Lt (AddMul.lt.Mul.of.Lt.Lt h₀ h₁) h₂


-- created on 2025-10-20
-- updated on 2025-10-21
