import Lemma.Nat.AddMulAddMul.lt.MulMul.of.Lt.Lt.Lt
open Nat


@[main]
private lemma main
  {m n l d : ℕ}
-- given
  (h₀ : i < m)
  (h₁ : j < n)
  (h₂ : k < l)
  (h₃ : t < d) :
-- imply
  ((i * n + j) * l + k) * d + t < m * n * l * d :=
-- proof
  AddMul.lt.Mul.of.Lt.Lt (AddMulAddMul.lt.MulMul.of.Lt.Lt.Lt h₀ h₁ h₂) h₃


-- created on 2025-10-21
