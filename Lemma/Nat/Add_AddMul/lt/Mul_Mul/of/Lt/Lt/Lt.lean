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
  i * (n * l) + (j * l + k) < m * (n * l) := 
-- proof
  AddMul.lt.Mul.of.Lt.Lt h₀ (AddMul.lt.Mul.of.Lt.Lt h₁ h₂)


-- created on 2025-10-22
