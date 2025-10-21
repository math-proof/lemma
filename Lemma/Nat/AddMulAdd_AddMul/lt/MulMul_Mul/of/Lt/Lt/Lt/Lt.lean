import Lemma.Nat.AddMulAddMul.lt.MulMul.of.Lt.Lt.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
open Nat


@[main]
private lemma main
  {m n d l : ℕ}
-- given
  (h₀ : i < m)
  (h₁ : j < n)
  (h₂ : t < d)
  (h₃ : k < l) :
-- imply
  (i * (n * d) + (j * d + t)) * l + k < m * (n * d) * l :=
-- proof
  AddMulAddMul.lt.MulMul.of.Lt.Lt.Lt h₀ (AddMul.lt.Mul.of.Lt.Lt h₁ h₂) h₃


-- created on 2025-10-21
