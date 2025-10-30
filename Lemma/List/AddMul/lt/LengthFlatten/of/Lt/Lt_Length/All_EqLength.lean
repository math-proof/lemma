import Lemma.List.LengthFlatten.eq.MulLength.of.All_EqLength
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
open List Nat


@[main]
private lemma main
  {i j n : ℕ}
  {s : List (List α)}
-- given
  (h₀ : ∀ l ∈ s, l.length = n)
  (h₁ : i < s.length)
  (h₂ : j < n) :
-- imply
  i * n + j < s.flatten.length := by
-- proof
  rw [LengthFlatten.eq.MulLength.of.All_EqLength h₀]
  apply AddMul.lt.Mul.of.Lt.Lt <;>
    assumption


-- created on 2025-06-28
