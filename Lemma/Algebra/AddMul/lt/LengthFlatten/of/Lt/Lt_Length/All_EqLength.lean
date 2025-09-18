import Lemma.Algebra.LengthFlatten.eq.MulLength.of.All_EqLength
import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
open Algebra


@[main]
private lemma main
  {i j n : ℕ}
  {v : List (List α)}
-- given
  (h₀ : ∀ l ∈ v, l.length = n)
  (h₁ : i < v.length)
  (h₂ : j < n) :
-- imply
  i * n + j < v.flatten.length := by
-- proof
  rw [LengthFlatten.eq.MulLength.of.All_EqLength h₀]
  apply AddMul.lt.Mul.of.Lt.Lt <;>
    assumption


-- created on 2025-06-28
