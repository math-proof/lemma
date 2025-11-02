import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.LtVal
open Nat


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h₀ : s = m * n)
  (h₁ : j < n)
  (i : Fin m) :
-- imply
  i * n + j < s := by
-- proof
  subst h₀
  apply AddMul.lt.Mul.of.Lt.Lt _ h₁
  apply LtVal i


-- created on 2025-11-02
