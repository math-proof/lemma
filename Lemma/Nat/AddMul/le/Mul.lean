import Lemma.Nat.AddMul.le.Mul.of.Lt
import Lemma.Nat.LtVal
open Nat


@[main]
private lemma main
  {n : ℕ}
  {i : Fin n} :
-- imply
  m * i + m ≤ m * n := by
-- proof
  have hi := LtVal i
  apply AddMul.le.Mul.of.Lt hi


-- created on 2025-05-06
-- updated on 2025-05-31
