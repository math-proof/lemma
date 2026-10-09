import Lemma.Nat.Le_SubMulS.of.Lt
open Nat


@[path]
private lemma left
  {m n : ℕ}
  {i : Fin n} :
-- imply
  m ≤ m * n - m * i := by
-- proof
  have hi := i.isLt
  apply Le_SubMulS.of.Lt.left hi


@[path]
private lemma main
  {m n : ℕ}
  {i : Fin n} :
-- imply
  m ≤ n * m - i * m := by
-- proof
  have hi := i.isLt
  apply Le_SubMulS.of.Lt hi


-- created on 2025-05-06
-- updated on 2025-05-31
