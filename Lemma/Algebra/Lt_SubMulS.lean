import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.Lt_Sub.of.LtAdd
open Nat


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  j < m * n - i * n := by
-- proof
  have h := AddMul.lt.Mul i j
  apply Lt_Sub.of.LtAdd.left h


-- created on 2025-05-09
