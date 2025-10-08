import Lemma.Nat.AddMul.lt.Mul
import Lemma.Algebra.Lt_Sub.of.LtAdd
open Algebra Nat


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  j < m * n - i * n := by
-- proof
  have h := AddMul.lt.Mul i j
  apply Lt_Sub.of.LtAdd.left.nat h


-- created on 2025-05-09
