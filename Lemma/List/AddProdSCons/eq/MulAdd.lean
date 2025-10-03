import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra List


@[main]
private lemma main
  [Add M]
  [Mul M]
  [One M]
  [RightDistribClass M]
-- given
  (a b : M)
  (l : List M) :
-- imply
  (a :: l).prod + (b :: l).prod = (a + b) * l.prod := by
-- proof
  rw [ProdCons.eq.Mul_Prod]
  rw [ProdCons.eq.Mul_Prod]
  rw [AddMulS.eq.MulAdd]


-- created on 2025-05-31
