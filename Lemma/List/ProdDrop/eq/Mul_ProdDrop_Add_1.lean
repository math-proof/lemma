import Lemma.List.Drop.eq.Cons_Drop_Add_1
import Lemma.Algebra.ProdCons.eq.Mul_Prod
open Algebra List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {v : List α}
-- given
  (i : Fin v.length) :
-- imply
  (v.drop i).prod = v[i] * (v.drop (i + 1)).prod := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1]
  rw [ProdCons.eq.Mul_Prod]


@[main, comm]
private lemma val
  [Mul α] [One α]
  {v : List α}
-- given
  (i : Fin v.length) :
-- imply
  (v.drop i).prod = v[i.val] * (v.drop (i + 1)).prod :=
-- proof
  main i

-- created on 2025-06-08
