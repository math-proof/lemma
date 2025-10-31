import Lemma.List.Drop.eq.Cons_Drop_Add_1
import Lemma.List.ProdCons.eq.Mul_Prod
open List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.drop i).prod = s[i] * (s.drop (i + 1)).prod := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1]
  rw [ProdCons.eq.Mul_Prod]


@[main, comm]
private lemma val
  [Mul α] [One α]
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.drop i).prod = s[i.val] * (s.drop (i + 1)).prod :=
-- proof
  main i

-- created on 2025-06-08
