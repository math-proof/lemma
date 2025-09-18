import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.Add
import Lemma.Algebra.EqSub_Sub.of.Ge
import Lemma.Algebra.LeAdd_1
open Algebra


@[main]
private lemma main
  {i : Fin n}
-- given
  (h : j = n - 1 - i) :
-- imply
  n - j = i + 1 := by
-- proof
  simp_all
  rw [SubSub.eq.Sub_Add.nat]
  rw [Add.comm]
  rw [EqSub_Sub.of.Ge]
  apply LeAdd_1


-- created on 2025-06-18
