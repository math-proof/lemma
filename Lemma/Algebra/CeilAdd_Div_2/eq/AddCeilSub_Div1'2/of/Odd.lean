import Lemma.Algebra.CeilAdd.eq.AddCeil
import Lemma.Algebra.AddSub.eq.Add_Sub
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.Algebra.Odd.is.Any_Eq_AddMul2
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Logic.EqUFnS.of.Eq
open Algebra Logic


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {n : ℤ}
-- given
  (h : n is odd) :
-- imply
  ⌈x + n / 2⌉ = ⌈x - 1 / 2⌉ + (n + 1) / 2 := by
-- proof
  rw [AddCeil.eq.CeilAdd]
  apply EqUFnS.of.Eq
  rw [AddSub.eq.Add_Sub]
  apply EqAddS.of.Eq.left
  let ⟨k, hk⟩ := Any_Eq_AddMul2.of.Odd h
  rw [hk]
  simp
  rw [DivAdd.eq.AddDivS]
  simp
  ring_nf
  simp
  rw [DivAdd.eq.AddDivS]
  norm_num
  rw [Add_Add.eq.AddAdd]
  apply EqAddS.of.Eq (k : α)
  norm_num


-- created on 2025-03-04
-- updated on 2025-08-13
