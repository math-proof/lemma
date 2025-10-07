import Lemma.Algebra.Sum.eq.Sum_MulBool
import Lemma.Algebra.Sum_Add.eq.AddSumS
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Set.In.is.In_Inter.ou.In_SDiff
import Lemma.Bool.BoolOr.eq.SubAddBoolS
import Lemma.Bool.ToNatDecide.eq.Bool
import Lemma.Set.In_Inter.In_SDiff.is.False
open Algebra Set Bool


@[main]
private lemma main
  [DecidableEq ι]
  [Fintype ι]
  [NonAssocSemiring α]
-- given
  (f : ι → α)
  (A B : Finset ι) :
-- imply
  ∑ x ∈ A, f x = (∑ x ∈ A ∩ B, f x) + ∑ x ∈ A \ B, f x := by
-- proof
  rw [Sum.eq.Sum_MulBool]
  conv_rhs =>
    rw [Sum.eq.Sum_MulBool]
  conv =>
    arg 2
    arg 2
    rw [Sum.eq.Sum_MulBool]
  rw [AddSumS.eq.Sum_Add]
  simp only [AddMulS.eq.MulAdd]
  have h := In.is.In_Inter.ou.In_SDiff.fin A B
  conv_lhs =>
    simp only [h]
  simp only [BoolOr.eq.SubAddBoolS]
  simp only [Set.In_Inter.In_SDiff.is.False.fin]
  simp


-- created on 2025-10-01
