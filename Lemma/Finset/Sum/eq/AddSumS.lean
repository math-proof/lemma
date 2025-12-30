import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Bool.BoolOr.eq.SubAddBoolS
import Lemma.Bool.ToNatDecide.eq.Bool
import Lemma.Finset.In_Inter.In_SDiff.is.False
import Lemma.Finset.In.is.In_Inter.ou.In_SDiff
import Lemma.Finset.Sum.eq.Sum_MulBool
import Lemma.Finset.Sum_Add.eq.AddSumS
open Bool Finset Nat


@[main]
private lemma main
  [Fintype ι] [DecidableEq ι]
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
  have h := In.is.In_Inter.ou.In_SDiff A B
  conv_lhs =>
    simp only [h]
  simp only [BoolOr.eq.SubAddBoolS]
  simp only [In_Inter.In_SDiff.is.False]
  simp


-- created on 2025-10-01
