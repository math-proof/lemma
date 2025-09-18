import Lemma.Algebra.ProdPermute__Neg.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1
import Lemma.Algebra.Add_ToNatNeg.eq.ToNatSub.of.Le_0
import Lemma.Algebra.EqMax.of.Ge
import Lemma.Algebra.GeNeg_0.of.Le_0
open Algebra


@[main]
private lemma main
  [Monoid α]
  {s : List α}
  {d : Fin s.length}
  {k : ℤ}
-- given
  (h_k : k ≤ 0)
  (h : d.val ≠ s.length - 1) :
-- imply
  (s.permute d k).prod = ((s.take (d + 1)).take ((s.take (d + 1)).length - (1 - k).toNat) ++ ((s.take (d + 1)).drop ((s.take (d + 1)).length - (1 - k).toNat)).rotate ((1 - k).toNat ⊓ (s.take (d + 1)).length - 1)).prod * (s.drop (d + 1)).prod := by
-- proof
  have := ProdPermute__Neg.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1 h (-k).toNat
  rw [Add_ToNatNeg.eq.ToNatSub.of.Le_0 h_k] at this
  simp [EqMax.of.Ge (GeNeg_0.of.Le_0 h_k)] at this
  simp [← this]


-- created on 2025-07-14
