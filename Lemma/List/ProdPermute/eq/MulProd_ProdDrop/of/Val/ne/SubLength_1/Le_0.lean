import Lemma.List.ProdPermute__Neg.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1
import Lemma.Int.Add_ToNatNeg.eq.ToNatSub.of.Le_0
import Lemma.Nat.EqMax.of.Ge
import Lemma.Algebra.GeNeg_0.of.Le_0
open Algebra List Int Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
  {i : Fin s.length}
  {d : ℤ}
-- given
  (h_d : d ≤ 0)
  (h_i : i.val ≠ s.length - 1) :
-- imply
  (s.permute i d).prod = ((s.take (i + 1)).take ((s.take (i + 1)).length - (1 - d).toNat) ++ ((s.take (i + 1)).drop ((s.take (i + 1)).length - (1 - d).toNat)).rotate ((1 - d).toNat ⊓ (s.take (i + 1)).length - 1)).prod * (s.drop (i + 1)).prod := by
-- proof
  have := ProdPermute__Neg.eq.MulProd_ProdDrop.of.Val.ne.SubLength_1 h_i (-d).toNat
  rw [Add_ToNatNeg.eq.ToNatSub.of.Le_0 h_d] at this
  simp [EqMax.of.Ge (GeNeg_0.of.Le_0 h_d)] at this
  simp [← this]


-- created on 2025-07-14
