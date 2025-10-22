import Lemma.List.ProdPermute.eq.MulProd_ProdAppend
import Lemma.Int.AddToNat.eq.ToNatAdd.of.Gt_0
import Lemma.Nat.EqMax.of.Gt
open List Int Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
  {d : ℤ}
-- given
  (h : d > 0)
  (i : Fin s.length) :
-- imply
  (s.permute i d).prod = (s.take i).prod * (((s.drop i).take (d + 1).toNat).rotate 1 ++ (s.drop i).drop (d + 1).toNat).prod := by
-- proof
  have := ProdPermute.eq.MulProd_ProdAppend i d.toNat
  rw [AddToNat.eq.ToNatAdd.of.Gt_0 (by linarith)] at this
  simp [EqMax.of.Gt h] at this
  simp [← this]


-- created on 2025-07-14
