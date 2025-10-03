import Lemma.List.ProdPermute.eq.MulProd_ProdAppend
import Lemma.Algebra.AddToNat.eq.ToNatAdd.of.Gt_0
import Lemma.Algebra.EqMax.of.Gt
open Algebra List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
  {k : ℤ}
-- given
  (h_k : k > 0)
  (d : Fin s.length) :
-- imply
  (s.permute d k).prod = (s.take d).prod * (((s.drop d).take (k + 1).toNat).rotate 1 ++ (s.drop d).drop (k + 1).toNat).prod := by
-- proof
  have := ProdPermute.eq.MulProd_ProdAppend d k.toNat
  rw [AddToNat.eq.ToNatAdd.of.Gt_0 (by linarith)] at this
  simp [EqMax.of.Gt h_k] at this
  simp [← this]


-- created on 2025-07-14
