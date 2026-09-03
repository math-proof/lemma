import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Mul
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Fin Tensor


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A B : Tensor α [n]) :
-- imply
  A @ B = ∑ k : Fin n, id (α := Tensor α []) A[k] * id (α := Tensor α []) B[k] := by
-- proof
  apply (Dot.eq.SumMul__0 A B).trans
  apply (Sum_0.eq.Sum_Get (A * B)).trans
  apply Sum.of.All_Eq
  intro k
  apply (GetMul.eq.MulGetS A B k).trans
  exact (Tensor.Mul (A[k] : Tensor α []) (B[k] : Tensor α [])).symm


-- created on 2019-11-09
