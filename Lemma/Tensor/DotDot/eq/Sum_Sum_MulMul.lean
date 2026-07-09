import Lemma.Fin.MulSum.eq.Sum_Mul
import Lemma.Fin.Sum.of.All_Eq
import Lemma.Finset.Sum_Sum
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
open Fin Finset Tensor


@[main]
private lemma main
  [NonUnitalSemiring α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o])
  (i : Fin l)
  (j : Fin o) :
-- imply
  (((L @ M) @ N).get i).get j = ∑ (k : Fin m), ∑ (ι : Fin n), (L.get i).get k * (M.get k).get ι * (N.get ι).get j := by
-- proof
  rw [Sum_Sum.comm]
  rw [GetDot.eq.Sum_MulGetS.fin]
  simp_rw [GetDot.eq.Sum_MulGetS.fin]
  apply @Fin.Sum.of.All_Eq
  intro k
  erw [@Fin.MulSum.eq.Sum_Mul]
  rfl


-- created on 2026-07-09
