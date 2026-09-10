import Lemma.Tensor.DotGetSwapMatrix.eq.Get
import Lemma.Tensor.EqTSwapMatrix
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j k : Fin n) :
-- imply
  (x @ (SwapMatrix (α := α) n i j))[k] = x[Equiv.swap i j k] := by
-- proof
  have hL := GetDot.eq.Sum_MulGetS.une x (SwapMatrix n i j) k
  have hR := GetDot.eq.Sum_MulGetS.mv (SwapMatrix n i j) x k
  have hLeft := DotGetSwapMatrix.eq.Get x i j k
  have hget := GetDot.eq.DotGet.une (SwapMatrix n i j) x k
  apply hL.trans
  apply Eq.trans _ (hget.trans hLeft)
  apply Eq.trans _ hR.symm
  apply Fin.Sum.of.All_Eq
  intro m
  apply Eq.trans
  · apply congrArg₂ (fun a b => a * b) (rfl : (x[m] : Tensor α []) = x[m])
    let S := SwapMatrix (α := α) n i j
    apply (EqGetT S m k).symm.trans
    exact congrArg (fun t : Tensor α [n, n] => t[k, m]) (EqTSwapMatrix (α := α) n i j)
  · have hW := GetSwapMatrix.eq.Ite (α := α) (i) (j) k m
    simp only [id]
    simp only [GetElem.getElem] at hW ⊢
    erw [hW]
    split_ifs <;> exact Tensor.Mul.nat _ _


-- created on 2026-09-10
