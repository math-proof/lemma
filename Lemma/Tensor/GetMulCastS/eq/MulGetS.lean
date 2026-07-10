import Lemma.List.EqSwap_0'1
import Lemma.Tensor.GetCastRepeatUnsqueeze.eq.GetGet
import Lemma.Tensor.GetCastRepeatUnsqueezeCast.eq.GetGet
import Lemma.Tensor.GetMul.eq.MulGetS
open List Tensor
set_option maxHeartbeats 10000000


@[main, fin]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n)
  (k : Fin l) :
-- imply
  (((cast (congrArg (Tensor α) (show ([] ++ [m, 1, l]).set 1 (n * ([] ++ [m, 1, l])[1]) = [] ++ [m, n, l] by grind)) ((A.unsqueeze 1).repeat (1 : Fin 3) n) * cast (congrArg (Tensor α) (show ([] ++ [1, n, l]).set 0 (m * ([] ++ [1, n, l])[0]) = [] ++ [m, n, l] by grind)) (((cast (congrArg (Tensor α) (show ([] ++ [l, n]).swap (([] ++ [l, n]).length - 2) (([] ++ [l, n]).length - 1) = [] ++ [n, l] by simp [EqSwap_0'1])) Bᵀ).unsqueeze 0).repeat (0 : Fin 3) m)).get i).get j).get k =
    (A.get i).get k * (B.get k).get j := by
-- proof
  erw [GetMul.eq.MulGetS.fin _ _ i]
  erw [GetMul.eq.MulGetS.fin _ _ j]
  erw [GetMul.eq.MulGetS.fin _ _ k]
  congr 1
  ·
    apply GetCastRepeatUnsqueeze.eq.GetGet
  ·
    apply GetCastRepeatUnsqueezeCast.eq.GetGet


-- created on 2026-07-09
