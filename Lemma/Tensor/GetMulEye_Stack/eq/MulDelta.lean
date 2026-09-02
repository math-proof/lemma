import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Mul
import sympy.matrices.expressions.special
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetMulEye_Stack.eq.MulDelta |
| comm | Tensor.MulDelta.eq.GetMulEye_Stack |
-/
@[main, comm]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (a : Tensor α [d])
  (i j : Fin d) :
-- imply
  (Tensor.eye d * [_ < d] a)[i, j] = KroneckerDelta i j * id (α := Tensor α []) a[j] := by
-- proof
  have hrow := GetMul.eq.MulGetS (Tensor.eye (α := α) d) ([_ < d] a) i
  have hcell := GetMul.eq.MulGetS ((Tensor.eye (α := α) d)[i]) (([_ < d] a)[i]) j
  have hd := GetEye.eq.Delta (α := α) i j
  have hA := EqGetStack (fun _ : Fin d => a) i
  have h1 : ((Tensor.eye (α := α) d) * [_ < d] a)[i][j] = ((Tensor.eye (α := α) d)[i] * ([_ < d] a)[i])[j] := congrArg (fun X : Tensor α [d] => X[j]) hrow
  simp only [id] at h1 hcell hd hA ⊢
  refine Eq.trans ?_ (Mul (↑(KroneckerDelta i j) : Tensor α []) (id (α := Tensor α []) a[j])).symm
  refine h1.trans (hcell.trans ?_)
  refine congrArg₂ HMul.hMul hd ?_
  exact congrArg (fun t : Tensor α [d] => t[j]) hA


-- created on 2026-09-02
