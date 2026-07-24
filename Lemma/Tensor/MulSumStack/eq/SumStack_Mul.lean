import Lemma.Nat.EqMul0_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Tensor.UFnSumStack.eq.SumStack_UFn.All_EqUFnAdd.EqUFn_0
open Nat Tensor
set_option maxHeartbeats 500000


@[main, comm]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Fin n → Tensor α s)
  (A : Tensor α s) :
-- imply
  let S : Tensor α s := ∑ i < n, X i
  S * A = ∑ i < n, X i * A := by
-- proof
  simp
  apply UFnSumStack.eq.SumStack_UFn.All_EqUFnAdd.EqUFn_0.fin (f := fun X => X * A)
  ·
    apply EqMul0_0
  ·
    simp [AddMulS.eq.MulAdd]


-- created on 2026-07-22
