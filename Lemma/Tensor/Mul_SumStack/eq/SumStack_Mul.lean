import Lemma.Nat.EqMul_0'0
import Lemma.Tensor.UFnSumStack.eq.SumStack_UFn.All_EqUFnAdd.EqUFn_0
open Nat Tensor


@[main, comm]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Fin n → Tensor α s)
  (A : Tensor α s) :
-- imply
  let S : Tensor α s := ∑ i < n, X i
  A * S = ∑ i < n, A * X i := by
-- proof
  simp
  apply UFnSumStack.eq.SumStack_UFn.All_EqUFnAdd.EqUFn_0.fin (f := fun X => A * X)
  ·
    apply EqMul_0'0
  ·
    simp [AddMulS.eq.Mul_Add]


-- created on 2026-07-22
