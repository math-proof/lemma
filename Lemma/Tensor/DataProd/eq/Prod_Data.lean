import sympy.tensor.tensor
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.EqData1'1
import Lemma.Finset.UFnProd.eq.Prod_UFn.All_EqUFnMul.EqUFn_1
open Tensor Finset


@[main, comm]
private lemma main
  [DecidableEq ι]
  [CommMonoid α]
-- given
  (S : Finset ι)
  (A : ι → Tensor α s) :
-- imply
  (∏ i ∈ S, A i).data = ∏ i ∈ S, (A i).data := by
-- proof
  apply UFnProd.eq.Prod_UFn.All_EqUFnMul.EqUFn_1 (f := Tensor.data) _ _ S A
  ·
    apply EqData1'1
  ·
    simp [DataMul.eq.MulDataS]


-- created on 2026-09-06
