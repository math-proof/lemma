import sympy.tensor.tensor
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Tensor Finset


@[main, comm]
private lemma main
  [DecidableEq ι]
  [AddCommMonoid α]
-- given
  (S : Finset ι)
  (A : ι → Tensor α s) :
-- imply
  (∑ i ∈ S, A i).data = ∑ i ∈ S, (A i).data := by
-- proof
  apply UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 (f := Tensor.data) _ _ S A
  ·
    aesop
  ·
    simp [DataAdd.eq.AddDataS]


-- created on 2025-07-14
