import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GetAdd.eq.AddGetS.of.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.UFnSumStack.eq.SumStack_UFn.All_EqUFnAdd.EqUFn_0
open Tensor Finset


@[main, fin]
private lemma main
  [Mul α] [AddMonoid α]
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (X : Fin n → Tensor α s)
  (k : Fin s[0]) :
-- imply
  (∑ i < n, X i).get ⟨k, by apply GtLength.of.GtLength_0 h_s⟩ = ∑ i < n, (X i).get ⟨k, by apply GtLength.of.GtLength_0 h_s⟩ := by
-- proof
  let f := fun X : Tensor α s => X.get ⟨k, by apply GtLength.of.GtLength_0 h_s⟩
  have h_f0 : f 0 = 0 := by
    apply EqGet0_0.fin
  have h_add : ∀ (a b : Tensor α s), f (a + b) = f a + f b := by
    intro a b
    simp [f]
    apply GetAdd.eq.AddGetS.of.GtLength_0 h_s
  have := UFnSumStack.eq.SumStack_UFn.All_EqUFnAdd.EqUFn_0.fin h_f0 h_add X
  simp [f] at this
  assumption


-- created on 2026-07-22
