import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GetAdd.eq.AddGetS.of.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
import sympy.tensor.tensor
open Finset Tensor


@[main, fin]
private lemma main
  [AddCommMonoid α]
  [DecidableEq ι]
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (X : ι → Tensor α s)
  (k : Fin s[0])
  (S : Finset ι) :
-- imply
  (∑ i ∈ S, X i).get ⟨k, by apply GtLength.of.GtLength_0 h_s⟩ = ∑ i ∈ S, (X i).get ⟨k, by apply GtLength.of.GtLength_0 h_s⟩ := by
-- proof
  let f := fun X : Tensor α s => X.get ⟨k, by apply GtLength.of.GtLength_0 h_s⟩
  have h_f0 : f 0 = 0 := by
    apply EqGet0_0.fin
  have h_add : ∀ (a b : Tensor α s), f (a + b) = f a + f b := by
    intro a b
    simp [f]
    apply GetAdd.eq.AddGetS.of.GtLength_0 h_s
  have := UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 h_f0 h_add S X
  simp [f] at this
  assumption


-- created on 2025-11-06
