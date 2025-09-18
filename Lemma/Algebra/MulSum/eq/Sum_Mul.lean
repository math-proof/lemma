import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Algebra


@[main, comm]
private lemma main
  [DecidableEq ι]
  [NonUnitalNonAssocSemiring α]
-- given
  (s : Finset ι)
  (a : ι → α)
  (x : α) :
-- imply
  (∑ i ∈ s, a i) * x = ∑ i ∈ s, a i * x := by
-- proof
  apply UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 (f := fun i => i * x)
  .
    simp
  .
    simp [AddMulS.eq.MulAdd]


-- created on 2025-04-06
-- updated on 2025-07-13
