import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Algebra Finset


@[main, comm]
private lemma main
  [DecidableEq ι]
  [NonUnitalNonAssocSemiring N]
-- given
  (s : Finset ι)
  (a : ι → N)
  (x : N) :
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
