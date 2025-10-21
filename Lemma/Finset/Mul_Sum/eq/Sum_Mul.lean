import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Finset Nat


@[main, comm]
private lemma main
  [DecidableEq ι]
  [NonUnitalNonAssocSemiring N]
-- given
  (s : Finset ι)
  (x : ι → N)
  (a : N) :
-- imply
  a * ∑ i ∈ s, x i = ∑ i ∈ s, a * x i := by
-- proof
  apply UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
  .
    simp
  .
    simp [AddMulS.eq.Mul_Add]


-- created on 2025-04-06
-- updated on 2025-07-13
