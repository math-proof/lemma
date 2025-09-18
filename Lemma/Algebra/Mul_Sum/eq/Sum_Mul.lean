import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Algebra


@[main, comm]
private lemma main
  [DecidableEq ι]
  [NonUnitalNonAssocSemiring α]
-- given
  (s : Finset ι)
  (x : ι → α)
  (a : α) :
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
