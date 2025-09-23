import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Algebra


@[main, comm]
private lemma main
  [DecidableEq ι]
  [DivisionSemiring α]
-- given
  (s : Finset ι)
  (a : ι → α)
  (x : α) :
-- imply
  (∑ i ∈ s, a i) / x = ∑ i ∈ s, a i / x := by
-- proof
  apply UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 (f := fun i => i / x)
  ·
    simp
  ·
    simp [AddDivS.eq.DivAdd]


-- created on 2025-09-22
