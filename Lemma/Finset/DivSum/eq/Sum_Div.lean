import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Algebra Finset


@[main, comm]
private lemma main
  [DecidableEq ι]
  [DivisionSemiring Q]
-- given
  (s : Finset ι)
  (a : ι → Q)
  (x : Q) :
-- imply
  (∑ i ∈ s, a i) / x = ∑ i ∈ s, a i / x := by
-- proof
  apply UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 (f := fun i => i / x)
  ·
    simp
  ·
    simp [AddDivS.eq.DivAdd]


-- created on 2025-09-22
