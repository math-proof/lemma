import Lemma.Finset.UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0
open Finset


@[main, comm]
private lemma main
  [AddCommMonoid N]
  [Div N]
-- given
  (h0 : ∀ x : N, 0 / x = 0)
  (hadd : ∀ a b x : N, (a + b) / x = a / x + b / x)
  (a : Fin n → N)
  (x : N) :
-- imply
  (∑ i : Fin n, a i) / x = ∑ i : Fin n, a i / x := by
-- proof
  apply UFnSum.eq.Sum_UFn.All_EqUFnAdd.EqUFn_0 (f := fun t => t / x)
  ·
    exact h0 x
  ·
    intro a b
    exact hadd a b x


-- created on 2026-08-15
