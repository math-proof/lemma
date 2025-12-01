import Lemma.Finset.MulSum.eq.Sum_Mul
open Finset


@[main, comm]
private lemma main
  [NonUnitalNonAssocSemiring N]
-- given
  (a : Fin n → N) :
-- imply
  (∑ i : Fin n, a i) * x = ∑ i : Fin n, a i * x := by
-- proof
  apply MulSum.eq.Sum_Mul


-- created on 2025-12-01
