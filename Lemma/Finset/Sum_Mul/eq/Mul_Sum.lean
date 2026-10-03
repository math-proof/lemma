import sympy.Basic
open Finset


@[main]
private lemma main
  [DecidableEq ι]
  [NonUnitalNonAssocSemiring N]
-- given
  (s : Finset ι)
  (x : ι → N)
  (a : N) :
-- imply
  ∑ i ∈ s, x i * a = (∑ i ∈ s, x i) * a :=
-- proof
  (sum_mul s x a).symm


-- created on 2026-10-03
