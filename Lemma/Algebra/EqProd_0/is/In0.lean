import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [MonoidWithZero M]
  [Nontrivial M]
  [NoZeroDivisors M]
-- given
  (l : List M) :
-- imply
  l.prod = 0 ↔ 0 ∈ l :=
-- proof
  List.prod_eq_zero_iff


-- created on 2025-08-02
