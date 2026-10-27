import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [Semiring α]
-- given
  (n : α) :
-- imply
  n is even ↔ 2 ∣ n :=
-- proof
  even_iff_two_dvd


-- created on 2025-08-12
