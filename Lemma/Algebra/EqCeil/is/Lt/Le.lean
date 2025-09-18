import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
-- given
  (a : α)
  (z : ℤ) :
-- imply
  ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ ↑z :=
-- proof
  Int.ceil_eq_iff


-- created on 2025-03-20
