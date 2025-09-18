import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
-- given
  (a : α)
  (z : ℤ) :
-- imply
  ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1 :=
-- proof
  Int.floor_eq_iff


-- created on 2025-03-20
