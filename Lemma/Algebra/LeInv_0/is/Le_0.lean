import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [GroupWithZero α]
  [LinearOrder α]
  [ZeroLEOneClass α]
  [PosMulMono α]
  {a : α} :
-- imply
  a⁻¹ ≤ 0 ↔ a ≤ 0 :=
-- proof
  inv_nonpos


-- created on 2025-03-30
