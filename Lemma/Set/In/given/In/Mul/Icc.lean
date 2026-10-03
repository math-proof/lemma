import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [CommMagma α] [Zero α] [Preorder α] [PosMulMono α] [PosMulStrictMono α]
  {x a b d : α}
-- given
  (hd : d > 0)
  (h : x ∈ Icc a b) :
-- imply
  d * x ∈ Icc (a * d) (b * d) := by
-- proof
  constructor
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left h.1 hd.le
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left h.2 hd.le


-- created on 2026-10-03
