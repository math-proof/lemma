import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [CommMagma α] [Zero α] [Preorder α] [PosMulMono α] [PosMulStrictMono α]
  {x a b d : α}
-- given
  (hd : d > 0)
  (h : x ∈ Ico a b) :
-- imply
  d * x ∈ Ico (a * d) (b * d) := by
-- proof
  constructor
  ·
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h.1 hd.le
  ·
    simpa [mul_comm] using mul_lt_mul_of_pos_left h.2 hd


-- created on 2018-11-21
-- updated on 2026-08-21
