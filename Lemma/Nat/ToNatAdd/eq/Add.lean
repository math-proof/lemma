import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (i d : ℕ) :
-- imply
  (i + (d : ℤ)).toNat = i + d := by
-- proof
  rw [← Nat.cast_add, Int.toNat_natCast]


-- created on 2025-10-20
-- updated on 2026-11-21
