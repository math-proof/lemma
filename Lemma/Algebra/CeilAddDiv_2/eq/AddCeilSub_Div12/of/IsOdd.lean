import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {n : ℤ}
-- given
  (hn : Odd n) :
-- imply
  ⌈x + (n : ℝ) / 2⌉ = ⌈x - 1 / 2⌉ + (n + 1) / 2 := by
-- proof
  obtain ⟨k, hk⟩ := hn
  have hn2 : (n : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
    rw [hk]
    simp [Int.cast_add, Int.cast_mul]
    ring
  have hn1 : (n + 1) / 2 = k + 1 := by
    rw [hk]
    omega
  rw [hn2, hn1]
  have hx : x + ((k : ℝ) + 1 / 2) = x - 1 / 2 + (k + 1 : ℤ) := by
    push_cast
    ring
  rw [hx, Int.ceil_add_intCast]


-- created on 2018-11-08
-- updated on 2026-08-20
