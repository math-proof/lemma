import Lemma.Rat.In_Icc.of.Gt_0
import sympy.sets.sets
open Rat


@[main]
private lemma main
  [NeZero n]
  {l u d : ℕ}
-- given
  (hi : i ∈ Icc n (n - 1 + l))
  (h_tail : (d : ℤ) ∣ (n - 1 : ℤ) - i + l) :
-- imply
  ⌈((↑(i - l) : ℤ) - (i - l)) / (d : ℚ)⌉ ≤ ⌊((↑((n - 1) ⊓ (i + u)) : ℤ) - (i - l)) / (d : ℚ)⌋ := by
-- proof
  if h_d : d = 0 then
    subst h_d
    simp
  else
    have hn : 0 < n := NeZero.pos n
    have hd : d > 0 := Nat.pos_of_ne_zero h_d
    obtain ⟨t, ht⟩ := h_tail
    have ht_Icc := (Rat.In_Icc.of.Gt_0 (d := d) hd n l u i t).mp (by grind)
    simpa using ht_Icc.1.trans (Int.cast_le.mpr ht_Icc.2)


-- created on 2026-07-28
