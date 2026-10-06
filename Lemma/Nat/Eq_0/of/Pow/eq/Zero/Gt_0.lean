import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
  {n : ℕ}
  -- given
  (hpos : 0 < n)
  (h : x ^ n = 0)
  -- imply
  : x = 0 := by
  -- proof
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    have h2 : x ^ (n + 1) = x ^ n * x := pow_succ x n
    rw [h2] at h
    have : x ^ n = 0 ∨ x = 0 := mul_eq_zero.mp h
    rcases this with (hpn | hxz)
    · by_cases hn : n = 0
      · subst hn
        simp at hpn
      · exact ih (by omega) hpn
    · exact hxz

-- created on 2018-11-03
-- updated on 2023-05-21
