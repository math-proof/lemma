import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {i l d b : ℕ}
-- given
  (hd : 0 < d)
  (hdl : (d : ℤ) ∣ (l : ℤ) - 1)
  (hb : (b : ℤ) = max ((i : ℤ) - l + 1) (((i : ℤ) - l + 1) % d)) :
-- imply
  (i : ℤ) < b + l ∧ ((b : ℤ) - i) % d = 0 ∧ ∀ j : ℕ, (i : ℤ) < j + l → ((j : ℤ) - i) % d = 0 → b ≤ j := by
-- proof
  set x : ℤ := (i : ℤ) - l + 1 with hx
  have hxi : (d : ℤ) ∣ x - i := by
    rw [show x - i = -((l : ℤ) - 1) by rw [hx]; ring]
    exact dvd_neg.mpr hdl
  have hxd : (x % d - i) % d = 0 := by
    rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
    exact Int.emod_eq_zero_of_dvd hxi
  refine ⟨by have := le_max_left x (x % d); omega, ?_, ?_⟩
  ·
    obtain h | h := le_total (x % d) x
    ·
      rw [hb, max_eq_left h]
      exact Int.emod_eq_zero_of_dvd hxi
    ·
      rw [hb, max_eq_right h]
      exact hxd
  ·
    intro j hj hji
    have hjx : (j : ℤ) % d = x % d := by
      have e1 := Int.dvd_of_emod_eq_zero hji
      have e2 : (d : ℤ) ∣ (j : ℤ) - x := by
        have := dvd_sub e1 hxi
        rwa [show (j : ℤ) - i - (x - i) = j - x by ring] at this
      exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd e2)
    have hjd : (j : ℤ) % d ≤ j := by
      have e := Int.emod_def (j : ℤ) d
      have : 0 ≤ (d : ℤ) * ((j : ℤ) / d) := mul_nonneg (by positivity) (Int.ediv_nonneg (by positivity) (by positivity))
      linarith
    have : (b : ℤ) ≤ j := by
      rw [hb]
      exact max_le (by omega) (hjx ▸ hjd)
    exact_mod_cast this


-- created on 2026-10-07
