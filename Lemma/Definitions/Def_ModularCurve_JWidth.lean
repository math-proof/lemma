import Mathlib

set_option autoImplicit false

namespace ModularCurve

def jWidth {K : Type*} [Field K] [DecidableEq K] (j : K) : ℕ :=
  if j = 0 then 3 else if j = 1728 then 2 else 1

variable {K : Type*} [Field K] [DecidableEq K]

theorem jWidth_of_eq_zero {j : K} (h : j = 0) : jWidth j = 3 := by simp [jWidth, h]

theorem jWidth_of_eq_1728 {j : K} (h : j = 1728) (h0 : j ≠ 0) : jWidth j = 2 := by
  subst h; simp [jWidth, h0]

theorem jWidth_of_ne {j : K} (h0 : j ≠ 0) (h1728 : j ≠ 1728) : jWidth j = 1 := by
  simp [jWidth, h0, h1728]

theorem jWidth_eq_ite (j : K) :
    jWidth j = (if j = 0 then 3 else if j = 1728 then 2 else 1) := rfl

theorem jWidth_pos (j : K) : 0 < jWidth j := by
  unfold jWidth; split_ifs <;> decide

theorem jWidth_eq_one_or (j : K) : jWidth j = 1 ∨ jWidth j = 2 ∨ jWidth j = 3 := by
  unfold jWidth; split_ifs <;> simp

theorem jWidth_dvd_six (j : K) : jWidth j ∣ 6 := by
  unfold jWidth; split_ifs <;> decide

theorem jWidth_map {L : Type*} [Field L] [DecidableEq L] (f : K →+* L) (j : K) :
    jWidth (f j) = jWidth j := by
  have h1728 : f 1728 = (1728 : L) := map_ofNat f 1728
  unfold jWidth
  by_cases hj0 : j = 0
  · subst hj0; simp
  · have hne : f j ≠ 0 := (map_ne_zero_iff f f.injective).mpr hj0
    rw [if_neg hj0, if_neg hne]
    by_cases hj : j = 1728
    · have hfj : f j = 1728 := by rw [hj, h1728]
      rw [if_pos hj, if_pos hfj]
    · have hfj : f j ≠ 1728 := fun h => hj (f.injective (h.trans h1728.symm))
      rw [if_neg hj, if_neg hfj]

end ModularCurve
