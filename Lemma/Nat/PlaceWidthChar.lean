import Def.ModularCurve_PlaceWidth
import Def.ModularCurve_PlaceWidthChar

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve


theorem jWidthChar_of_ne {K : Type*} [Field K] [DecidableEq K] {q : ℕ}
    (h2 : q ≠ 2) (h3 : q ≠ 3) (j : K) : jWidthChar q j = jWidth j := by
  unfold jWidthChar
  rw [if_neg h2, if_neg h3]

theorem jWidthChar_of_five_le {K : Type*} [Field K] [DecidableEq K] {q : ℕ} (hq : 5 ≤ q) (j : K) :
    jWidthChar q j = jWidth j :=
  jWidthChar_of_ne (by omega) (by omega) j

theorem jWidthChar_zero_char {K : Type*} [Field K] [DecidableEq K] (j : K) :
    jWidthChar 0 j = jWidth j :=
  jWidthChar_of_ne (by decide) (by decide) j

theorem jWidthChar_two_of_eq_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j = 0) :
    jWidthChar 2 j = 12 := by
  unfold jWidthChar
  rw [if_pos rfl, if_pos h]

theorem jWidthChar_three_of_eq_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j = 0) :
    jWidthChar 3 j = 6 := by
  unfold jWidthChar
  rw [if_neg (by decide), if_pos rfl, if_pos h]

theorem jWidthChar_two_of_ne_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j ≠ 0) :
    jWidthChar 2 j = 1 := by
  unfold jWidthChar
  rw [if_pos rfl, if_neg h]

theorem jWidthChar_three_of_ne_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j ≠ 0) :
    jWidthChar 3 j = 1 := by
  unfold jWidthChar
  rw [if_neg (by decide), if_pos rfl, if_neg h]

theorem jWidthChar_eq_or {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) :
    jWidthChar q j = jWidth j ∨ jWidthChar q j = 1 ∨ jWidthChar q j = 6 ∨ jWidthChar q j = 12 := by
  unfold jWidthChar
  split_ifs <;> simp

theorem jWidthChar_pos {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) : 0 < jWidthChar q j := by
  rcases jWidthChar_eq_or q j with h | h | h | h <;> rw [h]
  · exact jWidth_pos j
  · exact (by decide : (0 : ℕ) < 1)
  · exact (by decide : (0 : ℕ) < 6)
  · exact (by decide : (0 : ℕ) < 12)

theorem jWidthChar_dvd_twelve {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) :
    jWidthChar q j ∣ 12 := by
  rcases jWidthChar_eq_or q j with h | h | h | h
  · rw [h]
    exact (jWidth_dvd_six j).trans (by decide)
  · rw [h]
    exact (by decide : (1 : ℕ) ∣ 12)
  · rw [h]
    exact (by decide : (6 : ℕ) ∣ 12)
  · rw [h]

theorem jWidthChar_map {K L : Type*} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
    (f : K →+* L) (q : ℕ) (j : K) : jWidthChar q (f j) = jWidthChar q j := by
  unfold jWidthChar
  rw [jWidth_map f j]
  by_cases hj0 : j = 0
  · subst hj0
    simp
  · have hne : f j ≠ 0 := (map_ne_zero_iff f f.injective).mpr hj0
    simp only [if_neg hj0, if_neg hne]

theorem placeWidthChar_of_ne {K : Type*} [Field K] [DecidableEq K] {q : ℕ}
    (h2 : q ≠ 2) (h3 : q ≠ 3) (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N w = placeWidth N w := by
  unfold placeWidthChar placeWidth
  rw [jWidthChar_of_ne h2 h3]

theorem placeWidthChar_of_five_le {K : Type*} [Field K] [DecidableEq K] {q : ℕ} (hq : 5 ≤ q)
    (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N w = placeWidth N w :=
  placeWidthChar_of_ne (by omega) (by omega) N w

theorem placeWidthChar_eq_div {K : Type*} [Field K] [DecidableEq K] (q N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N w = jWidthChar q (w.evalAt (jGeomGen K N)) / placeRamificationJ N w :=
  rfl

theorem placeWidthChar_of_placeRamificationJ_eq_zero {K : Type*} [Field K] [DecidableEq K] (q N : ℕ)
    [NeZero N] {w : Place K (modularFunctionFieldC K N)} (h : placeRamificationJ N w = 0) :
    placeWidthChar q N w = 0 := by
  unfold placeWidthChar
  rw [h, Nat.div_zero]

example : jWidthChar 2 (0 : ZMod 2) = 12 := jWidthChar_two_of_eq_zero rfl
example : jWidthChar 3 (0 : ZMod 3) = 6 := jWidthChar_three_of_eq_zero rfl
example : jWidthChar 3 (1 : ZMod 3) = 1 := jWidthChar_three_of_ne_zero one_ne_zero
example (j : ℚ) : jWidthChar 0 j = jWidth j := jWidthChar_zero_char j

end ModularCurve

end
