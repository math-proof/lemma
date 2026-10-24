import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma helper_main
  {R : Type*} [CommRing R] (e : ℕ) (a : ℕ → R)
  (h : ∀ k : ℕ, k + 1 < e → a k - 2 * a (k + 1) + a (k + 2) = 0) :
  ∀ n : ℕ, n + 1 ≤ e →
    a n = a 0 + (a 1 - a 0) * n ∧ a (n + 1) = a 0 + (a 1 - a 0) * (n + 1 : ℕ) := by
  intro n
  induction n
  ·
    intro _
    constructor
    · simp
    · simp
  ·
    rename_i n ih
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨h2, ?_⟩
    have h3 := h n (by omega)
    push_cast at h1 h2 ⊢
    linear_combination h3 - h1 + 2 * h2
/--
[eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero.lean)
-/
@[path]
private lemma main
  [CommRing R] (e : ℕ) (a : ℕ → R)
  (h : ∀ k : ℕ, k + 1 < e → a k - 2 * a (k + 1) + a (k + 2) = 0)
  (k : ℕ) (hk : k ≤ e) :
  -- imply
  a k = a 0 + (a 1 - a 0) * k := by
  -- proof
  cases k
  · simp
  ·
    rename_i n
    refine (helper_main e a h n hk).2


-- created on 2026-10-20
