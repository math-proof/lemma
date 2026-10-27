import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Complex_normSq_conj_add_conj_mul_eq_and_complete_square](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_normSq_conj_add_conj_mul_eq_and_complete_square.lean)
-/
@[path]
private lemma main
  (r z : ℂ) :
  -- imply
  (‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 = ‖1 + r‖ ^ 2 * z.re ^ 2 + 4 * r.im * z.re * z.im + ‖1 - r‖ ^ 2 * z.im ^ 2) ∧ (‖1 + r‖ ^ 2 + ‖1 - r‖ ^ 2 = 2 * (1 + ‖r‖ ^ 2)) ∧ (‖1 + r‖ ≠ 0 → (1 - ‖r‖ ^ 2) ^ 2 + ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 = ‖1 + r‖ ^ 2 * ((z.re + 2 * r.im * z.im / ‖1 + r‖ ^ 2) ^ 2 + ((1 - ‖r‖ ^ 2) * Real.sqrt (z.im ^ 2 + ‖1 + r‖ ^ 2) / ‖1 + r‖ ^ 2) ^ 2)) ∧ (‖1 - r‖ ≠ 0 → (1 - ‖r‖ ^ 2) ^ 2 + ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 = ‖1 - r‖ ^ 2 * ((z.im + 2 * r.im * z.re / ‖1 - r‖ ^ 2) ^ 2 + ((1 - ‖r‖ ^ 2) * Real.sqrt (z.re ^ 2 + ‖1 - r‖ ^ 2) / ‖1 - r‖ ^ 2) ^ 2)) := by
  -- proof
  have hq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have e0 : ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 = ((1 + r.re) * z.re + r.im * z.im) ^ 2 + ((r.re - 1) * z.im - r.im * z.re) ^ 2 := by
    rw [hq]
    congr 1
    ·
      congr 1
      simp [Complex.conj_re, Complex.conj_im]
      ring
    ·
      congr 1
      simp [Complex.conj_re, Complex.conj_im]
      ring
  have eA : ‖1 + r‖ ^ 2 = (1 + r.re) ^ 2 + r.im ^ 2 := by
    rw [hq]
    simp
  have eC : ‖1 - r‖ ^ 2 = (1 - r.re) ^ 2 + r.im ^ 2 := by
    rw [hq]
    simp
  have et : ‖r‖ ^ 2 = r.re ^ 2 + r.im ^ 2 := hq r
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [e0, eA, eC]
    ring
  ·
    rw [eA, eC, et]
    ring
  ·
    intro hA
    have hA2 : ‖1 + r‖ ^ 2 ≠ 0 := pow_ne_zero 2 hA
    have hs : Real.sqrt (z.im ^ 2 + ‖1 + r‖ ^ 2) ^ 2 = z.im ^ 2 + ‖1 + r‖ ^ 2 := Real.sq_sqrt (by positivity)
    rw [div_pow, mul_pow, hs, e0, et]
    rw [eA] at hA2 ⊢
    field_simp
    ring
  ·
    intro hC
    have hC2 : ‖1 - r‖ ^ 2 ≠ 0 := pow_ne_zero 2 hC
    have hs : Real.sqrt (z.re ^ 2 + ‖1 - r‖ ^ 2) ^ 2 = z.re ^ 2 + ‖1 - r‖ ^ 2 := Real.sq_sqrt (by positivity)
    rw [div_pow, mul_pow, hs, e0, et]
    rw [eC] at hC2 ⊢
    field_simp
    ring


-- created on 2026-10-20
