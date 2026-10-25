import Mathlib
import sympy.Basic
import Def.ModularCurve_LegendreJ
import Lemma.Int.P2MUtil
open ModularCurve


/-- ported from external source -/

private lemma  legendreJ_eq_ofNat_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
  legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have h64 : (64 : K) ≠ 0 := by
    rw [show (64 : K) = 2 ^ 6 by norm_num]; apply pow_ne_zero _ h2
  rw [legendreJ, div_eq_iff hden]
  constructor
  ·
    intro h
    have key : (64 : K) * ((t + 1) ^ 2 * ((t - 2) ^ 2 * (2 * t - 1) ^ 2)) = 0 := by
      linear_combination h
    have key' := (mul_eq_zero.mp key).resolve_left h64
    refine Or.elim (mul_eq_zero.mp key') ?_ ?_
    ·
      intro h
      exact Or.inl (add_eq_zero_iff_eq_neg.mp ((pow_eq_zero_iff two_ne_zero).mp h))
    ·
      intro h
      refine Or.elim (mul_eq_zero.mp h) ?_ ?_
      ·
        intro h
        exact Or.inr (Or.inl (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)))
      ·
        intro h
        have h' : 2 * t - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h
        refine Or.inr (Or.inr (eq_inv_of_mul_eq_one_right (by linear_combination h')))
  ·
    rintro (rfl | rfl | ht)
    · norm_num
    · norm_num
    ·
      have h2t : (2 : K) * t = 1 := by rw [ht, mul_inv_cancel₀ h2]
      linear_combination
        (128 * t ^ 5 - 320 * t ^ 4 - 256 * t ^ 3 + 704 * t ^ 2 + 256 * t - 256) * h2t
p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff.ModularCurve"
@[path]
private lemma main
  [Field K]
  {t : K}
-- given
  (h0 : (2 : K) ≠ 0)
  (ht0 : t ≠ 0)
  (ht1 : t ≠ 1) :
-- imply
  legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ :=
-- proof
  legendreJ_eq_ofNat_iff' h0 ht0 ht1


-- created on 2026-10-23
