import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsAdicComplete_of_isNilpotent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAdicComplete_of_isNilpotent.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {I : Ideal R}
-- given
  (hI : IsNilpotent I) :
-- imply
  IsAdicComplete I R := by
-- proof
  obtain ⟨N, hN⟩ := hI
  have : IsHausdorff I R := ⟨fun x hx => by
    have h := hx N
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hN] at h
    exact h⟩
  have : IsPrecomplete I R := ⟨fun {f} hf => ⟨f N, fun n => by
    rcases le_or_gt n N with hn | hn
    · exact hf hn
    · have hzero : (I ^ n • ⊤ : Ideal R) = ⊥ := by
        rw [smul_eq_mul, Ideal.mul_top, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
        exact Ideal.pow_le_pow_right hn.le
      rw [SModEq.sub_mem, hzero, Ideal.mem_bot, sub_eq_zero]
      have h := hf hn.le
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hN, Ideal.zero_eq_bot, Ideal.mem_bot,
        sub_eq_zero] at h
      exact h.symm⟩⟩
  exact ⟨⟩


-- created on 2026-10-05
