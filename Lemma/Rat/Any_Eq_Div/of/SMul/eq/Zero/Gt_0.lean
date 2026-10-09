import Mathlib
import sympy.Basic


/--
[AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd.lean)
-/
@[path]
private lemma main
  {t : AddCircle (1 : ℚ)}
  {n N : ℕ}
-- given
  (hN : 0 < N)
  (hnN : n ∣ N)
  (ht : n • t = 0) :
-- imply
  ∃ a : ℤ, t = (((a : ℚ) / (N : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
-- proof
  have hn : n ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hnN
    omega
  induction t using QuotientAddGroup.induction_on with
  | H q =>

    have hq : ((n • q : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [AddCircle.coe_nsmul]; exact ht
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hq
    obtain ⟨d, hd⟩ := hnN
    refine ⟨k * d, ?_⟩
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [eq_div_iff hN', hd]
    push_cast
    rw [hk]
    ring


-- created on 2026-10-01
