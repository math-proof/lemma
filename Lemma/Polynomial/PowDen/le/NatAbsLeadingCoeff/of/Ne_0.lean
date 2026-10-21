import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_den_pow_le_natAbs_leadingCoeff_of_pow_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X])
  (q : ℚ)
  (k : ℕ)
-- given
  (hdiv : (C (q.den : ℤ) * X - C q.num) ^ k ∣ P)
  (hP : P ≠ 0) :
-- imply
  q.den ^ k ≤ P.leadingCoeff.natAbs := by
-- proof
  let L : ℤ[X] := C (q.den : ℤ) * X - C q.num
  have hL : L.leadingCoeff = (q.den : ℤ) := by
    dsimp [L]
    rw [leadingCoeff_sub_of_degree_lt]
    ·
      exact leadingCoeff_C_mul_X _
    ·
      rw [degree_C_mul_X (by exact_mod_cast q.pos.ne')]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hdvdZ : ((q.den ^ k : ℕ) : ℤ) ∣ P.leadingCoeff := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [hQ, leadingCoeff_mul, leadingCoeff_pow, hL]
    norm_cast
    exact dvd_mul_right _ _
  refine Nat.le_of_dvd
    (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hP)) ?_
  simpa using (Int.natAbs_dvd_natAbs.mpr hdvdZ)


-- created on 2026-10-21
