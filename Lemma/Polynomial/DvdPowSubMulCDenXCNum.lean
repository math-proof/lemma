import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.IsPrimitiveSubMulCDenXCNum
import Lemma.Polynomial.IsPrimitivePow.of.IsPrimitive
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_rat_linear_pow_dvd_of_map_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X])
  (q : ℚ)
  (k : ℕ)
-- given
  (hdiv : (X - C q) ^ k ∣ P.map (Int.castRingHom ℚ)) :
-- imply
  (C (q.den : ℤ) * X - C q.num) ^ k ∣ P := by
-- proof
  let L : ℤ[X] := C (q.den : ℤ) * X - C q.num
  let A : ℚ[X] := X - C q
  have hmapL : L.map (Int.castRingHom ℚ) = C (q.den : ℚ) * A := by
    dsimp [L, A]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, mul_sub, ← Polynomial.C_mul, Rat.den_mul_eq_num]
    rfl
  have hunit : IsUnit (C (q.den : ℚ)) :=
    isUnit_C.mpr
      (show IsUnit (q.den : ℚ) from
        (by exact_mod_cast q.pos.ne' : (q.den : ℚ) ≠ 0).isUnit)
  have hassoc : Associated ((L ^ k).map (Int.castRingHom ℚ)) (A ^ k) := by
    rw [Polynomial.map_pow, hmapL, mul_pow]
    exact associated_unit_mul_left _ _ (hunit.pow k)
  apply (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
    (L ^ k) P
    (IsPrimitivePow.of.IsPrimitive L k (IsPrimitiveSubMulCDenXCNum q))).mpr
  rwa [Associated.dvd_iff_dvd_left hassoc]


-- created on 2026-10-21
