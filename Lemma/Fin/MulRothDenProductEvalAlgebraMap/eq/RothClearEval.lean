import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_denProduct_mul_eval₂](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
-- given
  (hP : rothDegreeBound P r) :
-- imply
  (rothDenProduct q r : ℚ) * MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P =
    (rothClearEval P q r : ℚ) := by
-- proof
  classical
  unfold rothDenProduct rothClearEval
  rw [MvPolynomial.eval₂_eq']
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hcoord (h : Fin m) :
    ((q h).den : ℚ) ^ r h * q h ^ d h =
      ((((q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)) : ℤ) : ℚ) := by
    have hcast :
      ((((q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)) : ℤ) : ℚ) =
        ((q h).num : ℚ) ^ d h * ((q h).den : ℚ) ^ (r h - d h) := by
      push_cast
      rfl
    rw [hcast]
    calc
      _ = ((q h).den : ℚ) ^ r h * (((q h).num : ℚ) / (q h).den) ^ d h := by
        rw [(q h).num_div_den]
      _ = ((q h).num : ℚ) ^ d h * ((q h).den : ℚ) ^ (r h - d h) := by
        rw [div_pow]
        have hden : ((q h).den : ℚ) ≠ 0 := by
          exact_mod_cast (q h).den_nz
        field_simp
        have hp : ((q h).den : ℚ) ^ r h =
            ((q h).den : ℚ) ^ d h * ((q h).den : ℚ) ^ (r h - d h) := by
          rw [← pow_add, Nat.add_sub_of_le (hP d hd h)]
        rw [hp]
        ring
  have hmul :
    (∏ h, ((q h).den : ℚ) ^ r h) *
        ((algebraMap ℤ ℚ) (P.coeff d) * ∏ h, q h ^ d h) =
      (P.coeff d : ℚ) *
        ((∏ h, ((q h).den : ℚ) ^ r h) * ∏ h, q h ^ d h) := by
    rw [algebraMap_int_eq, Int.coe_castRingHom]
    dsimp only
    ring
  rw [hmul, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hcoord h


-- created on 2026-10-21
