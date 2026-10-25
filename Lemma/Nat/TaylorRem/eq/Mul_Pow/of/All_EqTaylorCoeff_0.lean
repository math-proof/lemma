import Mathlib
import sympy.Basic
import Def.AlgebraicCurve_PlaceTaylorCoeff
import Lemma.Int.P2MUtil

open AlgebraicCurve AlgebraicCurve.Place

/--
[AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {t f : F}
  {e : ℕ}
-- given
  (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
-- imply
  taylorRem v t f e = f * t⁻¹ ^ e := by
-- proof
  induction e with
    | zero => simp
    | succ e ih =>
      rw [taylorRem_succ', h e (Nat.lt_succ_self e), map_zero, sub_zero,
        ih (fun q hq => h q (Nat.lt_succ_of_lt hq)), pow_succ, mul_assoc]


-- created on 2026-10-23
