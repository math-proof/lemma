import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.FibrePoly
import Lemma.Int.P2MUtil

open Polynomial ModularCurve

/--
[ModularCurve_fibrePoly_eq_of_kroneckerCongruence](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence.lean)
-/
@[path]
private lemma main
  [Field k]
  {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
  {data : ModularCurve.ModularPolynomialData ℓ}
  {a : k}
-- given
  (hK : ModularCurve.KroneckerCongruence ℓ data) :
-- imply
  ModularCurve.fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by
-- proof
  have hK' : reduceModBivar ℓ data.Φ =
      (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := hK
  rw [fibrePoly_eq_map_reduceModBivar (ℓ := ℓ), hK']
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_pow]


-- created on 2026-10-23
