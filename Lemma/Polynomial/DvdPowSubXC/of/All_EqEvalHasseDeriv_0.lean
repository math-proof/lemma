import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_X_sub_C_pow_dvd_of_hasse_eval_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℚ[X])
  (q : ℚ)
  (k : ℕ)
-- given
  (hzero : ∀ n < k, (hasseDeriv n P).eval q = 0) :
-- imply
  (X - C q) ^ k ∣ P := by
-- proof
  rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
  intro n hn
  rw [taylor_coeff]
  exact hzero n hn


-- created on 2026-10-21
