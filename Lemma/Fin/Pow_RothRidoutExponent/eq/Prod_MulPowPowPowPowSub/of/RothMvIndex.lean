import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_ridout_pow_exponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
-- given
  (p : ι → ℕ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (k : RothMvIndex m)
  (l : ι) :
-- imply
  (p l : ℝ) ^ rothRidoutExponent r a b k l =
    ∏ h, ((p l : ℝ) ^ a h l) ^ k h *
      ((p l : ℝ) ^ b h l) ^ (r h - k h) := by
-- proof
  unfold rothRidoutExponent
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro h _
  rw [pow_add, pow_mul, pow_mul]


-- created on 2026-10-21
