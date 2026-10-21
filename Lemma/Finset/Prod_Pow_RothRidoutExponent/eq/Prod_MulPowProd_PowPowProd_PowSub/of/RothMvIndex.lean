import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_ridout_prime_product_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
-- given
  (k : RothMvIndex m) :
-- imply
  (∏ l ∈ S, p l ^ rothRidoutExponent r a b k l) =
    ∏ h, (∏ l ∈ S, p l ^ a h l) ^ k h *
      (∏ l ∈ S, p l ^ b h l) ^ (r h - k h) := by
-- proof
  classical
  unfold rothRidoutExponent
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [pow_add, pow_mul]
  simp only [Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  congr 1
  rw [Finset.prod_comm]


-- created on 2026-10-21
