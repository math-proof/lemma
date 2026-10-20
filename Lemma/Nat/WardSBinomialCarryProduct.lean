import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.WardSBinomialCarryProduct
open MetaMathlibExt


/--
[ward_sbinomial_carry_product_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma ward_sbinomial_carry_product_general_eq
  {s f : ℕ → ℤ}
  {n m : ℕ}
-- given
  (hs : ∀ b, 0 < b → s b ≠ 0)
  (hf : ∀ k, 0 < k → f k = ∏ d ∈ Nat.divisors k, s d) :
-- imply
  ((∏ i ∈ Finset.Icc 1 (n + m), f i : ℤ) : ℚ) /
    (((∏ i ∈ Finset.Icc 1 n, f i : ℤ) : ℚ) * ((∏ i ∈ Finset.Icc 1 m, f i : ℤ) : ℚ)) =
    ((wardGeneralizedBinomialCoefficient s n m : ℤ) : ℚ) := by
-- proof
  apply MetaMathlibExt.ward_sbinomial_carry_product_general s hs f hf n m

/--
[ward_sbinomial_carry_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma ward_sbinomial_carry_product_eq
  {s f : Nat → Int}
  {n m : Nat}
-- given
  (hs : ∀ b, s b ≠ 0)
  (hf : ∀ k, f k = ∏ d ∈ Nat.divisors k, s d) :
-- imply
  let fFactorial : Nat → Int := by
-- proof
  apply MetaMathlibExt.ward_sbinomial_carry_product s hs f hf n m


-- created on 2026-10-20
