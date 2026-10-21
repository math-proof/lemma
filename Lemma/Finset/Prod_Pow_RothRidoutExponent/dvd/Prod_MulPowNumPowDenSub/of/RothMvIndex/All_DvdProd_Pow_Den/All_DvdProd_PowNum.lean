import Mathlib
import Lemma.Finset.Prod_Pow_RothRidoutExponent.eq.Prod_MulPowProd_PowPowProd_PowSub.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Finset


/--
[roth_ridout_prime_product_dvd_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (q : Fin m → ℚ)
-- given
  (hnum : ∀ h, ((∏ l ∈ S, p l ^ a h l : ℕ) : ℤ) ∣ (q h).num)
  (hden : ∀ h, (∏ l ∈ S, p l ^ b h l) ∣ (q h).den)
  (k : RothMvIndex m) :
-- imply
  ((∏ l ∈ S, p l ^ rothRidoutExponent r a b k l : ℕ) : ℤ) ∣
    ∏ h, (q h).num ^ k h * ((q h).den : ℤ) ^ (r h - k h) := by
-- proof
  rw [Prod_Pow_RothRidoutExponent.eq.Prod_MulPowProd_PowPowProd_PowSub.of.RothMvIndex]
  push_cast
  apply Finset.prod_dvd_prod_of_dvd
  intro h _
  apply mul_dvd_mul
  ·
    have hnumh := hnum h
    push_cast at hnumh
    apply pow_dvd_pow_of_dvd hnumh
  ·
    apply pow_dvd_pow_of_dvd
    have hdenh := hden h
    exact_mod_cast hdenh


-- created on 2026-10-21
