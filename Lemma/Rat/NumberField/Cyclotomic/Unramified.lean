import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Cyclotomic.Unramified
open scoped NumberField
open IsCyclotomicExtension.Rat


/--
[isUnramifiedIn_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Cyclotomic/Unramified.lean)
-/
@[path]
private lemma isUnramifiedIn_of_not_dvd_eq
  [Field K] [NumberField K]
  {m p : ℕ} [NeZero m] [IsCyclotomicExtension {m} ℚ K]
-- given
  (hp : p.Prime)
  (hm : ¬ p ∣ m) :
-- imply
  Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
-- proof
  apply IsCyclotomicExtension.Rat.isUnramifiedIn_of_not_dvd hp K hm

/--
[isUnramifiedIn_divMaxPow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Cyclotomic/Unramified.lean)
-/
@[path]
private lemma isUnramifiedIn_divMaxPow_eq
  {m p : ℕ} [NeZero m]
-- given
  (hp : p.Prime) :
-- imply
  Algebra.IsUnramifiedIn
    (𝓞 (CyclotomicField (Nat.divMaxPow m p) ℚ))
    (Ideal.span {(p : ℤ)}) := by
-- proof
  apply IsCyclotomicExtension.Rat.isUnramifiedIn_divMaxPow m p hp

/--
[eq_bot_of_isUnramifiedIn_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Cyclotomic/Unramified.lean)
-/
@[path]
private lemma eq_bot_of_isUnramifiedIn_prime_pow_eq
  [Field L] [NumberField L]
  {p e : ℕ}
  {E₁ : IntermediateField ℚ L} [IsCyclotomicExtension {p ^ e} ℚ E₁]
  {F : IntermediateField ℚ L}
-- given
  (hp : p.Prime)
  (hFE₁ : F ≤ E₁)
  (hF : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)})) :
-- imply
  F = ⊥ := by
-- proof
  apply IsCyclotomicExtension.Rat.eq_bot_of_isUnramifiedIn_prime_pow hp L E₁ F hFE₁ hF


-- created on 2026-10-20
