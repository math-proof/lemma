import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.Unramified.Part2
import Lemma.Nat.NumberField.Unramified
open scoped NumberField


namespace IsCyclotomicExtension.Rat

/--
[isUnramifiedIn_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Cyclotomic/Unramified.lean)
-/
@[path]
lemma isUnramifiedIn_of_not_dvd
  [Field K] [NumberField K]
  {m p : ℕ} [NeZero m] [IsCyclotomicExtension {m} ℚ K]
-- given
  (hp : p.Prime)
  (hm : ¬ p ∣ m) :
-- imply
  Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
-- proof
  let _ : Fact p.Prime := ⟨hp⟩
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P hP hLie
  have _ := hP
  have _ := hLie
  exact ramificationIdx_eq_of_not_dvd p K P hm

end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

/--
[isUnramifiedIn_divMaxPow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Cyclotomic/Unramified.lean)
-/
@[path]
lemma isUnramifiedIn_divMaxPow
  {m p : ℕ} [NeZero m]
-- given
  (hp : p.Prime) :
-- imply
  Algebra.IsUnramifiedIn
    (𝓞 (CyclotomicField (Nat.divMaxPow m p) ℚ))
    (Ideal.span {(p : ℤ)}) := by
-- proof
  have h_eq := Nat.divMaxPow_mul_pow_padicValNat p m
  have hne : Nat.divMaxPow m p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h_eq
    exact NeZero.ne m h_eq.symm
  let _ : NeZero (Nat.divMaxPow m p) := ⟨hne⟩
  let _ : NeZero ((Nat.divMaxPow m p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hne⟩
  let _ : IsCyclotomicExtension {Nat.divMaxPow m p} ℚ
    (CyclotomicField (Nat.divMaxPow m p) ℚ) :=
    CyclotomicField.isCyclotomicExtension (Nat.divMaxPow m p) ℚ
  exact isUnramifiedIn_of_not_dvd (m := Nat.divMaxPow m p) (p := p) hp
    (CyclotomicField (Nat.divMaxPow m p) ℚ)
    (Nat.not_dvd_divMaxPow hp.one_lt (NeZero.ne m))

end IsCyclotomicExtension.Rat

namespace IsCyclotomicExtension.Rat

/--
[eq_bot_of_isUnramifiedIn_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Cyclotomic/Unramified.lean)
-/
@[path]
lemma eq_bot_of_isUnramifiedIn_prime_pow
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
  by_contra hFne
  have hfin : Module.finrank ℚ F ≠ 1 :=
    fun h => hFne (IntermediateField.finrank_eq_one_iff.mp h)
  obtain ⟨q, hq, hram⟩ : ∃ q : ℕ, q.Prime ∧
    ¬ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)}) :=
    NumberField.exists_not_isUnramifiedIn hfin
  apply hram
  by_cases hqp : q = p
  · subst hqp
    exact hF
  · have hqdvd : ¬ q ∣ p ^ e := by
    intro hd
    exact hqp (Nat.prime_eq_prime_of_dvd_pow hq hp hd)
    have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact NumberField.isUnramifiedIn_mono F E₁ hFE₁ (Ideal.span {(q : ℤ)})
      (isUnramifiedIn_of_not_dvd (m := p ^ e) (p := q) hq E₁ hqdvd)

end IsCyclotomicExtension.Rat


-- created on 2026-10-20
-- updated on 2026-10-23
