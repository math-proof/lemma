/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Instance.NumberTheory.NumberField.Ideal.Counting.Part2
open scoped NumberField


namespace NumberField

namespace Ideal

variable (K : Type*) [Field K] [NumberField K]

/-- Every bounded nonzero prime ideal lies above a small rational prime. -/
theorem exists_prime_liesOver {P : Ideal (𝓞 K)} (M : ℕ)
    (hprime : P.IsPrime) (hbot : P ≠ ⊥) (hle : Ideal.absNorm P ≤ M) :
    ∃ p : ℕ, p.Prime ∧ p ≤ M ∧
      P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  have hPprime : P.IsPrime := hprime
  haveI := hprime
  obtain ⟨q, hq⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hqspan : Ideal.span ({q} : Set ℤ) = P.under ℤ := hq.symm
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hbot
    have hunder : P.under ℤ = ⊥ := by
      rw [← hqspan]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    exact Ideal.eq_bot_of_under_eq_bot hunder
  have hgen_prime : (Ideal.span ({q} : Set ℤ)).IsPrime := by
    rw [hqspan]
    infer_instance
  have hqprime : Prime q := (Ideal.span_singleton_prime hq0).mp hgen_prime
  have hspan : Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ) =
      Ideal.span ({q} : Set ℤ) := by
    rcases abs_choice q with h | h <;> simp [h]
  have hlie : P.LiesOver (Ideal.span ({q} : Set ℤ)) := by
    rcases abs_choice q with h | h <;>
      simpa [h, Ideal.span_singleton_neg q, ← Ideal.submodule_span_eq, ← hq]
        using Ideal.over_under P
  have hlieN : P.LiesOver (Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ)) := by
    rw [hspan]
    exact hlie
  have hlieI : P.LiesOver (Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ)) := hlieN
  haveI := hlieN
  have hpow := Ideal.pow_inertiaDeg q.natAbs P
  have hpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have h1 : 1 ≤ q.natAbs := Int.natAbs_pos.mpr hq0
  refine ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hqprime, ?_, hlieN⟩
  calc q.natAbs ≤ q.natAbs ^ P.inertiaDeg ℤ := le_self_pow₀ h1 hpos.ne'
    _ = Ideal.absNorm P := hpow
    _ ≤ M := hle

/-- Prime factors of a bounded ideal are prime, nonzero, and bounded. -/
theorem factor_props {M : ℕ} {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hle : Ideal.absNorm I ≤ M)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ M := by
  obtain ⟨hprime, hleIP⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hP
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact hI (le_bot_iff.mp hleIP)
  have hdvd : P ∣ I :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hnorm : Ideal.absNorm P ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd)
  have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  have hPle : Ideal.absNorm P ≤ M :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hnorm).trans hle
  exact ⟨hprime, hPbot, hPle⟩

end Ideal
end NumberField
