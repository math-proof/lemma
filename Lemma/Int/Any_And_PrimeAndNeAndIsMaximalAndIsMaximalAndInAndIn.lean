import Mathlib
import sympy.Basic


attribute [local instance] Ideal.Quotient.field


private lemma int_isJacobsonRing :
-- imply
  IsJacobsonRing ℤ := by
-- proof
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  if hbot : P = ⊥ then
    subst hbot
    apply le_antisymm _ Ideal.le_jacobson
    intro n hn
    rw [Ideal.mem_bot]
    by_contra hn0
    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hprime : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
    have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := IsPrime.to_maximal_ideal hne
    have hmem : n ∈ Ideal.span {(p : ℤ)} := by
      have := (Ideal.mem_sInf.1 hn) (show Ideal.span {(p : ℤ)} ∈ {J : Ideal ℤ | ⊥ ≤ J ∧ J.IsMaximal} from ⟨bot_le, hmax⟩)
      apply this
    rw [Ideal.mem_span_singleton] at hmem
    have h1 : (p : ℤ).natAbs ≤ n.natAbs := Int.natAbs_le_of_dvd_ne_zero hmem hn0
    simp at h1
    omega
  else
    have : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    apply Ideal.jacobson_eq_self_of_isMaximal


private lemma exists_prime_natCast_eq_zero
  {K : Type} [Field K] [Algebra.FiniteType ℤ K] :
-- imply
  ∃ p : ℕ, p.Prime ∧ (p : K) = 0 := by
-- proof
  have := int_isJacobsonRing
  have hfin : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  have : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := by
    intro hp0
    subst hp0
    have : CharZero K := CharP.charP_to_charZero K
    apply Int.not_isField ((Algebra.IsIntegral.isField_iff_isField (show Function.Injective (algebraMap ℤ K) from RingHom.injective_int _)).2 (Field.toIsField _))
  have hpp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  refine ⟨p, hpp, CharP.cast_eq_zero K p⟩


private lemma exists_prime_natCast_mem
  {B : Type} [CommRing B] [Algebra.FiniteType ℤ B]
  {𝔪 : Ideal B}
-- given
  (h𝔪 : 𝔪.IsMaximal) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (p : B) ∈ 𝔪 := by
-- proof
  let _ : Algebra ℤ (B ⧸ 𝔪) := Ideal.Quotient.algebra ℤ
  have hft : Algebra.FiniteType ℤ (B ⧸ 𝔪) := inferInstance
  obtain ⟨p, hpp, hp⟩ := @exists_prime_natCast_eq_zero (B ⧸ 𝔪) (Ideal.Quotient.field 𝔪) hft
  refine ⟨p, hpp, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  apply hp


/--
[Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero.lean)
-/
@[path]
private lemma main
  {A : Type} [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] :
-- imply
  ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A),
    p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ 𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧ (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ := by
-- proof
  classical
  have := int_isJacobsonRing
  have hAJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℤ) (B := A)
  obtain ⟨𝔪₁, h𝔪₁⟩ := Ideal.exists_maximal A
  obtain ⟨p₁, hp₁, hp₁m⟩ := exists_prime_natCast_mem (𝔪 := 𝔪₁) h𝔪₁
  have hp₁0 : (p₁ : A) ≠ 0 := by
    exact_mod_cast hp₁.ne_zero
  let B := Localization.Away (p₁ : A)
  have : IsDomain B :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hp₁0)
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal B
  obtain ⟨h𝔪₂, hp₁not⟩ := (IsLocalization.isMaximal_iff_isMaximal_disjoint B (p₁ : A) 𝔫).1 h𝔫
  obtain ⟨p₂, hp₂, hp₂m⟩ := exists_prime_natCast_mem (𝔪 := 𝔫.under A) h𝔪₂
  have hne : p₁ ≠ p₂ := by
    intro hne
    subst hne
    apply hp₁not hp₂m
  refine ⟨p₁, p₂, 𝔪₁, 𝔫.under A, hp₁, hp₂, hne, h𝔪₁, h𝔪₂, hp₁m, hp₂m⟩


-- created on 2026-10-13
