import Mathlib
import sympy.algebra.adic_completion.polynomial_completion
import sympy.algebra.adic_completion.ring_functoriality
import sympy.algebra.adic_completion.semilocal
import sympy.algebra.adic_completion.tensor_ring
import sympy.algebra.adic_completion.galois_action

open IsLocalRing
open scoped AdicCompletion.GaloisAction

namespace BDescN6

theorem map_le {C : Type*} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] :
    𝔫.map (Algebra.ofId C S) ≤ maximalIdeal S := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔫 S]
  exact le_of_eq rfl

theorem levelMap_bijective {C : Type*} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] (n : ℕ) :
    Function.Bijective
      (AdicCompletion.levelMapₐ 𝔫 (maximalIdeal S) (Algebra.ofId C S) (map_le 𝔫 S) n) := by
  classical
  have hmS : maximalIdeal S ^ n = (𝔫 ^ n).map (algebraMap C S) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔫 S, Ideal.map_pow]
  constructor
  ·
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AdicCompletion.levelMapₐ_mk, AdicCompletion.levelMapₐ_mk, Ideal.Quotient.eq,
      Algebra.ofId_apply, Algebra.ofId_apply, ← map_sub, hmS,
      IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl] at hxy
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := hxy
    simp only at h
    rw [← map_mul] at h
    obtain ⟨⟨t, ht⟩, ht'⟩ := (IsLocalization.eq_iff_exists 𝔫.primeCompl S).mp h
    simp only at ht'
    rw [Ideal.Quotient.eq]
    have hmem : t * s * (x - y) ∈ 𝔫 ^ n := by
      have : t * ((x - y) * s) ∈ 𝔫 ^ n := by
        rw [ht']; exact Ideal.mul_mem_left _ _ ha
      have heq : t * s * (x - y) = t * ((x - y) * s) := by ring
      rw [heq]; exact this
    have hu : IsUnit (Ideal.Quotient.mk (𝔫 ^ n) (t * s)) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [pow_zero, Ideal.one_eq_top]; exact isUnit_of_subsingleton _
      · exact Ideal.Quotient.isUnit_mk_pow_of_notMem (I := 𝔫)
          (fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hs)
    have h0 : Ideal.Quotient.mk (𝔫 ^ n) (t * s) * Ideal.Quotient.mk (𝔫 ^ n) (x - y) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
    have : Ideal.Quotient.mk (𝔫 ^ n) (x - y) = 0 := (hu.mul_right_eq_zero).mp h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  ·
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl z
    have hu : IsUnit (Ideal.Quotient.mk (𝔫 ^ n) s) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [pow_zero, Ideal.one_eq_top]; exact isUnit_of_subsingleton _
      · exact Ideal.Quotient.isUnit_mk_pow_of_notMem (I := 𝔫) hs
    obtain ⟨t, ht⟩ :=
      Ideal.Quotient.mk_surjective ((hu.unit⁻¹ : (C ⧸ 𝔫 ^ n)ˣ) : C ⧸ 𝔫 ^ n)
    have hst : s * t - 1 ∈ 𝔫 ^ n := by
      rw [← Ideal.Quotient.eq, map_mul, ht, map_one]; exact hu.mul_val_inv
    refine ⟨Ideal.Quotient.mk (𝔫 ^ n) (a * t), ?_⟩
    rw [AdicCompletion.levelMapₐ_mk, Algebra.ofId_apply, Ideal.Quotient.eq, hmS]
    have hsp : IsLocalization.mk' S a ⟨s, hs⟩ * algebraMap C S s = algebraMap C S a :=
      IsLocalization.mk'_spec S a ⟨s, hs⟩
    have : algebraMap C S (a * t) - IsLocalization.mk' S a ⟨s, hs⟩ =
        IsLocalization.mk' S a ⟨s, hs⟩ * algebraMap C S (s * t - 1) := by
      rw [map_sub, map_one, map_mul, map_mul, ← hsp]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hst)

/-- Localization-at-prime induces an equivalence of adic completions. -/
noncomputable def adicEquiv {C : Type*} [CommRing C] (𝔫 : Ideal C) [𝔫.IsMaximal]
    (S : Type*) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫] :
    AdicCompletion 𝔫 C ≃+* AdicCompletion (maximalIdeal S) S :=
  (AdicCompletion.mapAlgEquivOfBijective 𝔫 (maximalIdeal S) (Algebra.ofId C S)
    (map_le 𝔫 S) (levelMap_bijective 𝔫 S)).toRingEquiv

end BDescN6

/-- Algebra structure on adic completions along a lying-over prime. -/
noncomputable instance instAlgebraAdicCompletion {O : Type*} [CommRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] {𝔫 : Ideal C} [𝔫.LiesOver (maximalIdeal O)] :
    Algebra (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) :=
  AdicCompletion.instAlgebraOfLiesOver (maximalIdeal O) 𝔫

noncomputable instance instIsScalarTowerAdicCompletion {O : Type*} [CommRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] {𝔫 : Ideal C} [𝔫.LiesOver (maximalIdeal O)] :
    IsScalarTower O (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) :=
  AdicCompletion.instIsScalarTowerOfLiesOver (maximalIdeal O) 𝔫
