import Mathlib
import sympy.Basic


/--
[Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
-- given
  (h₁ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₁)
  (h₂ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₂) :
-- imply
  ∃ z ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
-- proof
  by_contra hcon
  have hsub : (IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂ : Set (Ideal R)), (p : Set R) := by
    intro z hz
    rw [Set.biUnion_union]
    by_cases hreg : IsSMulRegular N₁ z
    · refine Set.mem_union_right _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₂]
      exact fun hreg2 => hcon ⟨z, hz, hreg, hreg2⟩
    · refine Set.mem_union_left _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₁]
      exact hreg
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hprime : ∀ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂),
      p ≠ (⊥ : Ideal R) → p ≠ (⊥ : Ideal R) → (id p).IsPrime := by
    rintro p (hp | hp) - -
    · exact hp.isPrime
    · exact hp.isPrime
  obtain ⟨p, hpmem, hple⟩ := (Ideal.subset_union_prime_finite hfin (f := id)
    (I := IsLocalRing.maximalIdeal R) ⊥ ⊥ hprime).mp (by simpa using hsub)
  have hpprime : p.IsPrime := by
    rcases hpmem with hp | hp
    · exact hp.isPrime
    · exact hp.isPrime
  have hpeq : p = IsLocalRing.maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpprime.ne_top) hple
  rw [hpeq] at hpmem
  rcases hpmem with hp | hp
  · exact h₁ hp
  · exact h₂ hp


-- created on 2026-10-05
