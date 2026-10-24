/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Ideal/PrimeExtension.lean -/


import Mathlib.RingTheory.Int.Basic
import Lemma.Ideal.PrimeExtension


-- Identity algebra over `ℤ`: every denominator is already cleared, with `c = ⊤`.
example : ((⊥ : Ideal ℤ).map (algebraMap ℤ ℤ)).IsPrime :=
  Ideal.isPrime_map_of_coprime_clearDenom ⊥ ⊤ inferInstance
    (by simpa using Function.injective_id)
    (fun x _ b => ⟨x * b, rfl⟩) (by simp)

-- Quotient-compatible example: `B = ℤ ⧸ ⊥` with the quotient algebra structure.
-- The quotient map is surjective (so `c = ⊤` clears denominators) and injective.
example : ((⊥ : Ideal ℤ).map (algebraMap ℤ (ℤ ⧸ (⊥ : Ideal ℤ)))).IsPrime :=
  Ideal.isPrime_map_of_coprime_clearDenom ⊥ ⊤ inferInstance hinj hclear (by simp)
where
  hinj : Function.Injective (algebraMap ℤ (ℤ ⧸ (⊥ : Ideal ℤ))) := by
    rw [Ideal.Quotient.algebraMap_eq]
    intro a b hab
    have h0 : Ideal.Quotient.mk (⊥ : Ideal ℤ) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h : a - b ∈ (⊥ : Ideal ℤ) := Ideal.Quotient.eq_zero_iff_mem.mp h0
    rw [Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  hclear : ∀ x ∈ (⊤ : Ideal ℤ), ∀ b : ℤ ⧸ (⊥ : Ideal ℤ),
      algebraMap ℤ (ℤ ⧸ (⊥ : Ideal ℤ)) x * b ∈
        Set.range (algebraMap ℤ (ℤ ⧸ (⊥ : Ideal ℤ))) :=
    fun x _ b => Ideal.Quotient.mk_surjective _

-- Maximality over a field with the identity algebra.
example : ((⊥ : Ideal ℚ).map (algebraMap ℚ ℚ)).IsMaximal :=
  Ideal.isMaximal_map_of_coprime_clearDenom ⊥ ⊤ Ideal.bot_isMaximal
    (by simpa using Function.injective_id)
    (fun x _ b => ⟨x * b, rfl⟩) (by simp)

-- Dimension-one corollary: the nonzero prime `span {2}` of `ℤ` extends maximally.
example : ((Ideal.span {(2 : ℤ)}).map (algebraMap ℤ ℤ)).IsMaximal :=
  Ideal.isMaximal_map_of_dimensionLEOne _ ⊤ hprime hne
    (by simpa using Function.injective_id)
    (fun x _ b => ⟨x * b, rfl⟩) (by simp)
where
  hprime : (Ideal.span {(2 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num), Int.prime_iff_natAbs_prime]
    exact Nat.prime_two
  hne : Ideal.span {(2 : ℤ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
