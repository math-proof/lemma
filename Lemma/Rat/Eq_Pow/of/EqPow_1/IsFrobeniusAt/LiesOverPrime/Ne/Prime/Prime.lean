import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_WeierstrassCurve_ReductionMap
import Lemma.Int.P2MUtil

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

/--
[ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow.lean)
-/
@[path]
private lemma main
  {p q : ℕ}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
  {ζ : AlgebraicClosure ℚ}
-- given
  (hp : p.Prime)
  (hq : q.Prime)
  (hqp : q ≠ p)
  (hA : A.LiesOverPrime q)
  (hσ : A.IsFrobeniusAt σ q)
  (hζ : ζ ^ p = 1) :
-- imply
  σ ζ = ζ ^ q := by
-- proof
  classical

  have hint : IsIntegral A ζ := by
    refine ⟨Polynomial.X ^ p - 1, ?_, ?_⟩
    · simpa using Polynomial.monic_X_pow_sub_C (1 : A) hp.ne_zero
    · simp [hζ]
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hζA : ζ ∈ A := by rw [← hz]; exact z.2

  have hu : σ ζ ∈ A :=
    ((⟨σ, hσ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) • (⟨ζ, hζA⟩ : A)).2
  have hw : ζ ^ q ∈ A := pow_mem hζA q

  have hap : (⟨σ ζ, hu⟩ : A) ^ p = 1 := by
    have h1 : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ, map_one]
    exact Subtype.ext (by push_cast; exact h1)
  have hbp : (⟨ζ ^ q, hw⟩ : A) ^ p = 1 := by
    have h1 : (ζ ^ q) ^ p = 1 := by rw [← pow_mul, mul_comm q p, pow_mul, hζ, one_pow]
    exact Subtype.ext (by push_cast; exact h1)

  have hres : IsLocalRing.residue A (⟨σ ζ, hu⟩ : A) = IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) := by
    have h1 := hσ.smul_residue_eq (IsLocalRing.residue A (⟨ζ, hζA⟩ : A))
    rw [← IsLocalRing.ResidueField.residue_smul] at h1
    rw [show (⟨σ, hσ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) • (⟨ζ, hζA⟩ : A)
        = ⟨σ ζ, hu⟩ from Subtype.ext rfl] at h1
    rw [← map_pow] at h1
    rw [show (⟨ζ, hζA⟩ : A) ^ q = ⟨ζ ^ q, hw⟩ from Subtype.ext (by push_cast; rfl)] at h1
    exact h1

  by_contra hne
  have hab : (⟨σ ζ, hu⟩ : A) - ⟨ζ ^ q, hw⟩ ≠ 0 := by
    intro h
    exact hne (congrArg Subtype.val (sub_eq_zero.mp h))
  have key : (∑ i ∈ Finset.range p, (⟨σ ζ, hu⟩ : A) ^ i * (⟨ζ ^ q, hw⟩ : A) ^ (p - 1 - i)) *
      ((⟨σ ζ, hu⟩ : A) - ⟨ζ ^ q, hw⟩) = 0 := by
    rw [geom_sum₂_mul, hap, hbp, sub_self]
  have hS : (∑ i ∈ Finset.range p, (⟨σ ζ, hu⟩ : A) ^ i * (⟨ζ ^ q, hw⟩ : A) ^ (p - 1 - i)) = 0 :=
    (mul_eq_zero.mp key).resolve_right hab

  have hsum : (p : IsLocalRing.ResidueField A) *
      IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ (p - 1) = 0 := by
    have h0 := congrArg (IsLocalRing.residue A) hS
    rw [map_sum, _root_.map_zero] at h0
    have h1 : ∀ i ∈ Finset.range p,
        IsLocalRing.residue A ((⟨σ ζ, hu⟩ : A) ^ i * (⟨ζ ^ q, hw⟩ : A) ^ (p - 1 - i))
          = IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ (p - 1) := by
      intro i hi
      have hip : i + (p - 1 - i) = p - 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [map_mul, map_pow, map_pow, hres, ← pow_add, hip]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    exact h0

  have htne : IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ (p - 1) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have h1 : IsLocalRing.residue A (⟨ζ ^ q, hw⟩ : A) ^ p = 1 := by
      rw [← map_pow, hbp, map_one]
    rw [h0, zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1

  have hp0 : (p : IsLocalRing.ResidueField A) = 0 := (mul_eq_zero.mp hsum).resolve_right htne
  haveI hchar : CharP (IsLocalRing.ResidueField A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp ((CharP.cast_eq_zero_iff _ q p).mp hp0))


-- created on 2026-10-23
