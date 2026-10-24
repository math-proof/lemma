import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_ringEquiv_apply_eq_pow_of_isPrimitiveRoot_of_pow_sq_sub_one_eq_of_apply_eq_mul.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (q : ℕ) [Fact q.Prime]
  (ζ π : A)
  (σ : A ≃+* A)
  (α : A)
  (d : ℕ)
  -- given
  (hAq : (q : A) ∈ maximalIdeal A)
  (hζ : IsPrimitiveRoot ζ q)
  (hπ : π ^ (q ^ 2 - 1) = (q : A))
  (hσ : ∀ a : A, σ a - a ∈ maximalIdeal A)
  (hσπ : σ π = α * π)
  (hd : α ^ (q + 1) - (d : A) ∈ maximalIdeal A) :
  -- imply
  σ ζ = ζ ^ d := by
  -- proof
  classical
  have hqp : q.Prime := Fact.out
  have hq1 : 1 < q := hqp.one_lt
  have hq0 : 0 < q := hqp.pos
  let _ : NeZero q := ⟨hqp.ne_zero⟩
  set u : A := ζ - 1 with hu
  have hu0 : u ≠ 0 := hζ.sub_one_ne_zero hq1
  have hqA0 : (q : A) ≠ 0 := (hζ.neZero').out
  have hπ0 : π ≠ 0 := by
    intro h
    apply hqA0
    rw [← hπ, h, zero_pow]
    apply Nat.sub_ne_zero_of_lt (by nlinarith)
  have hprod : (q : A) = ∏ μ ∈ primitiveRoots q A, (1 - μ) := by
    have h := Polynomial.eval_one_cyclotomic_prime (R := A) (p := q)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    apply h.symm
  have hassoc : ∀ μ ∈ primitiveRoots q A, Associated (1 - μ) u := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ q := (mem_primitiveRoots hq0).mp hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨k, -, hk⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply associated_of_dvd_dvd
    ·
      have h1 : (1 - ζ ^ i) ∣ (1 ^ k - (ζ ^ i) ^ k) := sub_dvd_pow_sub_pow 1 (ζ ^ i) k
      rw [one_pow, hk] at h1
      have h2 : u = -(1 - ζ) := by
        rw [hu]
        ring
      rw [h2]
      apply h1.neg_right
    ·
      have h1 : (ζ - 1) ∣ (ζ ^ i - 1 ^ i) := sub_dvd_pow_sub_pow ζ 1 i
      rw [one_pow] at h1
      have h2 : (1 - ζ ^ i) = -(ζ ^ i - 1) := by ring
      rw [h2]
      apply h1.neg_right
  have hcard : (primitiveRoots q A).card = q - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hqp]
  have hq_assoc : Associated (q : A) (u ^ (q - 1)) := by
    rw [hprod, ← hcard, ← Finset.prod_const]
    apply Associated.prod _ _ _ hassoc
  have hvu_ne : IsDiscreteValuationRing.addVal A u ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hvπ_ne : IsDiscreteValuationRing.addVal A π ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hvu_ne
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hvπ_ne
  have hval : (q - 1) • IsDiscreteValuationRing.addVal A u = (q ^ 2 - 1) • IsDiscreteValuationRing.addVal A π := by
    rw [← IsDiscreteValuationRing.addVal_pow, ← IsDiscreteValuationRing.addVal_pow, hπ]
    apply ((IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hq_assoc).symm
  have hba : b = (q + 1) * a := by
    rw [← hb, ← ha] at hval
    have h' : ((q - 1) * b : ℕ) = (q ^ 2 - 1) * a := by
      have := hval
      rw [nsmul_eq_mul, nsmul_eq_mul] at this
      exact_mod_cast this
    have hq2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have : 1 ≤ q := hq1.le
      zify [this, Nat.one_le_pow 2 q hq0]
      ring
    rw [hq2, mul_assoc] at h'
    apply Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hq1) h'
  have hu_assoc : Associated u (π ^ (q + 1)) := by
    rw [← IsDiscreteValuationRing.addVal_eq_iff_associated, IsDiscreteValuationRing.addVal_pow, ← hb, ← ha, hba]
    norm_cast
  obtain ⟨w, hw⟩ := hu_assoc.symm
  obtain ⟨m, -, hζm⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  set G : A := ∑ i ∈ Finset.range m, ζ ^ i with hG
  have hσu : σ u = G * u := by
    rw [hu, map_sub, map_one, ← hζm, hG]
    apply (geom_sum_mul ζ m).symm
  have hσu' : σ u = α ^ (q + 1) * (σ (w : A) * (w⁻¹ : Units A)) * u := by
    have h1 : σ u = α ^ (q + 1) * π ^ (q + 1) * σ (w : A) := by
      rw [← hw, map_mul, map_pow, hσπ, mul_pow]
    rw [h1, ← hw]
    rw [show α ^ (q + 1) * (σ (w : A) * (w⁻¹ : Units A)) * (π ^ (q + 1) * (w : A)) =
        α ^ (q + 1) * π ^ (q + 1) * σ (w : A) * ((w⁻¹ : Units A) * (w : A)) by ring]
    rw [Units.inv_mul, mul_one]
  have hG_eq : G = α ^ (q + 1) * (σ (w : A) * (w⁻¹ : Units A)) :=
    mul_right_cancel₀ hu0 (hσu.symm.trans hσu')
  have hπ𝔪 : π ∈ maximalIdeal A := by
    apply (maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem (q ^ 2 - 1)
    rw [hπ]
    apply hAq
  have hu𝔪 : u ∈ maximalIdeal A := by
    rw [← hw]
    apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπ𝔪 _ (Nat.succ_le_succ (Nat.zero_le _)))
  have hζres : residue A ζ = 1 := by
    have : residue A u = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hu𝔪
    rw [hu, map_sub, map_one, sub_eq_zero] at this
    apply this
  have hGres : residue A G = (m : ResidueField A) := by
    rw [hG, map_sum]
    simp [map_pow, hζres]
  have hwres : residue A (σ (w : A) * (w⁻¹ : Units A)) = 1 := by
    have h1 : residue A (σ (w : A)) = residue A w := by
      rw [← sub_eq_zero, ← map_sub]
      apply (Ideal.Quotient.eq_zero_iff_mem).mpr (hσ w)
    rw [map_mul, h1, ← map_mul, Units.mul_inv, map_one]
  have hαres : residue A (α ^ (q + 1)) = (d : ResidueField A) := by
    rw [← sub_eq_zero, ← map_natCast (residue A), ← map_sub]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr hd
  have hmd : ((m : ℤ) - (d : ℤ) : A) ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residue A _ = 0
    have : residue A G = residue A (α ^ (q + 1)) := by rw [hG_eq, map_mul, hwres, mul_one]
    rw [hGres, hαres] at this
    push_cast
    rw [map_sub, map_natCast, map_natCast, this, sub_self]
  have hdvd : (q : ℤ) ∣ (m : ℤ) - (d : ℤ) := by
    let J : Ideal ℤ := (maximalIdeal A).comap (Int.castRingHom A)
    have hJq : Ideal.span {(q : ℤ)} ≤ J := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      show ((q : ℤ) : A) ∈ maximalIdeal A
      exact_mod_cast hAq
    have hJne : J ≠ ⊤ := by
      intro h
      have : (1 : ℤ) ∈ J := h ▸ Submodule.mem_top
      simp [J] at this
      apply (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hqp).irreducible
    have hJeq : Ideal.span {(q : ℤ)} = J := hmax.eq_of_le hJne hJq
    have hmem : ((m : ℤ) - (d : ℤ)) ∈ J := by
      show (((m : ℤ) - (d : ℤ) : ℤ) : A) ∈ maximalIdeal A
      exact_mod_cast hmd
    rw [← hJeq] at hmem
    apply Ideal.mem_span_singleton.mp hmem
  have hmod : m ≡ d [MOD q] := by
    rw [Nat.modEq_iff_dvd]
    have := hdvd
    rwa [← neg_sub, dvd_neg]
  have hpm : ∀ n : ℕ, ζ ^ n = ζ ^ (n % q) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n q]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [← hζm, hpm m, hpm d, (hmod : m % q = d % q)]


-- created on 2026-10-20
