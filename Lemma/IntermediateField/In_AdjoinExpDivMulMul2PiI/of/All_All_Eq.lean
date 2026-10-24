import Mathlib
import sympy.Basic
open IntermediateField


/--
[IntermediateField_coe_mem_adjoin_exp_of_forall_ringHom_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_coe_mem_adjoin_exp_of_forall_ringHom_apply_eq.lean)
-/
@[path]
private lemma main
  {N p : ℕ} [NeZero N]
  {z : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ))}
-- given
  (hp : p ∣ N)
  (hz : ∀ s : ℕ, s.Coprime N → s ≡ 1 [MOD p] → ∀ φ : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)) →+* ℂ, (∀ w : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)), (w : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) → φ w = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s) → φ z = z) :
-- imply
  (z : ℂ) ∈ IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
-- proof
  classical
    let ζN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))
    let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζN} : Set ℂ)
    change ((z : K) : ℂ) ∈ _
    have hN0 : N ≠ 0 := NeZero.ne N
    have hζ : IsPrimitiveRoot ζN N := Complex.isPrimitiveRoot_exp N hN0
    obtain ⟨M, hM⟩ := hp
    have hp0 : p ≠ 0 := by rintro rfl; simp at hM; exact hN0 hM
    have hM0 : M ≠ 0 := by rintro rfl; simp at hM; exact hN0 hM
    have hint : IsIntegral ℚ ζN := (hζ.isIntegral (Nat.pos_of_ne_zero hN0)).tower_top
    have : IsCyclotomicExtension {N} ℚ K := by
      have h1 : IsCyclotomicExtension {N} ℚ ↥(Algebra.adjoin ℚ ({ζN} : Set ℂ)) := IsPrimitiveRoot.adjoin_isCyclotomicExtension ℚ hζ
      have heq : Algebra.adjoin ℚ ({ζN} : Set ℂ) = K.toSubalgebra :=
        (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic).symm
      have := h1
      exact IsCyclotomicExtension.equiv {N} ℚ ↥(Algebra.adjoin ℚ ({ζN} : Set ℂ)) (Subalgebra.equivOfEq _ _ heq)
    have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hint
    have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
    let ζK : K := ⟨ζN, IntermediateField.mem_adjoin_simple_self ℚ ζN⟩
    have hζK : IsPrimitiveRoot ζK N := hζ.of_map_of_injective (f := (algebraMap K ℂ)) (algebraMap K ℂ).injective
    let ζpK : K := ζK ^ M
    have hζp : ((ζpK : K) : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) := by
      show Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ M = _
      rw [← Complex.exp_nat_mul, hM]
      congr 1
      have : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
      have : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM0
      push_cast
      field_simp
    let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ ({ζpK} : Set K)
    have hfix : z ∈ IntermediateField.fixedField E.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hσp : σ ζpK = ζpK := by
        have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
        exact this ζpK (IntermediateField.mem_adjoin_simple_self ℚ ζpK)
      have hσζ : IsPrimitiveRoot (σ ζK) N := hζK.map_of_injective σ.injective
      obtain ⟨s, hsN, hs⟩ := hζK.eq_pow_of_pow_eq_one hσζ.pow_eq_one
      have hscop : s.Coprime N := by
        have := hs ▸ hσζ
        exact (hζK.pow_iff_coprime (Nat.pos_of_ne_zero hN0) s).mp this
      have hs1 : s ≡ 1 [MOD p] := by
        have h1 : ζK ^ (M * s) = ζK ^ M := by
          rwa [pow_mul', hs, ← map_pow]
        obtain rfl | hspos := Nat.eq_zero_or_pos s
        ·
          have hN1 : N = 1 := by simpa using hscop
          have hp1 : p = 1 := Nat.eq_one_of_mul_eq_one_right (hM.symm.trans hN1)
          subst hp1
          exact Nat.modEq_one
        ·
          have h2 : ζK ^ (M * (s - 1)) = 1 := by
          have hsplit : M * s = M * (s - 1) + M := by
            rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right M hspos)]
          rw [hsplit, pow_add] at h1
          exact (mul_eq_right₀ (pow_ne_zero _ (hζK.ne_zero hN0))).mp h1
          have h3 : N ∣ M * (s - 1) := (hζK.pow_eq_one_iff_dvd _).mp h2
          rw [hM] at h3
          have h4 : p ∣ s - 1 := by
            obtain ⟨t, ht⟩ := h3
            refine ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hM0) ?_⟩
            rw [ht]; ring
          refine ((Nat.modEq_iff_dvd' hspos).mpr h4).symm
      have := hz s hscop hs1 ((algebraMap K ℂ).comp σ.toAlgHom.toRingHom) (by
        intro w hw
        have : w = ζK := Subtype.ext hw
        subst this
        show ((σ ζK : K) : ℂ) = ζN ^ s
        rw [← hs]; rfl)
      exact Subtype.ext this
    rw [IsGalois.fixedField_fixingSubgroup] at hfix
    have hmap : ((z : K) : ℂ) ∈ (ℚ⟮ζpK⟯).map (IntermediateField.val K) := ⟨z, hfix, rfl⟩
    erw [IntermediateField.adjoin_map] at hmap
    have hmem : ((z : K) : ℂ) ∈ ℚ⟮((ζpK : K) : ℂ)⟯ := by simpa using hmap
    rwa [hζp] at hmem


-- created on 2026-10-23
