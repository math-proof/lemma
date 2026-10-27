import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsPrimitiveRoot_exists_tmul_sub_tmul_mem_of_aeval_cyclotomic_eq_zero.lean)
-/
@[path]
private lemma main
  (q : ℕ) [Fact q.Prime]
  (Z₀ : Type) [CommRing Z₀]
  (C : Type) [CommRing C] [Algebra Z₀ C] (w : C) (hw : Polynomial.aeval w (Polynomial.cyclotomic q Z₀) = 0)
  (A : Type) [CommRing A] [IsDomain A] [Algebra Z₀ A] (ζ : A) (hζ : IsPrimitiveRoot ζ q) :
  -- imply
  (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C) = 0) ∧
    (∀ 𝔭 : Ideal (TensorProduct Z₀ A C), 𝔭.IsPrime →
      ∃ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C) ∈ 𝔭) ∧
    (∀ (𝔭 : Ideal (TensorProduct Z₀ A C)) (μ μ' : A),
      ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C) ∈ 𝔭 →
      ((μ' ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C) ∈ 𝔭 →
        ((μ - μ') ⊗ₜ[Z₀] (1 : C) : TensorProduct Z₀ A C) ∈ 𝔭) ∧
    (∀ (𝔭 : Ideal (TensorProduct Z₀ A C)) (μ : A), 𝔭 ∈ minimalPrimes (TensorProduct Z₀ A C) →
      ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C) ∈ 𝔭 →
        𝔭.map (Ideal.Quotient.mk (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)})) ∈
          minimalPrimes ((TensorProduct Z₀ A C) ⧸ Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)}) ∧
        Nonempty (((TensorProduct Z₀ A C) ⧸ 𝔭) ≃+*
          (((TensorProduct Z₀ A C) ⧸ Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)}) ⧸
            𝔭.map (Ideal.Quotient.mk (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)}))))) := by
  -- proof
  classical
  set ψ : A →+* (TensorProduct Z₀ A C) := Algebra.TensorProduct.includeLeftRingHom with hψ
  set φ : C →+* (TensorProduct Z₀ A C) := (Algebra.TensorProduct.includeRight (R := Z₀) (A := A) (B := C)).toRingHom with hφ
  have hψμ : ∀ μ : A, ψ μ = μ ⊗ₜ[Z₀] (1 : C) := fun μ => rfl
  have hφw : φ w = (1 : A) ⊗ₜ[Z₀] w := rfl
  have hi : (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)) = 0 := by
    have h1 : Polynomial.cyclotomic q (TensorProduct Z₀ A C) = ∏ μ ∈ primitiveRoots q A, (Polynomial.X - Polynomial.C (ψ μ)) := by
      rw [← Polynomial.map_cyclotomic q ψ, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have h2 : Polynomial.eval (φ w) (Polynomial.cyclotomic q (TensorProduct Z₀ A C)) = 0 := by
      rw [← Polynomial.map_cyclotomic q φ, Polynomial.eval_map, ← Polynomial.map_cyclotomic q (algebraMap Z₀ C)]
      rw [Polynomial.eval₂_map]
      have : Polynomial.eval₂ (φ.comp (algebraMap Z₀ C)) (φ w) (Polynomial.cyclotomic q Z₀) = φ (Polynomial.eval₂ (algebraMap Z₀ C) w (Polynomial.cyclotomic q Z₀)) := by
        rw [Polynomial.hom_eval₂]
      rw [this]
      have hw' : Polynomial.eval₂ (algebraMap Z₀ C) w (Polynomial.cyclotomic q Z₀) = 0 := by
        rw [← Polynomial.aeval_def]
        apply hw
      rw [hw', map_zero]
    rw [h1, Polynomial.eval_prod] at h2
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
    have h3 : (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)) = ∏ μ ∈ primitiveRoots q A, (-(φ w - ψ μ)) := by
      apply Finset.prod_congr rfl
      intro μ _
      rw [hψμ, hφw, neg_sub]
    rw [h3, Finset.prod_neg, h2, mul_zero]
  refine ⟨hi, ?_, ?_, ?_⟩
  ·
    intro 𝔭 h𝔭
    let _ := h𝔭
    have : (∏ μ ∈ primitiveRoots q A, ((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)) ∈ 𝔭 := by
      rw [hi]
      apply zero_mem
    refine Ideal.IsPrime.prod_mem_iff.mp this
  ·
    intro 𝔭 μ μ' h h'
    have := 𝔭.sub_mem h h'
    rwa [sub_sub_sub_cancel_right, ← TensorProduct.sub_tmul] at this
  ·
    intro 𝔭 μ h𝔭 hj
    generalize hJ : (Ideal.span {((μ ⊗ₜ[Z₀] (1 : C)) - ((1 : A) ⊗ₜ[Z₀] w) : TensorProduct Z₀ A C)} : Ideal (TensorProduct Z₀ A C)) = J
    have hJle : J ≤ 𝔭 := by
      rw [← hJ, Ideal.span_le]
      rintro _ rfl
      apply hj
    have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
    let h𝔭p : 𝔭.IsPrime := h𝔭.1.1
    have hcomap : Ideal.comap (Ideal.Quotient.mk J) (𝔭.map (Ideal.Quotient.mk J)) = 𝔭 := by
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJle]
    have hP'prime : (𝔭.map (Ideal.Quotient.mk J)).IsPrime := by
      refine Ideal.map_isPrime_of_surjective hsurj ?_
      rw [Ideal.mk_ker]
      apply hJle
    refine ⟨⟨⟨hP'prime, bot_le⟩, ?_⟩, ⟨?_⟩⟩
    ·
      intro r hr hrle
      have h1 : Ideal.comap (Ideal.Quotient.mk J) r ≤ 𝔭 := by
        rw [← hcomap]
        apply Ideal.comap_mono hrle
      let _ : r.IsPrime := hr.1
      have h2 : 𝔭 ≤ Ideal.comap (Ideal.Quotient.mk J) r := h𝔭.2 ⟨Ideal.comap_isPrime _ r, bot_le⟩ h1
      calc
        _ ≤ (Ideal.comap (Ideal.Quotient.mk J) r).map (Ideal.Quotient.mk J) := Ideal.map_mono h2
        _ = r := Ideal.map_comap_of_surjective _ hsurj r
    ·
      apply (Ideal.quotEquivOfEq (sup_eq_right.mpr hJle).symm).trans (DoubleQuot.quotQuotEquivQuotSup J 𝔭).symm


-- created on 2026-10-20
