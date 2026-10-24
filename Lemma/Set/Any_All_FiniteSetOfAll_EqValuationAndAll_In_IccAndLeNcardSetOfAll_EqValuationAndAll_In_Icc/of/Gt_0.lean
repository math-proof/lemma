import Mathlib
import sympy.Basic
open NumberField IsDedekindDomain


/--
[NumberField_exists_forall_finite_and_ncard_le_setOf_forall_valuation_eq_of_forall_apply_mem_Icc](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_exists_forall_finite_and_ncard_le_setOf_forall_valuation_eq_of_forall_apply_mem_Icc.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K]
  {c₁ c₂ : ℝ}
-- given
  (hc₁ : 0 < c₁) :
-- imply
  ∃ C : ℕ, ∀ e : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ),
      {x : K | (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x = e v) ∧
          ∀ w : InfinitePlace K, w x ∈ Set.Icc c₁ c₂}.Finite ∧
      {x : K | (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x = e v) ∧
          ∀ w : InfinitePlace K, w x ∈ Set.Icc c₁ c₂}.ncard ≤ C := by
-- proof
  classical
    set F : Set K := {y : K | IsIntegral ℤ y ∧ ∀ φ : K →+* ℂ, ‖φ y‖ ≤ c₂ / c₁} with hF
    have hFfin : F.Finite := NumberField.Embeddings.finite_of_norm_le K ℂ (c₂ / c₁)
    refine ⟨F.ncard, fun e => ?_⟩
    set A : Set K := {x : K | (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x = e v) ∧
        ∀ w : InfinitePlace K, w x ∈ Set.Icc c₁ c₂} with hA
    if hne : A = ∅ then
      rw [hne]; simp
    else
      obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have hx₀0 : x₀ ≠ 0 := by
        intro h
        obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
        have := (hx₀.2 w).1
        rw [h, map_zero] at this
        linarith
      have hmaps : ∀ x ∈ A, x / x₀ ∈ F := by
        intro x hx
        refine ⟨?_, fun φ => ?_⟩
        ·
          have hle : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x / x₀) ≤ 1 := by
            intro v
            have h0 : v.valuation K x₀ ≠ 0 := by
              rwa [Ne, Valuation.zero_iff]
            rw [map_div₀, hx.1 v, hx₀.1 v] at *
            rw [div_self h0]
          obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (x / x₀) hle
          rw [← hy]
          exact RingOfIntegers.isIntegral_coe y
        ·
          have h1 := hx.2 (InfinitePlace.mk φ)
          have h2 := hx₀.2 (InfinitePlace.mk φ)
          rw [InfinitePlace.apply] at h1 h2
          rw [map_div₀, norm_div]
          have hpos : 0 < ‖φ x₀‖ := lt_of_lt_of_le hc₁ h2.1
          rw [div_le_div_iff₀ hpos hc₁]
          calc
            _ ≤ c₂ * c₁ := mul_le_mul_of_nonneg_right h1.2 hc₁.le
            _ ≤ c₂ * ‖φ x₀‖ :=
                mul_le_mul_of_nonneg_left h2.1 (le_trans hc₁.le (le_trans h2.1 h2.2))
      have hinj : Set.InjOn (fun x : K => x / x₀) A := by
        intro x _ y _ hxy
        simpa [div_left_inj' hx₀0] using hxy
      refine ⟨?_, Set.ncard_le_ncard_of_injOn (fun x => x / x₀) hmaps hinj hFfin⟩
      exact Set.Finite.of_finite_image
        (hFfin.subset (by rintro _ ⟨x, hx, rfl⟩; exact hmaps x hx)) hinj


-- created on 2026-10-23
