import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false


universe u

/--
[WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three.lean)
-/
@[path]
private lemma main
  {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
  {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
  (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀)) (W : WeierstrassCurve K) :
  -- imply
  ∃ (C : WeierstrassCurve.VariableChange K) (a b : R₀),
    C • W = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K) := by
  -- proof
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  have h2K : IsUnit (2 : K) := by
    have := h2.map (algebraMap R₀ K)
    rwa [map_natCast, Nat.cast_ofNat] at this
  have h3K : IsUnit (3 : K) := by
    have := h3.map (algebraMap R₀ K)
    rwa [map_natCast, Nat.cast_ofNat] at this
  let _ : Invertible (2 : K) := h2K.invertible
  let _ : Invertible (3 : K) := h3K.invertible
  obtain ⟨C₀, hC₀⟩ := W.exists_variableChange_isShortNF
  let _ := hC₀
  set W' := C₀ • W with hW'
  have ha₁ : W'.a₁ = 0 := W'.a₁_of_isShortNF
  have ha₂ : W'.a₂ = 0 := W'.a₂_of_isShortNF
  have ha₃ : W'.a₃ = 0 := W'.a₃_of_isShortNF
  obtain ⟨⟨d₁, hd₁⟩, p₁, hp₁⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R₀) W'.a₄
  obtain ⟨⟨d₂, hd₂⟩, p₂, hp₂⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R₀) W'.a₆
  simp only [Algebra.smul_def] at hp₁ hp₂
  have hd₁0 : d₁ ≠ 0 := nonZeroDivisors.ne_zero hd₁
  have hd₂0 : d₂ ≠ 0 := nonZeroDivisors.ne_zero hd₂
  set d : R₀ := d₁ * d₂ with hd
  have hdK : algebraMap R₀ K d ≠ 0 := (map_ne_zero_iff _ hinj).mpr (mul_ne_zero hd₁0 hd₂0)
  let u : Units K := (Units.mk0 (algebraMap R₀ K d) hdK)⁻¹
  refine ⟨⟨u, 0, 0, 0⟩ * C₀, d ^ 3 * d₂ * p₁, d ^ 5 * d₁ * p₂, ?_⟩
  rw [mul_smul, ← hW']
  have hu : ((u⁻¹ : Units K) : K) = algebraMap R₀ K d := by simp [u]
  ext
  · simp [WeierstrassCurve.variableChange_a₁, ha₁]
  · simp [WeierstrassCurve.variableChange_a₂, ha₁, ha₂]
  · simp [WeierstrassCurve.variableChange_a₃, ha₁, ha₃]
  ·
    rw [WeierstrassCurve.variableChange_a₄, WeierstrassCurve.map_a₄]
    simp only [ha₁, ha₂, ha₃, mul_zero, zero_mul, sub_zero, add_zero, hu, hd, map_mul, map_pow, hp₁]
    ring
  ·
    rw [WeierstrassCurve.variableChange_a₆, WeierstrassCurve.map_a₆]
    simp only [ha₁, ha₂, ha₃, mul_zero, zero_mul, sub_zero, add_zero, hu, hd, map_mul, map_pow, hp₂]
    ring


-- created on 2026-10-20
