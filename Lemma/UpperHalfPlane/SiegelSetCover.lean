import Mathlib

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped Modular MatrixGroups Pointwise

namespace FLT.SiegelSetCover

theorem sqrt_three_div_two_le_im_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) :
    Real.sqrt 3 / 2 ≤ τ.im := by
  have h1 : 3 ≤ 4 * τ.im ^ 2 := three_le_four_mul_im_sq_of_mem_fd h
  have h2 : Real.sqrt 3 ≤ 2 * τ.im := by
    rw [Real.sqrt_le_left (by linarith [τ.im_pos])]
    nlinarith
  linarith

theorem exists_sqrt_three_div_two_le_im_smul (z : ℍ) :
    ∃ g : SL(2, ℤ), Real.sqrt 3 / 2 ≤ (g • z).im := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  exact ⟨g, sqrt_three_div_two_le_im_of_mem_fd hg⟩

theorem exists_out_smul_smul_mem_fd (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, ∃ q : SL(2, ℤ) ⧸ Γ, Quotient.out q • (γ • z) ∈ 𝒟 := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
  refine ⟨(h : SL(2, ℤ))⁻¹, Γ.inv_mem h.2, QuotientGroup.mk g, ?_⟩
  rw [hh, mul_smul, smul_inv_smul]
  exact hg

theorem exists_smul_mem_iUnion_smul_fd (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, γ • z ∈ ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟 := by
  obtain ⟨γ, hγ, q, hq⟩ := exists_out_smul_smul_mem_fd Γ z
  exact ⟨γ, hγ, Set.mem_iUnion.mpr ⟨q, Set.mem_inv_smul_set_iff.mpr hq⟩⟩

theorem exists_out_smul_smul_im_ge (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, ∃ q : SL(2, ℤ) ⧸ Γ,
      Real.sqrt 3 / 2 ≤ (Quotient.out q • (γ • z)).im := by
  obtain ⟨γ, hγ, q, hq⟩ := exists_out_smul_smul_mem_fd Γ z
  exact ⟨γ, hγ, q, sqrt_three_div_two_le_im_of_mem_fd hq⟩

theorem finite_quotient_gamma0 (N : ℕ) [NeZero N] : Finite (SL(2, ℤ) ⧸ Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

theorem exists_gamma0_smul_mem_iUnion_smul_fd (N : ℕ) (z : ℍ) :
    ∃ γ ∈ Gamma0 N, γ • z ∈ ⋃ q : SL(2, ℤ) ⧸ Gamma0 N, (Quotient.out q)⁻¹ • 𝒟 :=
  exists_smul_mem_iUnion_smul_fd (Gamma0 N) z

private theorem one_le_quadratic_form (c d : ℤ) (h : c ≠ 0 ∨ d ≠ 0) :
    1 ≤ c ^ 2 - c * d + d ^ 2 := by
  have key : 0 < c ^ 2 - c * d + d ^ 2 := by
    rcases h with hc | hd
    · rcases lt_or_gt_of_ne hc with h' | h' <;>
        nlinarith [sq_nonneg (c - 2 * d), Int.add_one_le_iff.mpr h']
    · rcases lt_or_gt_of_ne hd with h' | h' <;>
        nlinarith [sq_nonneg (2 * c - d), Int.add_one_le_iff.mpr h']
  linarith [Int.add_one_le_iff.mpr key]

theorem gate_im_rho : (UpperHalfPlane.ρ).im = Real.sqrt 3 / 2 := rfl

theorem gate_rho_mem_fd : UpperHalfPlane.ρ ∈ 𝒟 := by
  constructor
  · show (1 : ℝ) ≤ Complex.normSq (UpperHalfPlane.ρ : ℂ)
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    rw [Complex.normSq_apply,
      show ((UpperHalfPlane.ρ : ℂ)).re = -1 / 2 from rfl,
      show ((UpperHalfPlane.ρ : ℂ)).im = Real.sqrt 3 / 2 from rfl]
    nlinarith
  · show |(UpperHalfPlane.ρ).re| ≤ (1 : ℝ) / 2
    rw [show (UpperHalfPlane.ρ).re = -1 / 2 from rfl]
    rw [abs_le]
    norm_num

theorem gate_im_smul_rho_le (g : SL(2, ℤ)) :
    (g • UpperHalfPlane.ρ).im ≤ Real.sqrt 3 / 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hcd : (g 1 0 : ℤ) ≠ 0 ∨ (g 1 1 : ℤ) ≠ 0 :=
    (bottom_row_coprime g).ne_zero_or_ne_zero
  have hint : (1 : ℤ) ≤ g 1 0 ^ 2 - g 1 0 * g 1 1 + g 1 1 ^ 2 :=
    one_le_quadratic_form _ _ hcd
  have hden : (1 : ℝ) ≤ Complex.normSq (denom g UpperHalfPlane.ρ) := by
    have heq : Complex.normSq (denom g UpperHalfPlane.ρ) =
        ((g 1 0 ^ 2 - g 1 0 * g 1 1 + g 1 1 ^ 2 : ℤ) : ℝ) := by
      rw [ModularGroup.denom_apply]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      rw [show (UpperHalfPlane.ρ).re = -1 / 2 from rfl,
        show (UpperHalfPlane.ρ).im = Real.sqrt 3 / 2 from rfl]
      push_cast
      linear_combination ((g 1 0 : ℤ) : ℝ) ^ 2 / 4 * h3
    rw [heq]
    exact_mod_cast hint
  rw [ModularGroup.im_smul_eq_div_normSq]
  calc (UpperHalfPlane.ρ).im / Complex.normSq (denom g UpperHalfPlane.ρ)
      ≤ (UpperHalfPlane.ρ).im := by
        refine div_le_self ?_ hden
        rw [gate_im_rho]
        positivity
    _ = Real.sqrt 3 / 2 := gate_im_rho

theorem gate_one_half_lt_sqrt_three_div_two : (1 : ℝ) / 2 < Real.sqrt 3 / 2 := by
  have : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem gate_S_not_mem_gamma0_two : ModularGroup.S ∉ Gamma0 2 := by
  intro hmem
  rw [Gamma0_mem] at hmem
  exact absurd hmem (by decide)

end FLT.SiegelSetCover
