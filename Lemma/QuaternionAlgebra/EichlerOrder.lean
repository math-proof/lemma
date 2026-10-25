import Mathlib
import Lemma.Submodule.LocalBox
import Def.QuaternionAlgebra_Order
import Def.QuaternionAlgebra_EichlerOrder

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace QuaternionAlgebra

variable {a b : ℚ}

theorem exists_natCast_smul_mem_of_mem_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {y : ℍ[ℚ, a, b]}
    (hy : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) :
    ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmu
    · rw [Nat.cast_mul, mul_smul]; exact Submodule.smul_mem _ _ hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have : (((c.den * n : ℕ) : ℤ)) • c • u = c.num • (((n : ℕ) : ℤ) • u) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ c.num,
        ← Int.cast_smul_eq_zsmul ℚ ((n : ℕ) : ℤ), smul_smul, smul_smul]
      congr 1
      push_cast
      rw [← Rat.mul_den_eq_num c]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ hnu

theorem IsOrder.inf {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : IsOrder Λ₁) (h₂ : IsOrder Λ₂) :
    IsOrder (Λ₁ ⊓ Λ₂) where
  one_mem := ⟨h₁.one_mem, h₂.one_mem⟩
  mul_mem := fun _ _ hx hy => ⟨h₁.mul_mem hx.1 hy.1, h₂.mul_mem hx.2 hy.2⟩
  spanTop := by
    refine top_unique ?_
    rw [← h₂.spanTop]
    refine Submodule.span_le.mpr fun y hy => ?_
    have hy' : y ∈ Submodule.span ℚ (Λ₁ : Set ℍ[ℚ, a, b]) := by rw [h₁.spanTop]; trivial
    obtain ⟨n, hn, hny⟩ := exists_natCast_smul_mem_of_mem_span hy'
    have hmem : ((n : ℕ) : ℤ) • y ∈ Λ₁ ⊓ Λ₂ := ⟨hny, Submodule.smul_mem _ _ hy⟩
    have : y = ((n : ℚ)⁻¹) • ((((n : ℕ) : ℤ) • y : ℍ[ℚ, a, b])) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  fg := by
    haveI : Module.Finite ℤ Λ₁ := Module.Finite.iff_fg.mpr h₁.fg
    haveI : Module.Finite ℤ ↥(Λ₁ ⊓ Λ₂) :=
      Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
    exact Module.Finite.iff_fg.mp inferInstance


theorem IsMaximalOrder.isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h : IsMaximalOrder Λ) : IsOrder Λ :=
  h.1


theorem IsEichlerOrder.isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (h : IsEichlerOrder Λ N) :
    IsOrder Λ := by
  obtain ⟨Λ₁, Λ₂, h₁, h₂, rfl, -⟩ := h
  exact h₁.isOrder.inf h₂.isOrder

theorem IsEichlerOrder.exists_le_isMaximalOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (h : IsEichlerOrder Λ N) :
    ∃ Λ₁ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₁ ∧ Λ ≤ Λ₁ ∧
      Λ.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N := by
  obtain ⟨Λ₁, Λ₂, h₁, -, rfl, hN⟩ := h
  exact ⟨Λ₁, h₁, inf_le_left, hN⟩


theorem IsDefiniteRamifiedExactlyAt.neg_left {q : ℕ} (h : IsDefiniteRamifiedExactlyAt a b q) : a < 0 :=
  h.1

theorem IsDefiniteRamifiedExactlyAt.neg_right {q : ℕ} (h : IsDefiniteRamifiedExactlyAt a b q) : b < 0 :=
  h.2.1

end QuaternionAlgebra
