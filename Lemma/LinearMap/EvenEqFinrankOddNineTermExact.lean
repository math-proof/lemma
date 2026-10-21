import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {V₀ : Type u} [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
  {V₁ : Type u} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  {V₂ : Type u} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
  {V₃ : Type u} [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
  {V₄ : Type u} [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
  {V₅ : Type u} [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
  {V₆ : Type u} [AddCommGroup V₆] [Module k V₆] [FiniteDimensional k V₆]
  {V₇ : Type u} [AddCommGroup V₇] [Module k V₇] [FiniteDimensional k V₇]
  {V₈ : Type u} [AddCommGroup V₈] [Module k V₈]
  (d₀ : V₀ →ₗ[k] V₁)
  (d₁ : V₁ →ₗ[k] V₂)
  (d₂ : V₂ →ₗ[k] V₃)
  (d₃ : V₃ →ₗ[k] V₄)
  (d₄ : V₄ →ₗ[k] V₅)
  (d₅ : V₅ →ₗ[k] V₆)
  (d₆ : V₆ →ₗ[k] V₇)
  (d₇ : V₇ →ₗ[k] V₈)
  -- given
  (e₀ : LinearMap.ker d₀ = ⊥)
  (e₁ : LinearMap.range d₀ = LinearMap.ker d₁)
  (e₂ : LinearMap.range d₁ = LinearMap.ker d₂)
  (e₃ : LinearMap.range d₂ = LinearMap.ker d₃)
  (e₄ : LinearMap.range d₃ = LinearMap.ker d₄)
  (e₅ : LinearMap.range d₄ = LinearMap.ker d₅)
  (e₆ : LinearMap.range d₅ = LinearMap.ker d₆)
  (e₇ : LinearMap.range d₆ = LinearMap.ker d₇)
  (e₈ : LinearMap.range d₇ = ⊤) :
  -- imply
  Module.finrank k V₀ + Module.finrank k V₂ + Module.finrank k V₄ + Module.finrank k V₆ + Module.finrank k V₈ =
    Module.finrank k V₁ + Module.finrank k V₃ + Module.finrank k V₅ + Module.finrank k V₇ := by
  -- proof
  have h₀ : Module.finrank k (LinearMap.range d₀) + Module.finrank k (LinearMap.ker d₀) = Module.finrank k V₀ :=
    LinearMap.finrank_range_add_finrank_ker d₀
  rw [e₀, finrank_bot] at h₀
  have h₁ := LinearMap.finrank_range_add_finrank_ker d₁
  have h₂ := LinearMap.finrank_range_add_finrank_ker d₂
  have h₃ := LinearMap.finrank_range_add_finrank_ker d₃
  have h₄ := LinearMap.finrank_range_add_finrank_ker d₄
  have h₅ := LinearMap.finrank_range_add_finrank_ker d₅
  have h₆ := LinearMap.finrank_range_add_finrank_ker d₆
  have h₇ := LinearMap.finrank_range_add_finrank_ker d₇
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  rw [← e₃] at h₃
  rw [← e₄] at h₄
  rw [← e₅] at h₅
  rw [← e₆] at h₆
  rw [← e₇] at h₇
  have h₈ : Module.finrank k (LinearMap.range d₇) = Module.finrank k V₈ := by
    rw [e₈]
    simp only [finrank_top]
  omega


-- created on 2026-10-20
