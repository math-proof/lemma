import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Lemma.P2M.Util

open AlgebraicCurve

/--
[AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.lean)
-/

private theorem _root_.ValuationSubring.pow_mem_iff' {F : Type*} [Field F]
    (A : ValuationSubring F) {n : ℕ} (hn : n ≠ 0) (x : F) :
    x ^ n ∈ A ↔ x ∈ A := by
  refine ⟨fun hxn => ?_, fun hx => pow_mem hx n⟩
  rcases A.mem_or_inv_mem x with hx | hxi
  · exact hx
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem A
    · have hkey : x = x ^ n * (x⁻¹) ^ (n - 1) := by
        rw [inv_pow, eq_comm, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hx0), ← pow_succ']
        congr 1; omega
      rw [hkey]; exact mul_mem hxn (pow_mem hxi _)

p2m_alias "P2MW.S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.ValuationSubring.pow_mem_iff'" "ValuationSubring.pow_mem_iff'"
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {φ : F →ₐ[K] F}
  {ℓ : ℕ}
-- given
  (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ)
  (hℓ : ℓ ≠ 0)
  (hφ : φ.IsIntegral) :
-- imply
  Function.Injective (AlgebraicCurve.Place.restrictAlong φ hφ) := by
-- proof
  intro w₁ w₂ hw
  refine AlgebraicCurve.Place.ext (SetLike.ext fun x => ?_)
  obtain ⟨y, hy⟩ := h.pow_mem_range x
  have key : ∀ w : AlgebraicCurve.Place K F,
      x ∈ w.toValuationSubring ↔ y ∈ (w.restrictAlong φ hφ).toValuationSubring := by
    intro w
    let := AlgebraicCurve.algebraAlong φ
    have := AlgebraicCurve.isScalarTower_along φ
    have := AlgebraicCurve.isIntegral_along φ hφ
    rw [show AlgebraicCurve.Place.restrictAlong φ hφ w = w.restrict F from rfl,
      AlgebraicCurve.Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
    show x ∈ w.toValuationSubring ↔ φ y ∈ w.toValuationSubring
    rw [hy]
    exact (w.toValuationSubring.pow_mem_iff' hℓ x).symm
  rw [key w₁, key w₂, hw]


-- created on 2026-10-23
