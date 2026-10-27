import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.FrobeniusEndo
open AlgebraicCurve


namespace Definitions
end Definitions

/--
[AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
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
  have pow_mem_iff' (A : ValuationSubring F) {n : ℕ} (hn : n ≠ 0) (z : F) :
    z ^ n ∈ A ↔ z ∈ A := by
    refine ⟨fun hzn => ?_, fun hz => pow_mem hz n⟩
    obtain hz | hzi := A.mem_or_inv_mem z
    ·
      exact hz
    ·
      obtain rfl | hz0 := eq_or_ne z 0
      ·
        exact zero_mem A
      ·
        have hkey : z = z ^ n * (z⁻¹) ^ (n - 1) := by
          rw [inv_pow, eq_comm, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hz0), ← pow_succ']
          congr 1; omega
        rw [hkey]; exact mul_mem hzn (pow_mem hzi _)
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
    exact (pow_mem_iff' w.toValuationSubring hℓ x).symm
  rw [key w₁, key w₂, hw]


-- created on 2026-10-24
