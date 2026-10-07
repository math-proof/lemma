import Mathlib
import sympy.Basic


/--
[AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one.lean)
-/
@[main]
private lemma main
  {n : ℕ}
-- given
  (hn : n ≠ 0)
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
-- imply
  ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a := by
-- proof
  have : NeZero n := ⟨hn⟩
  refine ⟨(modularCyclotomicCharacter.toFun n
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).val, fun μ hμ => ?_⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hμ
    exact zero_ne_one hμ
  have hmem : Units.mk0 μ hμ0 ∈ rootsOfUnity n (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity']
    exact hμ
  have h := modularCyclotomicCharacter.toFun_spec'
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem
  simpa using h


-- created on 2026-10-05
