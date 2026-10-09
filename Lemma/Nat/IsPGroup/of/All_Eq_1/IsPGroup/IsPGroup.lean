import Mathlib
import sympy.Basic


/--
[NumberField_isPGroup_algEquiv_compositum_of_isPGroup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_isPGroup_algEquiv_compositum_of_isPGroup.lean)
-/
@[path]
private lemma main
  {E F L N : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra E F] [Algebra E L] [Algebra E N] [Algebra F N] [Algebra L N] [IsScalarTower E F N] [IsScalarTower E L N] [IsGalois E F] [IsGalois E L] [IsGalois E N]
  {p : ℕ} [Fact p.Prime]
-- given
  (hF : IsPGroup p (F ≃ₐ[E] F))
  (hL : IsPGroup p (L ≃ₐ[E] L))
  (hgen : ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) → (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1) :
-- imply
  IsPGroup p (N ≃ₐ[E] N) := by
-- proof
  intro σ
  obtain ⟨i, hi⟩ := hF (AlgEquiv.restrictNormalHom F σ)
  obtain ⟨j, hj⟩ := hL (AlgEquiv.restrictNormalHom L σ)
  refine ⟨i + j, hgen _ (fun x => ?_) (fun y => ?_)⟩
  · have h1 : AlgEquiv.restrictNormalHom F (σ ^ p ^ (i + j)) = 1 := by
      rw [map_pow, pow_add, pow_mul, hi, one_pow]
    have h2 := AlgEquiv.restrictNormal_commutes (σ ^ p ^ (i + j)) F x
    rw [← h2]
    change algebraMap F N (AlgEquiv.restrictNormalHom F (σ ^ p ^ (i + j)) x) = _
    rw [h1, AlgEquiv.one_apply]
  · have h1 : AlgEquiv.restrictNormalHom L (σ ^ p ^ (i + j)) = 1 := by
      rw [map_pow, pow_add, mul_comm, pow_mul, hj, one_pow]
    have h2 := AlgEquiv.restrictNormal_commutes (σ ^ p ^ (i + j)) L y
    rw [← h2]
    change algebraMap L N (AlgEquiv.restrictNormalHom L (σ ^ p ^ (i + j)) y) = _
    rw [h1, AlgEquiv.one_apply]


-- created on 2026-10-05
